# Making `restore_invariant` an invariant

*Change note, September 2026. Files: `theories/models.v`, `theories/noninterference.v`.*

## The problem

`model_sliced` hands `initiate_next` a function `restore_invariant`, applied just
before the next process is chosen. It was meant as a device for the proof. Proving
`fv_NI` one stage of the transition at a time forgets what earlier stages
established, so `restore_invariant` writes the time-slice invariant back. The
documentation said it was the identity on every state the model can reach.

That was not true. Besides re-imposing mask bits, `restore_invariant` ORed two
things into the state that nothing else in `model_sliced` set:

| effect | consequence |
|---|---|
| `re_sched := true` | `sliced_preroutine` never set `re_sched`, and `initiate_scheduler` resets it to `false`. So `restore_invariant` was the only reason control ever returned to the scheduler after a slice. |
| slice live ⇒ NOP pending | `initiate_handler` clears a handler's pending bit when it starts it, and only an input event (`set_pending`) sets one. So `restore_invariant` was the only reason the NOP filler ever ran. |

The mechanised trace `sliced_no_dI'` shows both. It contains four NOP runs and no
`DefaultInterrupt` input, and it reaches the scheduler after each slice. The filler,
which is the heart of the security story, was being produced by the component
described as harmless bookkeeping.

## The change

The two behaviours move into the design. The two writes in `restore_invariant`
are then treated differently, because they play different roles in the proof (see
the next section): the `re_sched` write is removed, and the NOP-pending write stays,
now only re-imposing what the design has already done. All three edits are in code
that only `model_sliced` uses.

1. **`check_handler_completed`** now also makes the NOP handler pending at each
   handler boundary inside a slice:

   ```coq
   check_handler_completed runtime v =
     if handler_completed runtime (ir_count v)
     then update_ir_pending (set_tI (unset_masks v)) DefaultInterrupt true
     else v
   ```

2. **`initiate_ir`** now requests a reschedule when the timer's `Notify` opens a
   slice, as `immediate_preroutine` does in `model_immediate`:

   ```coq
   initiate_ir runtime runs o v =
     if tI_out o is Some Notify
     then update_re_sched (update_ir_count v (Some (time_slice runtime runs))) true
     else v
   ```

3. **`restore_invariant`** no longer writes `re_sched`: the first component of the
   tuple it ORs in is now `false`, which leaves `re_sched` alone.

### Why the reschedule is requested when the slice opens

The first version set `re_sched` when the slice *closed*, in `check_ir_count`.
That changes behaviour when `runtime = 1` (see below). There the slice ends one
boundary early, before the close has run, so control went back to the interrupted
process instead of the scheduler. Requested when the slice opens, `re_sched` stays
`true` until `initiate_scheduler` consumes it, whenever the slice ends. In
`model_sliced` that is the only point where `re_sched` is read.

### Behaviour is unchanged

`re_sched` is read only when a handler slot is live and nothing is ready. In
`model_sliced` that happens only at the end of a slice. Before the change it was
always `true` there; now it is `true` from the timer's `Notify` until the
scheduler starts. The NOP handler becomes pending at exactly the boundaries where
`restore_invariant` used to make it pending. The two mechanised `model_sliced`
traces replay unchanged.

### Why the NOP-pending write stays and the `re_sched` write goes

The NOP-pending write is the part of the invariant the proof needs. `fv_NI` must
hold for every pair of related states, and pending bits are private, so two related
states may differ on them. Take two states inside a live slice with the masks open,
the disk handler pending in `v` and nothing pending in `v'`. They are related at
`⊥`. Without the write, `initiate_next` starts the disk handler in `v` (pid
`inl true`) and nothing in `v'` (pid `inr _`); the pid's tag is public, so the
results are unrelated and `fv_NI` fails. Forcing NOP pending in both states ensures
a secret handler is ready in each. Removing the write was tried: the `initiate_next`
stage of `model_sliced_NI` no longer goes through. Such states are unreachable,
since the design makes NOP pending at every boundary, which is exactly the
"forgotten invariant" `restore_invariant` exists to restore. With the design now
doing so, the write is provably a no-op.

The `re_sched` write was the opposite case. The proof never needed it: `re_sched`
is public, so related states already agree on it. And it is not true on reachable
states: `re_sched` is `false` from the moment the scheduler starts until the next
slice opens, so the write changed the state at every choice in user space. It
could not be a no-op, so it had to go.

## The proof repairs

Only `model_sliced_NI` needed repair, at the two stages that now write extra fields.
Two small lemmas were added to `noninterference.v`, each applied once:

- `update_pending_rel`: writing the same pending bit into two related states keeps
  them related (the bit is private, the masks are untouched);
- `update_re_sched_rel`: likewise for `re_sched`, which is public.

The hard `initiate_next` stage needed no change. It never relied on
`restore_invariant` writing `re_sched`, because `re_sched` is public and two related
states already agree on it.

## The new theorem

`Section SlicedInvariant` in `models.v` proves

```coq
restore_invariant_noop :
  forall runtime runs Opub Opriv, runtime != 1 ->
  forall es o,
    ~~ masks_set (choice_state o (sliced_run es)) ->
    restore_invariant (choice_state o (sliced_run es)) = choice_state o (sliced_run es)
```

Here `sliced_run es` is the state after the events `es`, starting from
`initial_state_sliced`. `choice_state o v` is the state `initiate_next` receives on
output `o`, and the `~~ masks_set` premise is exactly the condition under which
`initiate_next` applies `restore_invariant`. The proof uses no axioms.

The event sequence `es` is arbitrary, not restricted to what a process pool can
emit. So the theorem is about the state machine alone and never reasons about
processes. That makes it stronger than a statement about reachable states, and
much easier to prove.

The proof has three parts:

- **`sliced_inv`**, the invariant between steps. The NOP and disk masks agree;
  outside a slice they are set; inside a slice a handler is running.
- **`choice_inv_step`**: from `sliced_inv`, the choice state satisfies
  `choice_inv`. That is `sliced_inv` relaxed at a boundary, where the masks are
  open and the NOP handler is pending. It is proved through one small lemma per
  stage (`check_scheduler`, `initiate_ir`, `check_handler_completed`,
  `check_ir_count`), each about the fields the invariant reads.
- **`restore_invariant_id`**: on a state satisfying `choice_inv` with masks not all
  set, `restore_invariant` is the identity. **`sliced_inv_step`**: every event
  preserves `sliced_inv`. Induction over `es` finishes the proof.

## A finding: one-step handlers

The theorem needs `runtime ≠ 1`, and the reason is a quirk of the model that
predates this change. The boundary test `handler_completed` reads the slice counter
before the stage that ticks it, while `timeslice_live` reads it after. For
`runtime ≥ 2` the counter after the tick at every boundary inside a slice is at
least `runtime - 1 ≥ 1`, so the slice still counts as live. For `runtime = 1` the
last boundary ticks it to `Some 0`. The slice already reads as over,
`restore_invariant` masks the handler that boundary just enabled, and every slice
loses its last handler run.

This does not affect non-interference: `model_sliced_NI` has no side condition and
covers `runtime = 1`. It does mean `restore_invariant` acts at `runtime = 1`, so the
no-op theorem has to exclude it. Fixing the off-by-one would let the hypothesis go;
it is recorded as a limitation in `docs/noninterference.md` §6.

## Verification

- A full clean build of all five files succeeds.
- `Print Assumptions` is unchanged for `model_sliced_NI`, `model_sliced_userview_NI`
  and `model_immediate_not_NI`. That is `eq_rect_eq` and the two lattice
  parameters, plus `classic` for the two positive results.
- `restore_invariant_noop` is closed under the global context.
