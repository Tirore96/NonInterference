# Section V: the state update, restore_invariant, and the plan

Working notes from the review of Section V (2026-11-03). They record what the
Rocq proof actually does with `restore_invariant`, the insights from the
discussion, and the plan for restructuring Section V. The red `\todo` comments in
`tex/sections/proof.tex` are still in place; this file is the longer record.

## 1. Where the state update sits in the proof

`model_sliced` is `reactive_system` (Section III-E): an outer `map`, a `loop`, an
inner `map id snd`, then `sta f g v (map pool_input inr (maybe pool))`. Once the
outer map and the loop are peeled off, the goal is `sta_NI` (Theorem 1(3)), with two
obligations on the state update `f = state_step`:

- `f_EP` (PE in the paper): an unobservable event leaves the state related to
  itself. Only a disk interrupt is unobservable, and `set_pending` only sets a
  private bit, so this is trivial, but illustrative: it is why an interrupt may
  only record that it is pending.
- `fv_NI` (NI(≐E, ≐V, ≐V)): related events take related states to related states.
  `state_step = step_sum set_pending (output lane)`, and ≐E never relates an input
  to an output, so `fv_NI_step_sum` splits it by cases on the event:
  - input: `set_pending` writes one private bit; trivial;
  - output: the output lane, a composite of six stages. This is where all the
    work is.

## 2. The output lane: six stages and their obligations

Order of application (`state_step`'s output summand is
`initiate_next restore_invariant ∘ sliced_service ∘ check_scheduler`, and
`sliced_service = tick_slice ∘ check_handler_completed ∘ open_slice_on_timer`):

| # | stage | reads | writes |
|---|---|---|---|
| 1 | `check_scheduler` | scheduler's output (public) | current pid |
| 2 | `open_slice_on_timer` | timer handler's output (public) | counter, reschedule flag |
| 3 | `check_handler_completed` | counter | at a boundary: unmask disk/NOP, mask timer, NOP pending := true |
| 4 | `tick_slice` | counter | tick; at `Some 0`: mask disk/NOP, unmask timer, counter := None |
| 5 | `restore_invariant` | counter, disk mask | NOP pending, masks (see §4) |
| 6 | `initiate_next` (the choice) | masks, pending bits, pid, prev pid, reschedule flag | pid, prev pid, masks, one pending bit |

Stages 1–5 read only public fields and public output slots, so on related
arguments they write the same values (private bits included): routine.
Stage 6 reads the private pending bits: the only non-trivial one.

`fv_NI_comp` proves the composite stage by stage. Each stage's obligation
quantifies over *all* pairs of related states, so the only thing that passes from
one stage to the next is relatedness. What an earlier stage establishes about its
result (e.g. stage 3 just made NOP pending; stage 4 just masked disk/NOP) is
forgotten. This is the "forgetting" that `restore_invariant` repairs.

Note: `restore_invariant` is applied once, inside `initiate_next`, after rule 1
(all masks set) and before rules 2–4. It is stage 5 above and appears nowhere else.
`model_immediate` instantiates it with `id`.

## 3. How the proof of `initiate_next` uses restore_invariant: case by case

Not as a chain: the proof of stage 6 (noninterference.v, from "initiate_next: the
outermost stage") splits into cases, and each case uses a different fact.
Throughout, `v ≐V v'` at ⊥, and `w = restore_invariant v`, `w' = restore_invariant v'`.

- **A. Rule 1 (all masks set).** Masks are public, so `masks_set v = masks_set v'`:
  both states continue, or neither. No use of restore_invariant.
- **B. Timer ready.** `ready_cases2P` first needs `ir_ready w timer = ir_ready w'
  timer`. Timer pending and timer mask are public, and restore_invariant writes the
  timer mask from the (public) counter, so they agree. Both start the timer handler.
  Use of restore_invariant: trivial (only because the goal is about w, w').
- **C. Timer not ready.** `ready_aux2`: each of w, w' has the disk handler first,
  the NOP handler first, or no secret handler ready. Nine combinations:
  - **C1. Secret in both (disk/disk, disk/NOP, NOP/disk, NOP/NOP).** Both start a
    handler: the pid becomes `inl b` with `b` private, all masks are set (public,
    equal), one pending bit is cleared (private). Related. **No use of
    restore_invariant.** Different secret handlers in the two states are
    explicitly allowed: which one runs is private.
  - **C2. Secret in one, none in the other (4 combinations).** Closed by
    `exfalso`, the only essential use of restore_invariant. Why this case must be
    impossible: the state with a ready secret handler starts it and enters S (pid
    `inl _`), while the other falls through to rule 3 or 4 and returns to, or
    continues, a user process or the scheduler (pid `inr _`), i.e. stays in U.
    The current pid's tag is public (≐^{H∘} + ≐^L), so the two states would be
    unrelated, and the attacker would see S in one run and U in the other. Why it
    is impossible after restore_invariant: if a secret handler is ready in w, the
    disk or NOP handler is unmasked, so (by §4) a slice is open; then the NOP handler
    is pending in both w and w' and the NOP mask equals the disk mask, which is
    public; so the NOP handler is ready in w' too. Contradiction.
  - **C3. None in both.** Rules 3/4: `is_handler_pid` (pid tag, public) and
    `get_re_sched` (public) agree; restore_invariant does not touch them. Use:
    trivial.

**Key insight for the paper:** restore_invariant does not make the same secret
handler run in both states (C1 explicitly allows disk in one and NOP in the
other). It makes *both run a secret handler, or neither*: otherwise one state
enters S while the other returns to U, and the pid's public tag exposes it.

## 4. The invariants: `sliced_inv`, `choice_inv`, and restore_invariant

"Open slice" = `timeslice_live`: the counter is `Some n` with `n > 0`.
(`Some 0` means the slice is closing; `None` means no slice.)

- **`sliced_inv v`** (models.v): the invariant **between steps**, true of every
  state the sliced policy reaches (`sliced_run_inv`, proved by `sliced_inv_step`:
  every event preserves it).
  1. NOP mask = disk mask;
  2. in an open slice, all masks are set (a handler is running);
  3. outside a slice, the disk mask is set (hence, by 1, the NOP mask too).
- **`choice_inv w`**: the invariant **at the choice point**, i.e. on the state
  `initiate_next` receives, after `check_scheduler` and the service policy
  (`choice_state o v`). Same as `sliced_inv`, except that inside an open slice it
  also allows a **handler boundary**: the masks of disk and NOP are open, the
  timer is masked and the NOP handler is pending (stage 3 has just queued the
  filler).
  1. NOP mask = disk mask;
  2. in an open slice: all masks set, **or** (NOP pending ∧ timer masked ∧ disk
     and NOP unmasked);
  3. outside a slice: disk masked.
  `choice_inv_step`: `sliced_inv v → choice_inv (choice_state o v)`.
- Why two: between steps, a handler is always running inside a slice; the service
  policy then runs before the choice and, at a boundary, opens the masks and queues
  the NOP handler. So the state the choice sees has one more shape than the states
  between steps.
- **`restore_invariant w`** writes into `w`: in an open slice, NOP pending := true
  and timer mask := true; outside, disk mask := true and NOP mask := true; in both,
  NOP mask := disk mask. Every state it returns satisfies the shape `initiate_next`
  needs whenever not all masks are set.
- `restore_invariant_id`: `choice_inv w ∧ ¬masks_set w → restore_invariant w = w`.
  With `choice_inv_step` and `sliced_run_inv` this gives Theorem 5
  (`restore_invariant_noop`): on every reachable state where it is applied, it is
  the identity.

## 5. Insights recorded

- **Theorem 5 is not used by the non-interference proof.** `restore_invariant_noop`
  appears in noninterference.v only in a comment; no lemma depends on it. It shows
  that the hook does not change the model's behaviour (so Theorem 4 is about the
  sliced policy as intended), which is more than naming, but secondary.
- **What is forgotten** is the link between the counter and the secret handlers'
  bits (§4); stage-by-stage composition passes only relatedness.
- **Restricting ≐V is impossible** (a characterised equivalence is reflexive on
  every value); **arguing over reachable states only** would lose the
  per-constructor structure.
- **Simplification idea: NOP pending := true unconditionally** in restore_invariant.
  - For non-interference it works and likely simplifies C2: after it, the NOP
    handler is always pending and its mask equals the disk mask, so a secret
    handler is ready exactly when the NOP mask is clear, which is public. The
    counter no longer matters for this argument.
  - **It breaks Theorem 5 as stated**: outside a slice a reachable state can have
    the NOP pending bit clear (the NOP handler cleared it when it ran the last
    filler), and restore_invariant would set it, so it is no longer the identity.
    Observable behaviour is unchanged (NOP is masked outside a slice, and the next
    slice sets the bit anyway), so Theorem 5 would have to become a statement about
    behaviour, not an identity.
- **Predicate instead of function (to explore).** Remove restore_invariant from
  the model; make the invariant an assumption of the proof and a theorem that every
  stage preserves it.
  - Gains: no proof-only hook in the model; `model` loses a parameter; Sections
    III-D/E and IV get simpler; Theorem 5 becomes "the invariant is an invariant"
    (pieces exist: `sliced_inv_step`, `choice_inv_step`, `sliced_run_inv`).
  - Costs: `sta_NI` quantifies over all related states, so a new composition
    theorem is needed: if the initial state satisfies P and the state updates
    preserve P, it suffices to prove `fv_NI` (and `f_EP`) for related states that
    both satisfy P. Inside the lane, `fv_NI_comp` needs a pre/postcondition
    version, since the condition at the choice (`choice_inv`) differs from the one
    between steps (`sliced_inv`). The forgetting moves into those conditions, so it
    removes less than it first seems, but it pushes an essential part of the proof
    into the metatheory, which is interesting in itself.
  - New theorems go at the bottom of theorems.v (prior work above stays untouched).
  - **Done (2026-11-03): `sta_NI_inv`** at the bottom of theorems.v, section
    `StaInvariant`, axiom-free (only `d`, `L`). Statement: if `P` is preserved by
    `f` and `g` (`pres_on`), the initial state satisfies `P`, `g` and `f` satisfy
    `fv_NI_on P` (fv_NI for related states that both satisfy `P`), `f` satisfies
    `f_EP_on P`, and `p ∈ NI(≐V ×_R ≐I, ≐O)`, then
    `sta f g v p ∈ NI(≐I, ≐V × ≐O)`. The proof is sta_NI's with `P` threaded
    through the `lthread` lemmas (`*_on` copies): every state the proof hands to
    `f` or `g` is an iterate of `f`/`g` from the initial state.
  - Not yet done: using it for `model_sliced`. That needs (a) `P := sliced_inv`
    with preservation by `state_step` minus restore_invariant, (b) a version of
    the output-lane proof where `initiate_next` gets `choice_inv` from
    `sliced_inv` via the earlier stages (a pre/postcondition chaining, since
    `fv_NI_comp` alone forgets it), and (c) removing restore_invariant from
    `model` and its instances.

## 6a. Plan: replace restore_invariant by the invariant (Rocq only; paper deferred)

**Not pursued (2026-11-03).** The invariants `sliced_inv`/`choice_inv` differ too
much from `restore_invariant`; an invariant used this way should correspond to
"the state is in the image of restore_invariant". Kept for reference.

### Notation

- `choose w`: rules 2–4 of `initiate_next` (start the first ready handler; else
  return from a finished handler; else continue).
- `next_R w := if masks_set w then w else choose (restore_invariant w)`: today's
  `initiate_next restore_invariant`.
- `next w := if masks_set w then w else choose w`: the target, no hook.
- `pre o v := sliced_service o (check_scheduler o v)`: stages 1–4
  (`choice_state o v` in models.v).
- `step_R` / `step`: `step_sum set_pending (fun o v => next_R (pre o v))` /
  the same with `next`. `step_R` is today's `state_step _ restore_invariant`.

### The observation behind Phase 1, precisely

1. `restore_invariant_id` (exists): if `choice_inv w` and not `masks_set w`, then
   `restore_invariant w = w`.
2. Hence, for every `w` with `choice_inv w`: `next_R w = next w`. If all masks are
   set, both return `w` without calling `restore_invariant`; otherwise
   `restore_invariant w = w` by 1, so both compute `choose w`.
3. `choice_inv_step` (exists): `sliced_inv v → choice_inv (pre o v)`.
4. Hence, for every `v` with `sliced_inv v` and every event `e`:
   `step_R e v = step e v`. On an input both are `set_pending`; on an output
   `step_R (inr o) v = next_R (pre o v) = next (pre o v) = step (inr o) v` by 3
   and 2.

So `step` and `step_R` agree on the set `sliced_inv`. `sta_NI_inv` with
`P := sliced_inv` asks for `fv_NI` only between related states that both satisfy
`sliced_inv`, and on those states `step` can be rewritten to `step_R`, whose
`fv_NI` over *all* related states is already proved. No new relational reasoning
is needed: the existing proof is reused verbatim.

That is a checkpoint, not the goal: Phase 1 still uses `restore_invariant` inside
the proof. Phase 2 removes it.

### Decision to make first: runtime = 1

`choice_inv_step` (hence `sliced_inv_step`) holds only under the section hypothesis
`runtime_ne1 : runtime != 1` (used in `hc_ge2` and in one case of
`choice_inv_step`). Today Theorem 4 needs no such hypothesis, because
`restore_invariant` repairs the state unconditionally. With the invariant as a
proof assumption, runtime = 1 must be handled. What happens there: at counter
`Some 1` the last boundary fires (`check_handler_completed` opens the disk and NOP
masks and sets the NOP pending bit), then `tick_slice` ticks the counter to
`Some 0`, which is not an open slice, so `choice_inv` (disk masked outside a
slice) fails. Without the hook, `next` starts a secret handler there (NOP pending
and unmasked in both related states), and the next step closes the slice under it.
Options:
- (a) Extend the invariant to allow this "closing boundary": outside an open slice,
  `choice_inv` also accepts counter `Some 0` with the boundary shape (NOP pending,
  timer masked, disk and NOP unmasked); `sliced_inv` likewise accepts a running
  handler at `Some 0` (all masks set, which it already does). Secret readiness then
  depends only on the counter and the masks, both public, so the C2 argument still
  goes through, and Theorem 4 keeps holding for every runtime. Cost: re-prove
  `choice_inv_step`/`sliced_inv_step` for the wider invariant.
- (b) Add `runtime != 1` as a hypothesis of Theorem 4 and Corollary 1. Cheap, but
  the theorem gets weaker than today's.
Recommendation: try (a); fall back to (b) only if (a) gets out of hand. Note that
(a) also changes the model's behaviour at runtime = 1 compared with today (the last
run is no longer lost, but overlaps the slice's closing step), which the paper's
runtime = 1 remark must then describe.

### Phase 1: take restore_invariant out of the model (checkpoint)

1. **models.v, definitions.** `initiate_next` loses its parameter (`next` above);
   `state_step` loses `restore_invariant`; `model` loses the `restore_invariant`
   argument; `model_immediate` drops `id`; `model_sliced` drops
   `restore_invariant`. Keep `restore_invariant` and `restore_invariant_id` (moved
   next to the invariants) as proof devices.
2. **models.v, invariant lemmas for the new step.** Define `step_R` locally (the old
   step) and prove `step_agree : sliced_inv v → step_R e v = step e v`
   (observation 4). Re-prove `sliced_inv_step`, `sliced_run_inv` for `step` (from
   the old proofs: the only change is that the `restore_invariant_id` rewrite is no
   longer needed). Add `sliced_init_inv : sliced_inv sliced_init`.
3. **models.v §10–11 fallout.** The `rewr` Ltac, the `sta (state_step _ _)` match
   pattern, `scanl (state_step service restore …)` and the state-row lemmas
   (`immediate_states_*`, `sliced_states_*`) lose an argument. The computed traces
   and states do not change (the hook was the identity on reachable states); the
   `vm_compute` proofs should go through unchanged.
4. **noninterference.v, a step-level lemma.** Factor today's proof of
   `fv_NI (eqsum_L in_equiv out_equiv) state_type_equiv state_type_equiv step_R`
   (the long script inside `model_sliced_NI`) into a standalone lemma
   `step_R_fv_NI`, and likewise `step_R_f_EP`.
5. **noninterference.v, `model_sliced_NI` via `sta_NI_inv`** with
   `P := sliced_inv`, `f := step`, `g := (fun _ v => v)`:
   - `pres_on P f`: `sliced_inv_step` (step 2);
   - `pres_on P g`: trivial;
   - `fv_NI_on P f`: given `e ≐ e'`, `v ≐ v'`, `sliced_inv v`, `sliced_inv v'`,
     rewrite `step e v` and `step e' v'` with `step_agree`, then `step_R_fv_NI`;
   - `fv_NI_on P g`: trivial;
   - `f_EP_on P f`: from `step_R_f_EP` via `step_agree` (inputs only);
   - `P v0`: `sliced_init_inv`.
6. **Remove Theorem 5 from the model's story.** `restore_invariant_noop` is no
   longer a statement about the model; delete it (or keep it as a lemma about
   `step_R`). Its role is taken by `sliced_run_inv`.
7. **Build** off OneDrive, `Print Assumptions` for `model_sliced_NI` and
   `model_sliced_userview_NI` (still only `d`, `L`), regenerate mechlinks.

### Phase 2: no restore_invariant in the proof either

The goal is to prove `fv_NI_on sliced_inv` of the output lane of `step` directly,
with the invariant passed from stage to stage as pre/postconditions, so that
`restore_invariant`, `restore_invariant_id`, `step_R` and `step_agree` can be
deleted.

8. **A composition lemma with conditions** (noninterference.v, next to
   `fv_NI_comp`):
   `fv_NI_comp_on : (forall i v, P v -> Q (s1 i v)) -> fv_NI IRel VRel VRel s1 ->
    fv_NI_on Q IRel VRel s2 -> fv_NI_on P IRel VRel (fun i => s2 i \o s1 i)`.
   Stage 1 is proved over all related states (as today) and maps `P` into `Q`;
   stage 2 needs only states in `Q`. Proof: a few lines. This is the precise form
   of "the composite forgets": `fv_NI_comp` passes only relatedness; the new lemma
   also passes a single-state fact (`Q`) that each side satisfies.
9. **A step_sum lemma with conditions:** `fv_NI_step_sum_on`, as
   `fv_NI_step_sum` but concluding `fv_NI_on P` from `fv_NI_on P` (or `fv_NI`) of
   each lane.
10. **The key new lemma: secret readiness is public under `choice_inv`.**
    `secret_ready_public : choice_inv w -> ~~ masks_set w ->
     (ir_ready w disk_irq || ir_ready w nop_irq) = timeslice_live (get_slice_count w)`
    (with option (a) of the runtime decision, extended by the closing-boundary
    case). Reason: outside an open slice the disk mask is set and the NOP mask equals
    it, so neither is ready; inside, not all masks are set, so `choice_inv` gives the
    boundary shape: the NOP handler is pending and unmasked, so it is ready. Proof:
    a case split on the bits, like `restore_invariant_id` (vm_compute).
11. **`initiate_next` on `choice_inv` states:** `next_fv_NI_on :
    fv_NI_on choice_inv out_equiv state_type_equiv (fun _ => next)`. Proof: today's
    `initiate_next` script with `restore_invariant v` replaced by `v`:
    - A (rule 1), B (timer), C1 (secret in both) and C3 (none in both) are
      unchanged except that the trivial `restore_invariant` rewrites disappear;
    - C2 (secret in one, none in the other): instead of unfolding
      `restore_invariant`, apply `secret_ready_public` to both states; their
      counters are public, hence equal, so secret readiness is equal: contradiction.
      This replaces the four long `exfalso` scripts by one argument.
12. **Chain the output lane:** `pre` is `fv_NI` over all related states (the
    existing stage proofs for `check_scheduler` and the three service stages,
    composed with `fv_NI_comp`), and `choice_inv_step` gives
    `sliced_inv v -> choice_inv (pre o v)`. Then `fv_NI_comp_on` with
    `P := sliced_inv`, `Q := choice_inv` and step 11 gives `fv_NI_on sliced_inv` of
    the output lane; `fv_NI_step_sum_on` adds the input lane (`set_pending`, `fv_NI`
    as today).
13. **`model_sliced_NI`:** the `fv_NI_on P f` obligation of step 5 now comes from
    step 12 instead of `step_agree`.
14. **Delete** `restore_invariant`, `restore_invariant_id`, `restore_invariant_noop`,
    `step_R`, `step_agree`, `step_R_fv_NI`, `step_R_f_EP` and the comments that
    describe the hook (models.v header, §7 comment, §8 table, noninterference.v
    "composition-breakdown technique" comment, `ready_cases2` uses on restored
    states). Rebuild, check axioms, regenerate mechlinks.

### What the result says, for the paper later

- Theorem 4 is proved with `sta_NI_inv` and `P := sliced_inv`; the model has no
  proof hook.
- The invariant theorem (`sliced_run_inv`, from `sliced_inv_step`) replaces
  Theorem 5 and is now used: it discharges `pres_on`.
- The forgetting of stage-by-stage composition is repaired by passing `choice_inv`
  from the service stages to the choice (`fv_NI_comp_on`), and the one place it
  matters is C2, via `secret_ready_public`: under the invariant, whether a secret
  handler is ready is a function of public fields.

## 6. Plan for Section V (keep)

Restructure V-B around `sta`:
1. Route the reader: after peeling off the outer map and the loop, the goal is
   `sta_NI`.
2. Its obligations: `f_EP`, trivial but illustrative (an interrupt only sets a
   private bit); then `fv_NI`.
3. `fv_NI` by cases on the event: input (trivial, `set_pending`); output (the six
   stages of §2), leading to the forgetting story, possibly in its own subsection
   (decide when there is a draft).
4. The overview of the six stages' obligations (§2), and the case analysis of
   `initiate_next` (§3), including why C2 must be impossible (S vs U, public tag).
5. Theorem 5 last, as the secondary result that the hook changes nothing.

The function-vs-predicate decision (§5) changes how steps 3–5 are told; draft with
the function, or settle the predicate first.
