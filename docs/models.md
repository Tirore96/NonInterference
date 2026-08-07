# NonInterference — model documentation

*Prose companion to [`theories/models.v`](../theories/models.v).*

There is one generic model. Instantiating it one way gives a design that leaks a
secret interrupt through scheduling; instantiating it another way gives one that
does not. This document defines the generic model, then the two instantiations,
then one concrete system to run them on. Names are those of the source, and every
process is given with the `@` and `Ty` annotations erased (section 0 says why the
source needs them); no proof code is reproduced.

> Why one instantiation is non-interfering and the other is not — the security
> relations, the classification of each interface, and the central proof obligation
> — is in [`noninterference.md`](noninterference.md), the companion to
> [`theories/noninterference.v`](../theories/noninterference.v).

| Model | Type | What it is |
|---|---|---|
| `model_immediate` | `Proc T_in (T_out' Opub Opriv)` | Interrupts handled the ordinary way: a handler runs as soon as its interrupt is serviced. Secret interrupts leak through scheduling. |
| `model_sliced` | `Proc T_in (T_out' Opub Opriv)` | Interrupt masking controlled so that a secret interrupt can be serviced without disturbing the public schedule. Like `model_immediate`, its output exposes every pool slot. |
| `model_sliced_userview` | `Proc T_in (T_out Opub Opriv)` | `model_sliced` behind a projection of the pool's output that erases every slot but the two user space processes. This is the model the headline theorem is about. |

## Contents

**Part I — the generic model.**
[0. Preliminaries](#0-preliminaries-the-process-algebra) ·
[1. The generic model](#1-the-generic-model) ·
[2. Interrupt handler and slot map](#2-interrupt-handler-and-slot-map) ·
[3. Process pool](#3-process-pool) ·
[4. Stateful wrapper](#4-stateful-wrapper) ·
[5. Model state](#5-model-state) ·
[6. State transitions](#6-state-transitions) ·
[7. The generic model, and its three parameters](#7-the-generic-model-and-its-three-parameters)

**Part II — the two designs.**
[8. Side by side](#8-the-two-designs-side-by-side) ·
[9. `model_sliced_userview`](#9-model_sliced_userview)

**Part III — one concrete system.**
[10. A concrete system](#10-a-concrete-system) ·
[11. Adequacy: the example traces](#11-adequacy-the-example-traces)


## 0. Preliminaries: the process algebra

Everything below is built from a small process calculus (defined in
[`theories/definitions.v`](../theories/definitions.v)). The calculus and its
non-interference theorems are due to Rafnsson et al., *Timing-Sensitive
Noninterference through Composition* ([POST
2017](https://users.ece.cmu.edu/~lbauer/papers/2017/post2017-compose-time.pdf));
mechanising them is part of the contribution of this development. The
mechanisation departs from the paper in one respect: **definitions the paper gives
coinductively are given inductively here** — `oblivious`, for instance, is stated
over the traces a process admits rather than over an infinite stream. The proofs
are substantially simpler for it, since they never have to construct streams.

A process has type `Proc I O`, where `I` and `O` are its input and output
interfaces. It runs by alternating input steps and output steps. There are seven
constructors:

- **`out o`** — constant process. Ignores every input; every output step emits
  the fixed value `o` and the process is unchanged.
- **`map f g p`** — rewire `p` at the interface. Each incoming input is passed
  through `f` before reaching `p`, and each of `p`'s outputs is passed through `g`
  on the way out. (`Proc I' O → Proc I O'`)
- **`sta f g v p`** — give `p` a state cell holding `v`. On input `i` the cell
  updates to `f i v` and `p` sees the new value alongside `i`; on an output `o`
  from `p` the cell updates to `g o v` and the whole process emits the pair
  `(new-state, o)`. So a `sta` process *exposes* its state in its output stream
  and threads it across steps.
- **`swi b p`** — a one-bit "switch" in phase `b`, wrapping a `p` whose output is
  tagged with a Bool. An input `(b', i)` flips the phase by `b ← xor b b'` and
  hands `i` to `p`. On output: in phase `false` the switch emits `None` and stays
  closed; in phase `true` it lets `p`'s tagged output `(c, o)` through as `Some o`
  and re-flips the phase by the tag, `b ← xor true c`. `swi` is how a pool slot is
  gated on / off (section 3).
- **`par p1 p2`** — broadcast the same input to `p1` and `p2`; each output step
  pairs one output of `p1` with one output of `p2`.
- **`loop p`** — feedback: every output `p` produces is immediately fed back to
  `p` as its next input. (`Proc I I → Proc I I`)
- **`maybe p`** — make the input optional. Input `None` is a no-op (`p` idles);
  input `Some i` steps `p` on `i`. Outputs pass through unchanged.
  (`Proc I O → Proc (Option I) O`)

> **Why interfaces are not just types.** `I` and `O` are drawn from an inductive
> `Ty` (`Nat`, `Bool`, `Unit`, `Times`, `Option`, `Sum`, ...), and `[t]` interprets a
> `t : Ty` as the `Set` it encodes. Going through `Ty` rather than through `Set`
> directly is what makes reductions invertible, which the negative result needs: to
> refute non-interference one must show a trace is *not* accepted. The cost is the
> explicit annotations in the source, which this document strips away.

The whole development ends by proving `NI` of `model_sliced_userview`. What `Trace`
and `NI` mean, and the equivalences they are indexed by, are in
[`noninterference.md` §1](noninterference.md).


# Part I — the generic model

## 1. The generic model

```coq
model runtime init handler_preroutine bool_coding p_pub p_priv p_sched =
  reactive_system init (state_step handler_preroutine bool_coding) def
    (pool runtime p_pub p_priv p_sched) pool_input
      : Proc T_in (T_out' Opub Opriv)
```

An operating system as a single process: a **pool** of cooperating processes
(section 3) — three interrupt handlers, a scheduler, two user processes — closed
into a self-driving whole by a **stateful wrapper** (section 4) that threads the
global state and decides, on every step, whose turn it is (sections 5 and 6).

It consumes interrupts and emits one tuple per step holding every slot's output.
Nothing in it is committed to a security design: that is entirely the job of the
three parameters `init`, `handler_preroutine` and `bool_coding`, which section 7
sets out and Part II fixes in two different ways — once so that a secret interrupt
leaks, once so that it does not.

Sections 2 to 6 define each piece, bottom-up.


## 2. Interrupt handler and slot map

The only leaf process the mechanism itself fixes is the interrupt handler. The
scheduler and the two user processes are parameters — they are what the mechanism
is meant to protect, not part of it — and are supplied in section 10.

**`I_handler runtime : Proc Empty THandlerOutput`** (`handler_type`)

```coq
I_handler runtime =
  map id (fun o => if o.1 == 0 then Notify else Nothing)
    (sta (fun _ v => v) (fun _ v => v.+1 %% runtime) 0 (out tt))
```

Its state cell counts modulo `runtime` and the emitted value is read off the
*updated* cell: `Notify` when it is 0, `Nothing` otherwise. So each activation emits
`runtime - 1` `Nothing`s and then a `Notify` signalling completion — a fixed number
of output steps. Its input type is `Empty`: a handler is driven entirely by the
interrupt controller and never consumes input.

`runtime` is a parameter. The security argument needs only that all three handlers
share it, so that a secret handler's run is exactly as long as the filler run it
replaces. (`runtime = 0` degenerates — `n %% 0 = n`, so the cell never returns to 0
and the handler never signals completion. Nothing breaks; the handler simply never
finishes.)

**The slot map.** `my_f_I` and `my_f_O` give the interfaces of pool slot `n`, and
`slot_procs` gives its process:

| slot | process | input | output |
|---|---|---|---|
| 0 | timer-interrupt handler | `Empty` | `THandlerOutput` |
| 1 | disk-interrupt handler | `Empty` | `THandlerOutput` |
| 2 | default handler | `Empty` | `THandlerOutput` |
| 3 | scheduler (parameter `p_sched`) | `Empty` | `Nat` |
| 4 | secret user process (`p_priv`) | `THandlerOutput` | `Opriv` |
| 5 | public user process (`p_pub`) | `Empty` | `Opub` |
| ≥6 | padding, `unit_proc = out tt` | `Empty` | `Unit` |

```coq
slot_procs runtime p_pub p_priv p_sched n =
  match n with
  | 0 | 1 | 2 => I_handler runtime
  | 3 => p_sched  | 4 => p_priv  | 5 => p_pub
  | _ => unit_proc
  end
```

`Opub` and `Opriv`, the alphabets the two user processes emit over, are parameters
for the same reason the processes are: nothing in the mechanism inspects a user-slot
*value*, only whether the slot produced one (section 6).

Slots 0, 1 and 2 are three *separate* handlers reusing one definition; what
distinguishes them is their own pending and mask bits in the interrupt controller
(section 5), and which interrupt sets them. Only slot 4 has a non-`Empty` input:
the secret user process is the one process that consumes anything, namely the disk
handler's `Notify`. `process_pool` recurses over slot indices, so the family must be
total on `nat`; `unit_proc` exists only for that, and nothing above 5 is ever
selected.

**Layout invariant.** The public process is outermost (slot 5), then the secret
process (4), then the scheduler (3), matching the pids `my_f_pid` assigns. This
ordering cannot be varied: the output accessors of section 6 are tuple patterns
that hardwire *two* user slots sitting before the scheduler slot, so adding or
reordering user slots changes the state transition and lands in the `fv_NI`
obligation. The pool is also right-associated, so the two user slots are leftmost
but not a subterm — there is no `par userspace system` to point at.


## 3. Process pool

The pool wires slots `0..n` into one process, each gated by a switch so that only
the slot matching the current pid is live.

```coq
process_pool n f_initial f_I f_O f_proj f_pid f_proc =
  match n with
  | 0 =>
      map (fun i => (f_pid i.1 == 0, f_proj i.2 0)) id
        (swi (f_initial 0) (maybe (map id (fun o => (true, o)) (f_proc 0))))
  | n0.+1 =>
      par (map (fun i => (f_pid i.1 == n0.+1, f_proj i.2 n0.+1)) id
             (swi (f_initial n0.+1) (maybe (map id (fun o => (true, o)) (f_proc n0.+1)))))
          (process_pool n0 ...)
  end
    : Proc (Times cur_pid T') (times_on n f_O)
```

Reading a single slot `k` from the inside out: `f_proc k` is the slot's process, and
`map id (fun o => (true, o))` tags each output with the constant bit `true`; `maybe`
makes the input optional, so the slot idles unless handed `Some`; `swi (f_initial k)`
gates it, forwarding output only in phase `true`, and the constant `true` tag closes
the phase after one output — so a selected slot advances by exactly one step and
then waits to be re-selected (every process is cooperative); the outer `map`
computes the switch bit `f_pid cur_pid == k` and the slot's payload `f_proj T' k`.

`par` lays the slots side by side and `times_on n f_O` is the nested product of all
slot outputs, each wrapped in `Option`. The net effect: exactly the slot whose index
equals the current pid advances and emits; all others emit `None`.

**Instantiation.** `cur_pid = Sum Bool Nat` — process ids, split so the `inl` side
holds **exactly the two secret ids** and the `inr` side everything public:

| pid | selects slot | | pid | selects slot |
|---|---|---|---|---|
| `inl true` | 1, disk handler | | `inr 0` | 0, timer handler |
| `inl false` | 2, default/NOP handler | | `inr 1` | 3, scheduler |
| | | | `inr 2` | 4, secret user process |
| | | | `inr 3` | 5, public user process |

The timer handler is `inr 0`, on the public side: it is a handler, but not a secret
one. The split is not "handler versus not" — `is_handler_pid` is true of `inr 0` as
well as of both `inl` ids. Its purpose is to delimit which ids are secret values, so
the state relation can classify them in one place (`eqsum privateRel publicRel`) and
the proof can case-split on the tag ([`noninterference.md`
§7b](noninterference.md)).

The rest: `initial_pid = inr 3`, so the system starts in the public user process;
`my_f_initial n = (n == my_f_pid initial_pid)` opens only that slot; and `f_proj`
routes the shared payload, of type `Option THandlerOutput`, to slot 4 alone —

```coq
f_proj i n = match n with 4 => i | _ => None end
```

— which is the whole reason every other slot can declare its input type `Empty`.
`pool runtime p_pub p_priv p_sched` is `process_pool` at 5 with these, i.e. the
six-slot pool.


## 4. Stateful wrapper

The pool consumes `(cur_pid, T')` and produces a product of slot outputs. On its own
it has no state and no way to drive itself. `reactive_system` closes it into a single
self-driving `Proc T_in T_out'` by adding the global state and a feedback loop.

```coq
reactive_system state state_update def p pool_input =
  map inl (inr_or_def def)
    (loop (map id snd
      (sta state_update (fun _ v => v) state
        (map pool_input inr (maybe p)))))
```

From the inside out: `maybe p` runs the pool, idling on `None`; `map pool_input inr`
turns each pool result into the pool's *next* input, tagging it `inr` for the
feedback channel; `sta state_update ... state` holds the global state and advances it
on every event, external input or fed-back output; `loop` ties output back to input;
and the outer `map` presents external inputs on the left and, on the way out, applies
`inr_or_def def x = if x is inr x' then x' else def`, substituting `def` — the
all-`None` tuple — when there is no genuine external output yet.

`state_update` is `state_step ...` (section 6), and `pool_input` routes the pool:

```coq
pool_input (v, event) = if event is inr o then Some (get_cur_pid v, dI_out o) else None
```

On a pool output it feeds back the current pid together with the disk handler's
output component — the wire that delivers a disk `Notify` to the secret user
process.


## 5. Model state

The global state cell threaded by `reactive_system` has type

```coq
stateType = ((cur_pid, prev_pid), (re_sch, (ir_count, ic)))
```

| field | type | meaning |
|---|---|---|
| `cur_pid` | `Sum Bool Nat` | the pid whose slot is currently live (section 3) |
| `prev_pid` | `Option Nat` | the user pid to return to once handlers finish |
| `re_sch` | `Bool` | reschedule flag: control should go to the scheduler rather than back to the interrupted process |
| `ir_count` | `Option Nat` | the handler time-slice counter: `None` when disabled, `Some n` when `n` handler output-steps remain, `Some 0` when the slice is over |
| `ic` | `Times I_bits (Times I_bits I_bits)` | the interrupt controller: one `I_bits` per interrupt, in order default, disk, timer |
| `I_bits` | `Times pending mask` | `pending` — an interrupt of this kind has arrived and awaits service; `mask` — service is currently blocked |

The file then defines the obvious getters and setters (`get_cur_pid`,
`update_I_mask`, ...), the boolean helpers `set_masks` / `unset_masks` / `masks_set`
(all-masked is the "a handler is running, do not nest" condition), and
`or_bool_state`, which merges requested controller bits into the live state while
keeping the time slice untouched. A handler is *selectable* for an interrupt kind iff
it is pending and not masked (`I_ready`); `first_ready` picks the highest-priority
ready one, in the fixed order timer > disk > default.


## 6. State transitions

First, the accessors that read a pool output: `tI_out` / `dI_out` / `default_I_out`
pick out the three handler slots, `is_I_out_done` reports which handler (if any) just
emitted `Notify`, and `is_sch_out` matches the scheduler slot. Note what `is_sch_out`
does *not* do: it matches `(None, (None, (Some n, _)))`, so the two user slots are
inspected for `None`-ness and nothing more. No stage below ever reads a user-slot
*value*, which is why the state transition is independent of what userspace does.

`state_update` is `state_step handler_preroutine bool_coding`, applied once per
event and composed of four stages (right to left):

```coq
state_step ... i  =  initiate_next(bool_coding) ∘ handler_preroutine
                     ∘ apply_schedule ∘ record_pending    (each guarded by the event i)
```

- **`record_pending`** — on an external interrupt input, set that interrupt's
  `pending` bit.
- **`apply_schedule`** — on a scheduler output, set `cur_pid` to the scheduled pid.
- **`handler_preroutine`** — a parameter; see section 7.
- **`initiate_next(bool_coding)`** — decide who runs next:

  ```coq
  initiate_next bc v =
    if masks_set v then v                     (* a handler is running *)
    else let v := bc v in                     (* the second parameter *)
         if first_ready v is Some ir then initiate_handler ir v
         else if is_handler_pid v
              then if get_re_sch v then initiate_scheduler v
                                   else initiate_prev_pid v
              else v                           (* stay in user space *)
  ```

  `initiate_handler` saves the current user pid to `prev_pid`, points `cur_pid` at
  the handler, sets all masks, and clears that interrupt's `pending` bit.
  (`initiate_next` is wrapped in `step_right` — applied only on output events, not on
  inputs — which matters for the equivalence proof.)

**Why `state_step` is a composition.** Writing it as a chain of independent stages
rather than one monolithic update lets each stage be reasoned about on its own, which
is what makes the central proof obligation tractable. The cost is that each stage is
analysed over *all* states, forgetting the reachable subset the previous stage
produces — which is exactly what `bool_coding` exists to compensate for (section 8b).
The proof-side story is in [`noninterference.md`](noninterference.md).


## 7. The generic model, and its three parameters

That completes it:

```coq
model runtime init handler_preroutine bool_coding p_pub p_priv p_sched =
  reactive_system init (state_step handler_preroutine bool_coding) def
    (pool runtime p_pub p_priv p_sched) pool_input
```

The pool, the state layout, `record_pending`, `apply_schedule` and `initiate_next`
are the same term in both designs. What is left free is a triple, and each part of it
is a distinct point of control over *when a handler is allowed to run*:

- **`init : [stateType]`** — the state the system starts in. Because a handler is
  serviceable exactly when it is pending and unmasked, the initial masks decide which
  interrupts can be serviced before anything at all has happened. It also decides
  whether the time-slice counter is enabled (`Some _`) or switched off (`None`).

- **`handler_preroutine : [T_out'] -> [stateType] -> [stateType]`** — runs on each
  pool *output*, immediately before `initiate_next`. It is the only place a design
  sees a handler announce completion, and so the only place it can reopen masks. It
  therefore decides **when the next handler becomes eligible** — the difference
  between reopening as soon as a handler says it is done, and reopening only at a
  fixed boundary.

- **`bool_coding : [stateType] -> [stateType]`** — consulted by `initiate_next`,
  after the "is a handler already running" test and before `first_ready` picks the
  next one. It is the design's last chance to constrain the state that the choice is
  made from. Its real use is the one named above: re-imposing an invariant that the
  compositional proof has forgotten, so that the choice can be shown to come out the
  same in two related executions.

Between them: `init` says what is runnable at rest, `handler_preroutine` says when
that changes, and `bool_coding` says what must hold when the choice is made.


# Part II — the two designs

## 8. The two designs, side by side

Both are `model` at a different triple, and that difference is the whole security
story.

| | `model_immediate` | `model_sliced` |
|---|---|---|
| **`init`** | all masks clear; counter `None` (disabled) | all masks set except the timer's; counter `Some 0` |
| **`handler_preroutine`** | `immediate_preroutine`: on a handler's `Notify`, unmask everything; if it was the timer, ask to reschedule | `sliced_preroutine`: reload the slice on a timer `Notify`, unmask at fixed boundaries, tick the slice |
| **`bool_coding`** | `id` (no bookkeeping) | `bool_coding`: restore the time-slice invariant; force the default mask to equal the disk mask |
| **When a handler stops** | when it emits its **secret** `Notify` — *secret-driven* | at a fixed **public** time-slice boundary — *slice-driven* |
| **What mask changes track** | secret handler behaviour | public slice boundaries |
| **Non-interfering?** | **No** (`model_immediate_not_NI`) | **Yes** (`model_sliced_NI`, for any non-interfering userspace) |
| **Why** | a handler runs as soon as its interrupt is serviced, so a secret interrupt displaces the scheduled process and the gap is visible | handlers run only within the public slice, replacing NOP filler, so the schedule is unchanged |

Handlers must all run for the same length of time, or the schedule would again
depend on which interrupt arrived. The three handler slots therefore reuse one
`I_handler runtime` (section 2), and the slice is `runs * runtime` — a whole number
of handler runs by construction, so it always ends on a handler boundary. A real
system would reach a fixed length by padding.

### 8a. `model_immediate`

```coq
model_immediate runtime p_pub p_priv p_sched =
  model runtime initial_state_immediate immediate_preroutine id p_pub p_priv p_sched

initial_state_immediate = ((initial_pid, None), (false, (None, false_ic)))

immediate_preroutine o v =
  if is_I_out_done o is Some ir
  then let v := unset_masks v in
       if ir is TimerInterrupt then update_re_sch v true else v
  else v
```

The counter is disabled and every controller bit clear, so the system starts with
every interrupt serviceable. A handler signals completion by emitting `Notify`, and
`immediate_preroutine` responds by unmasking everything — if it was the timer, also
asking to reschedule. `bool_coding` is `id`: there is no bookkeeping to do.

**Why it leaks.** Nothing constrains *when* a handler runs. Since all masks are
clear, an interrupt is serviced as soon as it arrives, and its handler runs for its
full `runtime` steps in place of whichever process was running — pushing every later
public output back by that much. The handler's own output is secret and the attacker
cannot see it, but the public process's slot is not, and across those steps it
carries nothing: an output that was due and did not arrive. `model_immediate_not_NI`
turns that into a counterexample ([`noninterference.md` §5](noninterference.md));
section 11 shows it in the model's own traces.

### 8b. `model_sliced`

```coq
model_sliced runtime runs p_pub p_priv p_sched =
  model runtime initial_state_sliced (sliced_preroutine runtime runs) bool_coding
    p_pub p_priv p_sched

sliced_preroutine o = check_ir_count ∘ check_handler_completed ∘ initiate_ir o
```

Unlike `immediate_preroutine`, the handler preroutine here is a composition of three
stages. The rest of this section walks it right to left — `initiate_ir` opens a
slice, `check_handler_completed` reopens masks at a boundary inside it, and
`check_ir_count` ticks it and closes it — and then covers `bool_coding`.

Two things change relative to `model_immediate`. **All masks start set except the
timer's**, so a secret handler can never be started merely because its interrupt
arrived; the only interrupt serviceable from rest is the public timer. And **a fixed
time slice replaces "run until the handler says it is done"**: what ends a handler's
turn is the slice, not the handler's own secret output.

```coq
initial_state_sliced = ((initial_pid, None), (false, (Some 0, mask_most)))
mask_most = ((false,true), ((false,true), (false,false)))
            (* pending false everywhere; masks set for default and disk,
               clear for the timer *)
```

**`initiate_ir` — open a slice.**

```coq
initiate_ir runtime runs o v =
  if tI_out o is Some Notify then update_ir_count v (Some (time_slice runtime runs))
  else v
```

When the timer handler completes, load the counter to `time_slice runtime runs`. The
slice is `runs` complete handler executions long, so that many can take place before
it ends. The timer is public, so *when* slices start is public.

**`check_handler_completed` — reopen the masks at a boundary.**

```coq
time_slice runtime runs = runs * runtime

handler_completed runtime c =
  match c with
  | Some n => (n != 0) && (n %% runtime == 0)   (* on a handler boundary *)
  | None   => false
  end

check_handler_completed runtime v =
  if handler_completed runtime (ir_count v) then set_tI (unset_masks v) else v
```

Because the slice is *defined* as `runs * runtime`, it always ends on a handler
boundary, and the counter is a nonzero multiple of `runtime` precisely when a handler
has just finished — which is what `handler_completed` computes, rather than
assumes. Note this reads the *counter*, not the handler's output: the boundary is
public, whichever handler happens to be occupying the slot.

**`check_ir_count` — tick, and close.**

```coq
check_ir_count v =
  match ir_count v with
  | Some n.+1 => update_ir_count v (Some n)                 (* tick down *)
  | Some 0    => update_ir_count (set_otherIs (unset_tI v)) None
  | None      => v
  end
```

The `Some 0` case is the mirror image of `check_handler_completed`: it closes the
slice by masking the secret handlers and unmasking the timer, so the only interrupt
serviceable next is the public one that starts the next slice.

Together, at the concrete instance of section 10, where a slice of 4 is two runs of a
2-step handler:

```text
  ir_count    what just happened            masks after this step
  ────────────────────────────────────────────────────────────────────────
  Some 4  ──▶ timer handler completed  ──▶  disk + NOP unmasked, timer masked
                (slice starts)                 │
  Some 3  ──▶ (mid-run)                ──▶    unchanged
                                              ▼
  Some 2  ──▶ a disk/NOP handler       ──▶  disk + NOP unmasked, timer masked
                completed                      │   (so the second run can start)
  Some 1  ──▶ (mid-run)                ──▶    unchanged
                                              ▼
  Some 0  ──▶ slice over               ──▶  disk + NOP masked, timer unmasked,
                                              counter disabled (None)
```

`Some 4` and `Some 2` are the nonzero multiples of `runtime` below the slice, so they
are exactly the boundaries `handler_completed` marks, and at both the secret handlers
are the ones left runnable. A secret handler run therefore takes the place of a
default/NOP run instead of displacing a user process, and a slice containing a disk
run has the same shape as one containing only filler.

**`bool_coding`.**

```coq
timeslice_live c = (c is Some n with 0 < n)

bool_coding v =
  let b := timeslice_live (ir_count v) in
  let ic := (true, (None, ((b,~~b), ((false,~~b), (false,b))))) in
  let v := update_bool_state v (or_bool_state (bool_state v) ic) in
  update_I_mask v DefaultInterrupt (get_I_mask v DiskInterrupt)
```

It ORs a controller pattern, parameterised by whether the slice is live, into the
state, then forces the default mask to equal the disk mask.

*Why it is needed.* Two facts hold of every state the model can actually reach:

```text
(i)  slice live  ⇒  NOP pending, NOP and disk unmasked, timer masked
(ii) the NOP and disk masks are always toggled together
```

Both are invariants, and neither is available to the proof: writing `state_step` as a
composition of independent stages (section 6) buys tractability at the cost of
forgetting what the previous stage established, so each stage must be proved for
*every* pair of related states, including ones that never arise. `bool_coding` puts
the two facts back — the OR for (i), the mask equality for (ii). On any reachable
state both are no-ops; stated unconditionally, they narrow the state space
`initiate_next` is analysed over enough for the argument to go through.

The pattern is parameterised by `timeslice_live`, which reads only `ir_count` — a
public field — so it is the same across two related executions. That is what makes
this legitimate rather than question-begging, and it is where the fact that the slice
is started by the *public* timer handler does real work.
[`noninterference.md` §7d](noninterference.md) gives the proof-side account.


## 9. `model_sliced_userview`

`model_sliced` still exposes the whole pool output, including handler and scheduler
activity. The final model erases every slot but the two user space processes.

```coq
parse_output o =
  match o with
  | (Some public, _)      => Some (inl public)   (* public user output *)
  | (None, (Some prv, _)) => Some (inr prv)      (* the secret syscall *)
  | _                     => None
  end

model_sliced_userview runtime runs p_pub p_priv p_sched =
  map id parse_output (model_sliced runtime runs p_pub p_priv p_sched)
    : Proc T_in (T_out Opub Opriv)

final_out_rel Opub Opriv = eqmaybe_false (eqsum (publicRel Opub) (privateRel Opriv))
```

Of the six output slots only two survive — the public one re-tagged `inl` and the
secret one `inr`; every other slot, and any all-`None` tuple, projects to `None`.
`final_out_rel` is the output relation the top theorem uses: the public component
compared exactly, the syscall component treated as secret.

`model_sliced_userview_NI` proves `NI in_rel final_out_rel model_sliced_userview` —
the payoff: with fixed-length, masked handling, the presence of a secret disk
interrupt is invisible in the user-space output. The proof is documented in
[`noninterference.md`](noninterference.md).


# Part III — one concrete system

## 10. A concrete system

Nothing in Parts I and II names a user process, a scheduler, a handler length or a
slice size. This section supplies one of each, so both designs can be run.

```coq
low_p     = out GetRequest                                    (* public user process *)
high_p    = alternate Syscall NOP tt (fun i => i == Notify)   (* secret user process *)
scheduler = map id (fun o => o.1 + 2)
              (sta (fun _ v => v) (fun _ v => v.+1 %% 2) 1 (out tt))

handler_runtime = 2      (* each handler runs for two output steps *)
slice_runs      = 2      (* a slice is two complete handler runs, so four steps *)
```

`low_p` does nothing but repeatedly issue the public request `GetRequest`.

`high_p` issues a `Syscall` in any cycle where it received a `Notify` — the disk
handler telling it a disk event occurred, over the wire of section 4 — and a harmless
`NOP` otherwise. Which of the two it emits is secret-dependent, but that is not
itself the leak: both are classified secret, so the attacker cannot tell them apart
([`noninterference.md` §4](noninterference.md)). What must not leak is the
*scheduling*. It is built from a reusable two-phase process,

```coq
alternate x y z pred =
  map inl (fun o => if o is inr (true, _) then x else y)
    (loop (map id inr
      (sta (fun i v => if i is inl i' then v || pred i' else false)
           (fun o v => v) false (out z))))
```

which emits `x` when it has seen a `pred`-matching input since it last fired and `y`
otherwise: a one-bit accumulator latches on a match, the loop feedback clears it once
per cycle, and the outer `map` reads the tag.

`scheduler` is a round-robin over the two user processes — the cell toggles 0/1 from
1 and the output adds 2, so the pid alternates 2, 3, 2, 3, i.e. secret then public.
Its input type is `Empty`: it only proposes the next process id.

```coq
model_immediate_concrete       = model_immediate       handler_runtime            low_p high_p scheduler
model_sliced_concrete          = model_sliced          handler_runtime slice_runs low_p high_p scheduler
model_sliced_userview_concrete = model_sliced_userview handler_runtime slice_runs low_p high_p scheduler
```

`model_sliced_NI` and `model_sliced_userview_NI` are proved of the *parametric*
models, and hold for any scheduler and any two user processes that are themselves
non-interfering at the classification their slot declares ([`noninterference.md`
§6](noninterference.md)). These instances are what the traces below, and the
counterexample `model_immediate_not_NI`, are stated at.


## 11. Adequacy: the example traces

Each design is exercised on two runs of the concrete system — one with no disk
interrupt, one with a disk interrupt — and each run is proved to be an accepted
trace. Reading a design's two runs against each other is what exhibits its
behaviour, so both are shown aligned, with `≠` marking every row on which they
differ.

Every output is a six-slot tuple with exactly one slot `Some` at a time. The slot
order is the *reverse* of the pool index of section 2:

| slot | carries | classified |
|---|---|---|
| `pub` | public user output | public |
| `sys` | the secret process's `Syscall` or `NOP` | secret |
| `pid` | scheduled pid | public |
| `dfl` | default/NOP handler output | secret |
| `dsk` | disk handler output | secret |
| `tmr` | timer handler output | public |

The last column is the classification `out_rel` gives each slot
([`noninterference.md` §4](noninterference.md)); the tables below are read against
it. In them a row is one step, named by the slot it fills: `·` is `None`, `Nth` is
`Nothing`, `Nfy` is `Notify`, and `sch hi` / `sch lo` are scheduler outputs naming
the secret and the public process. Since a handler activation is always `Nothing`
then `Notify`, an `Nth`/`Nfy` pair is exactly one complete handler run.

### `model_immediate`: the leak

`trace_immediate_no_dI'` against `trace_immediate_with_dI'`.

```text
  no disk interrupt        with disk interrupt
  ──────────────────────────────────────────────
  Get                      Get
                           dI                     ← secret input
                           Get
                           dsk  Nth               ← the disk handler runs immediately, wherever
                           dsk  Nfy                 its interrupt happened to be serviced
                           Get
  tI                       tI
  Get                      Get
  tmr  Nth                 tmr  Nth
  tmr  Nfy                 tmr  Nfy
  sch  hi                  sch  hi
  NOP                   ≠  Sys                    ← the secret process reacts
  tI                       tI
  NOP                      NOP
  tmr  Nth                 tmr  Nth
  tmr  Nfy                 tmr  Nfy
  sch  lo                  sch  lo
  Get                      Get
```

What this shows is *where* a handler run may appear. In `model_immediate` it appears
wherever its interrupt happened to be serviced: the disk run lands in the middle of
the public output stream, and everything after it shifts down. The handler's own slot
is secret and the public slot is not, so what an attacker observes is not the handler
but its effect — steps on which a public output was due and nothing arrived.
`model_immediate_not_NI` ([`noninterference.md` §5](noninterference.md)) turns that
into a counterexample using a trace of just two public requests.

### `model_sliced`: the same two runs, and the projection

`trace_sliced_no_dI'` against `trace_sliced_with_dI'`, in the same layout. The extra
column is what `model_sliced_userview` emits for that step, i.e. the row under
`parse_output`.

```text
  no disk interrupt        with disk interrupt   user view
  ──────────────────────────────────────────────────────────
  Get                      Get                   Get
                           dI                    dI          ← secret input: nothing happens, the disk
                           Get                   Get           interrupt is masked until a slice opens
                           Get                   Get
  tI                       tI                    tI
  Get                      Get                   Get
  tmr  Nth                 tmr  Nth              ·
  tmr  Nfy                 tmr  Nfy              ·
  dfl  Nth              ≠  dsk  Nth              ·           ┐ the slice: two handler runs, and the
  dfl  Nfy              ≠  dsk  Nfy              ·           │ whole difference between the two runs
  dfl  Nth                 dfl  Nth              ·           │ is that the disk handler takes the
  dfl  Nfy                 dfl  Nfy              ·           ┘ place of the first NOP run
  sch  hi                  sch  hi               ·
  NOP                   ≠  Sys                   NOP / Sys   ← both secret, so indistinguishable at ⊥
  tI                       tI                    tI
  NOP                      NOP                   NOP
  tmr  Nth                 tmr  Nth              ·
  tmr  Nfy                 tmr  Nfy              ·
  dfl  Nth                 dfl  Nth              ·           ┐
  dfl  Nfy                 dfl  Nfy              ·           │ second slice, identical in both runs
  dfl  Nth                 dfl  Nth              ·           │
  dfl  Nfy                 dfl  Nfy              ·           ┘
  sch  lo                  sch  lo               ·
  Get                      Get                   Get
```

Three things stand out, and they are the whole argument in miniature.

**A handler run can appear in only one place.** Compare with `model_immediate`
above, where the disk handler ran the moment its interrupt was serviced. Here the
disk interrupt arrives and *nothing happens*: it is masked, so it is merely recorded
as pending, and the public process carries on emitting. Only when the timer handler
completes does a slice open, and only inside that slice may a handler run.

**Inside the slice, the disk handler substitutes for a NOP run.** That is the only
structural difference between the two runs — the `≠` at the first of the two handler
runs. It is a substitution, not an insertion: the slice is `runs * runtime` steps
either way, so the run with a secret interrupt is exactly as long, and the public
skeleton around it — the timer handler, the scheduled pid, the resumed `Get` — is
identical. The second slice, where no interrupt is waiting, is `dfl` in both.

**The projection erases the substitution entirely.** Both `dsk` and `dfl` sit in
slots `parse_output` discards, so the user view column is `·` on every handler step
and on every scheduled pid, in both runs alike. The only surviving difference is the
secret process reacting to its notification, `NOP` against `Sys` — and both of those
are classified secret, so an observer at `⊥` cannot tell them apart. Nothing the
attacker can see distinguishes the two runs, which is what
`model_sliced_userview_NI` proves in general.


## Where to go next

That is the whole construction. What it does *not* say is why any of it is secure:
nothing above defines what an attacker can observe, and the claims made in passing —
that a slot is public, that the pid split matters, that a handler run must be
indistinguishable from filler — are stated but not made precise.

That is the subject of [`noninterference.md`](noninterference.md): the security
relation carried by each interface, the counterexample for `model_immediate`, how the
generic theorems compose to prove `model_sliced`, and the one substantial obligation
(`fv_NI`) that the compositional structure of `state_step` and `bool_coding` exist to
make tractable.
