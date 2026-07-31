# NonInterference — model documentation

*Prose companion to [`theories/models.v`](../theories/models.v).*

This document explains what the three models of
[`theories/models.v`](../theories/models.v) are and why the sliced one is built the
way it is. It follows the order of the Coq file — generic building blocks first,
then the concrete instantiations. Names are those of the source, so the two can be
read side by side, and every process is given in a lightweight notation with the
`@` and `Ty` annotations erased (section 0 explains why the source needs them); no
proof code is reproduced.

> Why `model_sliced` is non-interfering and `model_immediate` is not — the security
> relations, the classification of each interface, and the central proof obligation
> — is in [`noninterference.md`](noninterference.md), the companion to
> [`theories/noninterference.v`](../theories/noninterference.v).

## The three models

Defined in sections 7–9 below.

| Model | Type | What it is |
|---|---|---|
| `model_immediate` | `Proc T_in T_out'C` | Interrupts handled the ordinary way: a handler runs as soon as its interrupt is serviced. Secret interrupts leak through scheduling. |
| `model_sliced` | `Proc T_in (T_out' Opub Opriv)` | Interrupt masking controlled so that a secret interrupt can be serviced without disturbing the public schedule. Like `model_immediate`, its output exposes every pool slot: the two user processes, the scheduler and all three handlers. |
| `model_sliced_userview` | `Proc T_in (T_out Opub Opriv)` | `model_sliced` behind a projection that keeps only the user-visible channel. This is the model the headline theorem is about. |

## Contents

0. [Preliminaries: the process algebra](#0-preliminaries-the-process-algebra)
1. [Userspace processes, scheduler and interrupt handler](#1-userspace-processes-scheduler-and-interrupt-handler)
2. [Process pool](#2-process-pool)
3. [Stateful wrapper](#3-stateful-wrapper)
4. [Model state](#4-model-state)
5. [State transitions](#5-state-transitions)
6. [Trace vocabulary](#6-trace-vocabulary)
7. [`model_immediate`](#7-model_immediate)
8. [`model_sliced`](#8-model_sliced)
9. [`model_sliced_userview`](#9-model_sliced_userview)


## 0. Preliminaries: the process algebra

Everything below is built from a small process calculus (defined in
[`theories/definitions.v`](../theories/definitions.v)). The calculus and its
non-interference theorems are due to Bauer et al., *Composing Security Policies in
Timed Systems* ([POST
2017](https://users.ece.cmu.edu/~lbauer/papers/2017/post2017-compose-time.pdf));
mechanising them is part of the contribution of this development. The
mechanisation departs from the paper in one respect: **definitions the paper gives
coinductively are given inductively here** — `oblivious`, for instance, is stated
over the traces a process admits rather than over an infinite stream. The proofs
are substantially simpler for it, since they never have to construct streams.

A process has type `Proc I O`, where the interface types `I` and `O` are drawn from
an inductive `Ty` (Nat, Bool, Unit, Times, Option, Sum, ...) and `[t]` denotes the
ordinary Coq type that `t : Ty` encodes. Indexing interfaces by the inductive `Ty`
rather than by `Set` is what lets the proofs invert reductions; the cost is the
explicit type annotations in the source, which is exactly what this document strips
away.

A process runs by alternating input steps and output steps. There are seven
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
  gated on / off (see section 2).
- **`par p1 p2`** — broadcast the same input to `p1` and `p2`; each output step
  pairs one output of `p1` with one output of `p2`.
- **`loop p`** — feedback: every output `p` produces is immediately fed back to
  `p` as its next input. (`Proc I I → Proc I I`)
- **`maybe p`** — make the input optional. Input `None` is a no-op (`p` idles);
  input `Some i` steps `p` on `i`. Outputs pass through unchanged.
  (`Proc I O → Proc (Option I) O`)

Two derived notions used throughout:

- **`Trace ORel l s p`** — `s` is a legal input/output sequence of `p`, where each
  output is compared to the trace's label through the relation `ORel` at security
  level `l`.
- **`NI IRel ORel p`** — non-interference: at every level, inserting/removing or
  swapping level-indistinguishable inputs leaves the set of traces unchanged — an
  observer at level `l` cannot tell such inputs apart from `p`'s outputs.

The whole development ends by proving `NI` of `model_sliced_userview`.


## 1. Userspace processes, scheduler and interrupt handler

These are the leaf processes that populate the pool.

**`low_p : Proc Empty TPublicOutput`**

```coq
low_p = out GetRequest
```

The public user-space process. It does nothing but repeatedly issue the public
request `GetRequest`.

**`alternate x y z pred`** — a reusable two-phase process

```coq
alternate x y z pred =
  map inl (fun o => if o is inr (true, _) then x else y)
    (loop (map id inr
      (sta (fun i v => if i is inl i' then v || pred i' else false)
           (fun o v => v) false
           (out z))))
```

`alternate` emits `x` when it has seen a `pred`-matching input since it last
fired, and `y` otherwise. The one-bit accumulator latches to `true` as soon as an
input satisfies `pred`, the loop feedback clears it once per cycle, and the outer
`map` reads the resulting tag.

**`high_p : Proc THandlerOutput TTypeSyscall`**

```coq
high_p = alternate Syscall NOP tt (fun i => i == Notify)
```

The secret user-space process. It issues a `Syscall` in any cycle where it
received a `Notify` (which, in the wiring of section 3, is the disk-interrupt
handler telling it a disk event occurred), and a harmless `NOP` otherwise. Which
of the two it emits is therefore secret-dependent — but that is not itself the
leak: both are classified secret, so the attacker cannot tell a `Syscall` from a
`NOP` (see [`noninterference.md` §4](noninterference.md)). What must not leak is
the *scheduling*: when a secret interrupt is serviced, and hence which process is
running at which step.

**`scheduler : Proc Empty Nat`**

```coq
scheduler =
  map id (fun o => o.1 + 2)
    (sta (fun _ v => v) (fun _ v => v.+1 %% 2) 1 (out tt))
```

A round-robin over the two user processes. The state cell toggles 0/1 (starting
at 1), and the output adds 2, so the emitted pid alternates 2, 3, 2, 3, ... i.e.
`high_p` then `low_p`. Its input type is `Empty`: the scheduler never consumes
input, it only proposes the next process id.

**`I_handler runtime : Proc Empty THandlerOutput`** (`handler_type`)

```coq
I_handler runtime =
  map id (fun o => if o.1 == 0 then Notify else Nothing)
    (sta (fun _ v => v) (fun _ v => v.+1 %% runtime) 0 (out tt))
```

The process *definition* shared by the timer, disk and default handlers. It is
not one handler: slots 0, 1 and 2 are three separate handlers that happen to
reuse this definition, each with its own pending and mask bits in the interrupt
controller (section 4). Its state cell counts modulo `runtime` (starting at 0) and
the emitted value is read off the *updated* cell: `Notify` when it is 0, `Nothing`
otherwise. So each activation emits `runtime - 1` `Nothing`s and then a `Notify`
that signals completion — a fixed number of output steps. Keeping every handler
identical and fixed-length is central to `model_sliced` (section 8). Its input
type is `Empty`: a handler is driven entirely by the interrupt controller and
never consumes input.

`runtime` is a parameter. The security argument needs only that all three
handlers share it, not what it is; the concrete instance is `handler_runtime = 2`,
which is what the example traces below are written at. (`runtime = 0` degenerates
— `n %% 0 = n`, so the cell never returns to 0 and the handler never signals
completion. Nothing breaks, the handler simply never finishes.)

**`unit_proc : Proc Empty Unit`**

```coq
unit_proc = out tt
```

Padding for unused pool slots (indices ≥ 6).

**Interface tables and the process family.** `my_f_I` and `my_f_O` give the input
/ output interface of pool slot `n`:

| slot | process | input | output |
|---|---|---|---|
| 0 | timer-interrupt handler | `Empty` | `THandlerOutput` |
| 1 | disk-interrupt handler | `Empty` | `THandlerOutput` |
| 2 | default handler | `Empty` | `THandlerOutput` |
| 3 | scheduler | `Empty` | `Nat` |
| 4 | secret user process | `THandlerOutput` | `Opriv` |
| 5 | public user process | `Empty` | `Opub` |
| ≥6 | padding | `Empty` | `Unit` |

Only slot 4 has a non-`Empty` input: the secret user process is the one process
that consumes anything, namely the disk handler's `Notify`. Every other slot is
driven purely by being scheduled.

`Opub` and `Opriv` are parameters (`my_f_O Opub Opriv`), as are the processes in
slots 3, 4 and 5 — see below.

**The pool is built from a process *function*.** `process_pool` (section 2) is
generic in a family `f_proc : forall n, Proc (f_I n) (f_O n)`, and recurses over
slot indices — so the family must be a *total* function on `nat`, defined before
the pool can be instantiated:

```coq
slot_procs runtime p_pub p_priv p_sched n : Proc (my_f_I n) (my_f_O Opub Opriv n) =
  match n with
  | 0 | 1 | 2 => I_handler runtime
  | 3 => p_sched
  | 4 => p_priv
  | 5 => p_pub
  | _ => unit_proc
  end

my_procs = slot_procs handler_runtime low_p high_p scheduler
```

`unit_proc` exists only to make this total. The pool proper is slots `0..5`;
nothing above 5 is ever selected, and the padding branch is present because
`slot_procs` must have a value everywhere, not because the system has more
processes.

**The scheduler and the two user processes are parameters.** They are what the
mechanism is meant to protect, not part of it, so the development fixes only the
handlers and the padding. `pool`, `model_sliced` and `model_sliced_userview` all
take `p_pub`, `p_priv` and `p_sched`; `my_procs`, `my_process_pool`,
`model_sliced_concrete` and `model_sliced_userview_concrete` are the instances at
`low_p`, `high_p` and `scheduler`, and `model_immediate` is concrete throughout.

**Layout invariant.** `slot_procs` puts the public process outermost (slot 5),
then the secret process (4), then the scheduler (3), matching the pids `my_f_pid`
assigns. This ordering is load-bearing and cannot be varied: the output
projections of section 5 — `is_sch_out` and friends — are tuple patterns that
hardwire *two* user slots sitting before the scheduler slot. Adding or reordering
user slots therefore changes the state transition, and lands in the `fv_NI`
obligation. Note also that the pool is right-associated, so the two user slots are
leftmost but are not a subterm: there is no `par userspace system` to point at.

Slots 0, 1 and 2 are three *separate* handlers that share the single definition
`I_handler`. What distinguishes them is not their code but their own pending and
mask bits in the interrupt controller (section 4), and which interrupt sets them.


## 2. Process pool

The pool wires slots `0..n` into one process, each gated by a switch so that only
the slot matching the current pid is live.

**`process_pool n f_initial f_I f_O f_proj f_pid f_proc : Proc (Times cur_pid T') (times_on n f_O)`**

```coq
process_pool n ... =
  match n with
  | 0 =>
      map (fun i => (f_pid i.1 == 0, f_proj i.2 0)) id
        (swi (f_initial 0) (maybe (map id (fun o => (true, o)) (f_proc 0))))
  | n0.+1 =>
      par (map (fun i => (f_pid i.1 == n0.+1, f_proj i.2 n0.+1)) id
             (swi (f_initial n0.+1) (maybe (map id (fun o => (true, o)) (f_proc n0.+1)))))
          (process_pool n0 ...)
  end
```

Reading a single slot `k` from the inside out:

- `f_proc k` is the slot's process; `map id (fun o => (true, o))` tags each of its
  outputs with the constant bit `true`;
- `maybe` makes the slot's input optional, so the slot idles unless it is handed
  `Some` input;
- `swi (f_initial k)` gates the slot: it forwards the slot's output only while the
  switch is in phase `true`, and the constant `true` tag flips the phase closed
  after one output, so a selected slot advances by exactly one output step and
  then waits to be re-selected (every process is cooperative);
- the outer `map` computes, from the shared input `(cur_pid, T')`, the switch bit
  `f_pid cur_pid == k` (is this slot the currently selected pid?) and the slot's
  optional payload `f_proj T' k`.

`par` lays the slots side by side; `times_on n f_O` is the nested product of all
slot outputs (each wrapped in `Option`). The net effect: exactly the slot whose
index equals the current pid advances and emits; all others emit `None`.

**Concrete instantiation.**

- `cur_pid = Sum Bool Nat` — process ids, split so that the `inl` side holds
  **exactly the two secret ids** and the `inr` side everything public:

  | pid | selects slot | | pid | selects slot |
  |---|---|---|---|---|
  | `inl true` | 1, disk handler | | `inr 1` | 3, scheduler |
  | `inl false` | 2, default/NOP handler | | `inr 2` | 4, `high_p` |
  | | | | `inr 0` | 0, timer handler |
  | | | | `inr 3` | 5, `low_p` |

  Note the timer handler is `inr 0`, on the public side: it is a handler, but not a
  secret one. The split is not "handler versus not" — `is_handler_pid` is true of
  `inr 0` as well as of both `inl` ids. Its purpose is to delimit which ids are
  secret values, so that the state relation can classify them in one place
  (`eqsum privateRel publicRel`) and the proof can case-split on the tag. Section
  [`noninterference.md` §7b](noninterference.md) makes that classification precise,
  and §6 there shows where the case split is used.
- `initial_pid = inr 3` (`my_f_pid = 5`, i.e. start in the public process `low_p`)
- `my_f_initial n = (n == my_f_pid initial_pid)` (only the start slot is open)
- `f_proj i n` routes the shared payload — of type `Option THandlerOutput` — to the
  slots:

  ```coq
  f_proj i n = match n with 4 => i | _ => None end
  ```

  Only slot 4 (`high_p`) receives the payload `i` (the disk handler's output);
  every other slot receives `None`, which is the whole reason those slots can
  declare their input type as `Empty`.
- `my_process_pool = process_pool 5 my_f_initial my_f_I my_f_O (Option THandlerOutput) f_proj my_f_pid my_procs` — the six-slot pool (indices 0..5).


## 3. Stateful wrapper

The pool consumes `(cur_pid, T')` and produces a big product of slot outputs. On
its own it has no state and no way to drive itself. `reactive_system` closes it into a
single self-driving process `Proc T_in T_out'` by adding the global state and a
feedback loop. (This is the *stateful wrapper* of the construction; it is unrelated
to `model_sliced_userview`, which is a projection applied at the very end.)

**`reactive_system state state_update def p pool_input : Proc T_in T_out`**

```coq
reactive_system state state_update def p pool_input =
  map inl (inr_or_def def)
    (loop (map id snd
      (sta state_update (fun _ v => v) state
        (map pool_input inr (maybe p)))))
```

From the inside out:

- `maybe p` runs the pool, idling on `None`;
- `map pool_input inr` turns each pool result into the pool's *next* input via `pool_input`
  (which reads the global state and the current event), tagging it `inr` for the
  feedback channel;
- `sta state_update ... state` holds the global model state and advances it by
  `state_update` on every event (external input or fed-back output);
- `loop` ties the output back to the input, so the system self-drives;
- the outer `map` presents external inputs on the left, and on the way out applies
  `inr_or_def def x = if x is inr x' then x' else def` — projecting the looped
  value back out, and substituting `def` when there is no genuine external output
  yet.

In the models, `state_update` is `state_step ...` (section 5) and `pool_input`
routes the pool:

**`pool_input (v, event) : Option (cur_pid * Option THandlerOutput)`**

```coq
pool_input si = if si.2 is inr o then Some (get_cur_pid si.1, dI_out o) else None
```

On a pool output `o` it feeds back the current pid together with the disk
handler's output component (`dI_out o`) as the shared payload — this is the wire
that delivers a disk `Notify` to `high_p`.


## 4. Model state

The global state cell threaded by `reactive_system` has type

```coq
stateType = Times pids bool_state
          = ((cur_pid, prev_pid), (re_sch, (ir_count, ic)))
```

with the pieces:

| field | type | meaning |
|---|---|---|
| `cur_pid` | `Sum Bool Nat` | the pid whose slot is currently live (section 2) |
| `prev_pid` | `Option Nat` | the user pid to return to once handlers finish |
| `re_sch` | `Bool` | reschedule flag: control should go to the scheduler rather than back to the interrupted process |
| `ir_count` | `Option Nat` | the handler time-slice counter |
| `ic` | `Times I_bits (Times I_bits I_bits)` | the interrupt controller: one `I_bits` per interrupt, in order default, disk, timer |
| `I_bits` | `Times pending mask` | `pending : Bool` — an interrupt of this kind has arrived and awaits service; `mask : Bool` — service is currently blocked |

The counter reads `None` when disabled, `Some n` when `n` handler output-steps
remain in the current slice, and `Some 0` when the slice is over and control should
return to user space.

The file then defines the obvious getters/setters (`get_cur_pid`, `update_I_mask`,
...), the boolean helpers `set_masks` / `unset_masks` / `masks_set` (all-masked is
the "a handler is running, do not nest" condition), and `or_bool_state`, which
merges a handler's requested controller bits into the live state while keeping the
base time-slice untouched.

A handler is *selectable* for an interrupt kind iff it is pending and not masked
(`I_ready`), and `first_ready` picks the highest-priority ready one in the fixed
order timer > disk > default.

## 5. State transitions

`state_update` in `reactive_system` is `state_step handler_preroutine bool_coding`,
applied once per event. It is the composition of four stages (right to left):

```coq
state_step ... i  =  initiate_next(bool_coding) ∘ handler_preroutine
                     ∘ apply_schedule ∘ record_pending    (each guarded by the event i)
```

- **`record_pending`** — on an external interrupt input, set that interrupt's `pending` bit.
- **`apply_schedule`** — on a scheduler output (a bare `Nat` in the pool output), set
  `cur_pid` to the scheduled pid (`check_scheduler` / `is_sch_out`).
- **`handler_preroutine`** — model-specific; the two models differ here
  and only here plus in `bool_coding` (sections 7 and 8).
- **`initiate_next(bool_coding)`** — decide who runs next:

  ```coq
  initiate_next bc v =
    if masks_set v then v                     (* a handler is running *)
    else let v := bc v in                     (* apply time-slice logic *)
         if first_ready v is Some ir then initiate_handler ir v
         else if is_handler_pid v
              then if get_re_sch v then initiate_scheduler v
                               else initiate_prev_pid v
              else v                           (* stay in user space *)
  ```

  `initiate_handler` saves the current user pid to `prev_pid`, points `cur_pid` at
  the handler, sets all masks, and clears that interrupt's `pending` bit.

  (`initiate_next` is wrapped in `step_right` — applied only on output events, not
  on inputs — which matters for the equivalence proof.)

**Why `state_step` is a composition.** `state_step` is deliberately written as a
chain of independent stages (`record_pending`, `apply_schedule`, `handler_preroutine`,
`initiate_next`) rather than as one monolithic update, so each stage can be
reasoned about on its own. This is what makes the central proof obligation
tractable — but it also means each stage is analysed over all states, forgetting
the restricted, reachable subset the previous stage produces; `bool_coding`
(section 8) exists to re-establish the lost invariant. The proof-side story — the
state relation, the `fv_NI` obligation, the composition breakdown, and how
`bool_coding` compensates — is in [`noninterference.md`](noninterference.md).

The two models are instantiations of `state_step`, differing only in
`handler_preroutine` and `bool_coding`. Everything above is shared.


## 6. Trace vocabulary

Interfaces:

```coq
T_in                = TInterrupt        (* external input: an interrupt      *)
T_out' Opub Opriv   = (Option Opub,     (* full pool output, in slot order:  *)
                       Option Opriv,    (*   public output, syscall,         *)
                       Option Nat,      (*   scheduler pid,                  *)
                       times_on 2 THandlerOutput)  (*   three handler outputs *)
T_out Opub Opriv    = Option (Sum Opub Opriv)  (* external view: user output *)
```

`Opub` and `Opriv` — the alphabets of the public and the secret user process — are
parameters, for the same reason the processes are: nothing in the mechanism
inspects a user-slot *value*, only whether the slot produced one. `T_out'C` and
`T_outC` abbreviate the concrete instances (`TPublicOutput`, `TTypeSyscall`) used
by `model_immediate` and by the example traces.

**The `T_out'` slot map.** Every output of `model_immediate` and `model_sliced` is a
six-slot tuple, and exactly one slot is `Some` at a time. The slot order is the
*reverse* of the pool index (section 1), so reading left to right:

| # | slot | carries | constant that sets it | classified |
|---|---|---|---|---|
| 1 | `pub` | public user output (`low_p`) | `low_out x` | public |
| 2 | `sys` | `high_p`'s output — `Syscall` or `NOP` | `high_out x` | secret |
| 3 | `pid` | scheduled pid | `sch_o x` | public |
| 4 | `dfl` | default/NOP handler output | `defaultI_o x` | secret |
| 5 | `dsk` | disk handler output | `dI_o x` | secret |
| 6 | `tmr` | timer handler output | `tI_o x` | public |

The last column is the security classification each slot is given by `out_rel`,
defined in [`noninterference.md` §4](noninterference.md); the trace tables below
are read against it.

The remaining constants name the specific tuples the example traces use, so those
traces read as vocabulary rather than as nested pairs. Inputs:

| constant | is |
|---|---|
| `dI'` | the disk interrupt (the secret input) |
| `tI'` | the timer interrupt (public) |

Outputs:

| constant | is | slot |
|---|---|---|
| `out_get'` | `low_out GetRequest` | `pub` |
| `out_syscall'` / `out_nop'` | `high_out Syscall` / `high_out NOP` | `sys` |
| `sched_priv'` / `sched_pub'` | `sch_o 2` / `sch_o 3` (i.e. `high_p` / `low_p`) | `pid` |
| `nop_step'` / `nop_done'` | `defaultI_o Nothing` / `defaultI_o Notify` | `dfl` |
| `dsk_step'` / `dsk_done'` | `dI_o Nothing` / `dI_o Notify` | `dsk` |
| `tmr_step'` / `tmr_done'` | `tI_o Nothing` / `tI_o Notify` | `tmr` |

Two conventions run through these names. A **prime** marks the full pool output
(`T_out'`); the unprimed name of the same value, where one exists, is its
`model_sliced_userview` counterpart in `T_out` — so `out_get'` is a `pub` slot in a
six-tuple, and `out_get` is the single value the user view emits. And since a
handler activation is always `Nothing` then `Notify` (section 1), a `_step'`/`_done'`
pair in a trace is exactly one complete handler run.


## 7. `model_immediate`

The baseline: interrupts are handled the "normal" way, and secret interrupts leak
through scheduling.

```coq
initial_state = ((initial_pid, None), (false, (None, false_ic)))
```

Counter disabled (`None`), every controller bit clear, start in `low_p`.

```coq
immediate_preroutine o v =
  if is_I_out_done o is Some ir
  then let v := unset_masks v in
       if ir is TimerInterrupt then update_re_sch v true else v
  else v
```

A handler signals completion by emitting `Notify` (`is_I_out_done` scans the
handler-output slots for it). On completion `model_immediate` simply unmasks
everything; if it was the timer handler it also asks to reschedule.

```coq
model_immediate = reactive_system initial_state (state_step immediate_preroutine id) def
                     my_process_pool pool_input
```

(`bool_coding` is `id`: `model_immediate` does no time-slice bookkeeping.)

**Why it leaks.** Nothing here constrains *when* a handler runs. All masks start
clear, so as soon as an interrupt is serviced its handler is scheduled, and it runs
for its two output steps in place of whichever process was running. A secret disk
interrupt thus moves every subsequent public output two steps later. The handler's
own output is secret and the attacker cannot see it, but the public process's
output slot is not, and for those two steps it is empty — an output that was due
and did not arrive. That is what `model_immediate_not_NI` turns into a counterexample
(see [`noninterference.md` §5](noninterference.md)).

### The leak, in the model's own traces

Two runs of `model_immediate` are proved to be traces, `trace_immediate_no_dI'` and
`trace_immediate_with_dI'`. Written out with the section 6 vocabulary — inputs marked
`·like this·`, and a `_step'`/`_done'` pair being one complete handler run:

```text
immediate_no_dI'    Get  ·tI·  Get  [tmr run]  sch  NOP  ·tI·  NOP  [tmr run]  sch  Get
immediate_with_dI'  Get  ·dI·  Get  [dsk run]  Get  ·tI·  Get  [tmr run]  sch  Sys  ...
                          └─────┬────┘
                          the disk handler runs as soon as the interrupt is
                          serviced, between two public outputs
```

What these show is *where* a handler run may appear. In `model_immediate` it appears
wherever its interrupt happened to be serviced: the disk run lands immediately
after the disk interrupt, in the middle of the public output stream, pushing every
later public output two steps back. The handler's own slot is secret and the public
slot is not, so what an attacker observes is not the handler but its effect — two
consecutive steps on which a public output was due and nothing arrives. That is the
leak, and `model_immediate_not_NI` ([`noninterference.md` §5](noninterference.md)) turns
it into a counterexample using a trace of just two public requests.

In `model_sliced` a handler run can appear in only one place: inside the fixed time
slice, after a timer `Notify`. A secret handler run there takes the place of a
default/NOP run instead of displacing a user process. Section 9 shows that run in
full.


## 8. `model_sliced`

*The security-critical instantiation.*

`model_sliced` keeps the entire generic structure of section 5 and changes only
`handler_preroutine` and `bool_coding`, so that a secret interrupt can be serviced
without its presence showing up in the schedule. Two things change relative to
`model_immediate`:

1. **All masks start set except the timer's.** A secret handler can therefore never
   be started merely because its interrupt arrived; the only interrupt that can be
   serviced from rest is the public timer.
2. **A fixed time slice replaces "run until the handler says it is done".** The
   counter `ir_count` is loaded when the timer handler *completes* and counts down
   over output steps. What ends a handler's turn is the slice, not the handler's own
   secret output.

Both models already give every handler the same two-step runtime (section 1). What
`model_sliced` adds is that handlers may run *only* inside the slice, and that the
NOP handler fills any part of the slice no real interrupt claims — so a slice
containing a disk handler run and a slice containing only filler have the same
shape.

**Definitions** (each with its security rationale).

**`initial_state_sliced`**

```coq
initial_state_sliced = ((initial_pid, None), (false, (Some 0, mask_most)))
mask_most = ((false,true), ((false,true), (false,false)))
            (* pending=false everywhere; masks set for default and disk,
               clear for the timer *)
```

*What it does:* start with the counter at `Some 0` (slice not yet live) and every
interrupt masked except the timer. Only the timer interrupt can be serviced
initially. This interrupt is public, so affecting which process is currently
running by interrupting the current process is not leaking any information.

**`initiate_ir`**

```coq
initiate_ir runtime runs o v =
  if tI_out o is Some Notify then
    update_ir_count v (Some (time_slice runtime runs))
  else v
```

*What it does:* when the timer handler emits `Notify`, (re)load the time-slice
counter to `Some (time_slice runtime runs)`. When the timer handler has completed,
the time slice begins. The slice is `runs` complete handler executions long, so
that many can take place before it ends. At the concrete instance
(`handler_runtime = 2`, `slice_runs = 2`) that is `Some 4`.

**The slice, and the masks it drives.** Three definitions read the counter and
decide the masks. Taken together they are easier to see as one table than as three
signatures:

```coq
time_slice runtime runs = runs * runtime

handler_completed runtime c =
  match c with
  | Some n => (n != 0) && (n %% runtime == 0)   (* on a handler boundary *)
  | None   => false
  end

check_handler_completed runtime v =
  if handler_completed runtime (ir_count v) then set_tI (unset_masks v) else v

check_ir_count v =
  match ir_count v with
  | Some n.+1 => update_ir_count v (Some n)                 (* tick down *)
  | Some 0    => update_ir_count (set_otherIs (unset_tI v)) None
  | None      => v
  end
```

Because the slice is *defined* as `runs * runtime`, it always ends on a handler
boundary, and the counter is a nonzero multiple of `runtime` precisely when a
handler has just finished — which is what `handler_completed` tests. Below at the
concrete instance, where a slice of 4 is two runs of a 2-step handler:

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
  Some 0  ──▶ slice over                ──▶  disk + NOP masked, timer unmasked,
                                              counter disabled (None)
```

The two boundaries `Some 4` and `Some 2` are the nonzero multiples of `runtime`
below the slice, so they are exactly the ones `handler_completed` marks,
and at both the secret handlers are the ones left runnable — that is
`check_handler_completed`. The `Some 0` case is the mirror image and belongs to
`check_ir_count`: it closes the slice by masking the secret handlers and unmasking
the timer, so the only interrupt that can be serviced next is the public one that
starts the next slice.

**`sliced_preroutine`**

```coq
sliced_preroutine o = check_ir_count ∘ check_handler_completed ∘ initiate_ir o
```

*What it does:* `model_sliced`'s `handler_preroutine` — reload on a timer
`Notify`, apply the completion boundary, then tick the slice.

**`timeslice_live`**

```coq
timeslice_live c = (c is Some n with 0 < n)
```

*What it does:* is the slice currently counting down. Used in `bool_coding`. While
it is true, either the disk or nop handler is running, and at the completion of
either of these handlers only those two are unmasked.

**`bool_coding`**

```coq
bool_coding v =
  let b := timeslice_live (ir_count v) in
  let ic := (true, (None, ((b,~~b), ((false,~~b), (false,b))))) in
  let v := update_bool_state v (or_bool_state (bool_state v) ic) in
  update_I_mask v DefaultInterrupt (get_I_mask v DiskInterrupt)
```

*What it does:* the time-slice "coding" folded into `initiate_next`. It ORs a
controller pattern (parameterised by whether the slice is live) into the state,
then forces the default mask to equal the disk mask.

*Why it is needed.* Two facts hold of every state the model can actually reach:

```text
(i)  slice live  ⇒  NOP pending, NOP and disk unmasked, timer masked
(ii) the NOP and disk masks are always toggled together
```

Both are invariants, and neither is available to the proof. Writing `state_step` as
a composition of independent stages (section 5) buys tractability at the cost of
forgetting what the previous stage established, so each stage must be proved for
*every* pair of related states, including ones that never arise. `bool_coding` puts
the two facts back: it ORs in the controller pattern for (i), and forces the
default mask to equal the disk mask for (ii). On any reachable state both are
no-ops. Stated unconditionally, they let `initiate_next` be analysed on a state
space narrow enough for the argument to go through.

The pattern is parameterised by `timeslice_live`, which reads only `ir_count` — a
public field — so it is the same across two related executions. That is what makes
this legitimate rather than question-begging, and it is where the fact that the
slice is started by the *public* timer handler does real work.
[`noninterference.md` §7d](noninterference.md) gives the proof-side account.

```coq
model_sliced = reactive_system initial_state_sliced
                      (state_step sliced_preroutine bool_coding) def
                      my_process_pool pool_input
```

A concrete run of `model_sliced`, and what survives the `model_sliced_userview`
projection, is worked through in section 9.


## 9. `model_sliced_userview`

`model_sliced` still exposes the whole pool output (`T_out'`), including handler and
scheduler activity. The final model hides all of that, exposing only what a
user-space observer sees.

```coq
parse_output o =
  match o with
  | (Some public, _)        => Some (inl public)   (* public user output *)
  | (None, (Some prv, _))   => Some (inr prv)       (* the high syscall *)
  | _                       => None
  end
```

Project the full output down to the user-visible channel: a public output, or the
secret process's syscall, or nothing. Of the six `T_out'` slots (section 6) only two
survive — `pub` (re-tagged `inl`) and `sys` (re-tagged `inr`); every other slot, and
any all-`None` tuple, projects to `None`.

```coq
model_sliced_userview runtime runs p_pub p_priv p_sched =
  map id parse_output (model_sliced runtime runs p_pub p_priv p_sched)
    : Proc T_in (T_out Opub Opriv)
```

```coq
final_out_rel Opub Opriv = eqmaybe_false (eqsum (publicRel Opub) (privateRel Opriv))
```

The output relation used by the top theorem: the public component is compared
exactly, the syscall component is treated as secret.

`model_sliced_userview_NI` proves `NI in_rel final_out_rel model_sliced_userview` — the
payoff: with `model_sliced`'s fixed-length, masked handling, the presence of a
secret (disk) interrupt is invisible in the user-space output. The proof itself is
documented in [`noninterference.md`](noninterference.md).

### Worked example: the projection in action

Below is the concrete run `sliced_with_dI'` (a disk interrupt arrives at step 2),
read top-to-bottom. The left block is `model_sliced`'s full six-slot tuple, in the
§6 slot order; to the right of the double bar is the single value
`model_sliced_userview` emits for that step. Legend: `·` = `None`, `Nth` = `Nothing`,
`Nfy` = `Notify`, `hi`/`lo` = scheduler pids.

```text
step  in   pub   sys   pid   dfl   dsk   tmr   ║  wrapped
───────────────────────────────────────────────╫──────────
  1         Get    ·     ·     ·     ·     ·    ║  Get
  2    dI    (disk interrupt — secret input)    ║  dI
  3         Get    ·     ·     ·     ·     ·    ║  Get
  4         Get    ·     ·     ·     ·     ·    ║  Get
  5    tI    (timer interrupt)                  ║  tI
  6         Get    ·     ·     ·     ·     ·    ║  Get
  7          ·     ·     ·     ·     ·    Nth   ║  ·
  8          ·     ·     ·     ·     ·    Nfy   ║  ·
  9          ·     ·     ·     ·    Nth    ·    ║  ·
 10          ·     ·     ·     ·    Nfy    ·    ║  ·
 11          ·     ·     ·    Nth    ·     ·    ║  ·
 12          ·     ·     ·    Nfy    ·     ·    ║  ·
 13          ·     ·    hi     ·     ·     ·    ║  ·
 14          ·    Sys    ·     ·     ·     ·    ║  Sys
 15    tI    (timer interrupt)                  ║  tI
 16          ·    NOP    ·     ·     ·     ·    ║  NOP
 17          ·     ·     ·     ·     ·    Nth   ║  ·
 18          ·     ·     ·     ·     ·    Nfy   ║  ·
 19          ·     ·     ·    Nth    ·     ·    ║  ·
 20          ·     ·     ·    Nfy    ·     ·    ║  ·
 21          ·     ·     ·    Nth    ·     ·    ║  ·
 22          ·     ·     ·    Nfy    ·     ·    ║  ·
 23          ·     ·    lo     ·     ·     ·    ║  ·
 24         Get    ·     ·     ·     ·     ·    ║  Get
```

Two things stand out.

**The projection erases most of the run.** Only the `pub` and `sys` slots survive.
The handler steps (7–12, 17–22) and the scheduled pids (13, 23) fall in slots
`parse_output` discards, so the wrapped column is uniformly `·` across them.

**The secret interrupt does not move the public schedule.** The disk handler does
run — steps 9–10 — but inside the time slice, in place of a default/NOP run. Each
slice is six hidden steps: the timer handler, then two further handler runs. That
holds of both slices here and of `sliced_no_dI'`: with a disk interrupt the pair at
steps 9–10 is `dsk`, without one it is `dfl`. The public skeleton around the slice —
`tI`, the scheduled pid, the resumed `Get` — is unchanged. The only other trace of
the interrupt is step 14, `Sys` instead of `NOP`, which is the secret user process
reacting to the handler's notification. Both the disk input and the syscall output
are classified secret ([`noninterference.md` §4](noninterference.md)), so at the
attacker's level the two runs are indistinguishable — which is what
`model_sliced_userview_NI` proves in general.


## Where to go next

That is the whole construction. What it does *not* say is why any of it is secure:
nothing above defines what an attacker can observe, and the claims made in passing
— that a slot is public, that the pid split matters, that a handler run must be
indistinguishable from filler — are stated but not made precise.

That is the subject of [`noninterference.md`](noninterference.md): the security
relation carried by each interface, the counterexample for `model_immediate`, how the
generic theorems compose to prove `model_sliced`, and the one substantial obligation
(`fv_NI`) that the compositional structure of `state_step` and `bool_coding` exist
to make tractable.

## Appendix: asides and alternatives

None of this is needed to follow the models; it records design questions a reader
may reasonably ask.

### Why the slice counter lives in the interrupt controller, not in the handler
 In earlier versions the "steps to complete"
counter lived inside the handler process. It has been moved into the global state,
as part of `ic` (the interrupt controller). This mirrors how real hardware would
enforce a time slice, and the following argues it is implementable rather than a
modelling artefact:

- **Hardware level — the interrupt controller.** For a guaranteed, hard-real-time
  bound that software cannot bypass or delay, the counter belongs in the interrupt
  controller (ARM GIC, RISC-V PLIC/CLIC, x86 APIC) or a small custom "interrupt
  throttler" block, held in the controller's MMIO register space. When an
  interrupt is dispatched to the CPU a hardware timer is loaded with the
  time-slice value. It decrements while the CPU executes in interrupt context
  (which the hardware tracks via the interrupt-acknowledge and End-of-Interrupt
  signals). If the counter reaches zero before EOI, the hardware raises an
  internal mask signal that stops the distributor / CPU interface from forwarding
  further interrupts to the processor.
- **Model correspondence.** Each interrupt kind registers a `pending` bit when its
  interrupt is input to the system; the `mask` decides whether a pending interrupt
  is actually activated. The check happens during an *output* step, updating
  `cur_pid` to the appropriate handler. Handlers are prioritised (timer before
  disk). While a handler runs all masks are set, so no interrupt nests. When a
  handler completes we unmask and re-check for another ready handler — this is the
  controller being consulted at the end of a CPU clock cycle. If none is ready we
  check the reschedule flag: if set, control passes to the scheduler; if clear,
  `cur_pid` is restored to `prev_pid`, the user process that was interrupted.

### Could the timer be left unmasked during the slice?

It would be possible to unmask timer interrupts during the time slice, but a timer
interrupt arriving mid-slice would reset the slice — possibly while the disk or NOP
handler was still mid-execution — and `handler_completed` would then no longer be
in step with the actual completion of handlers. The model takes the simpler of the
two approaches and keeps the timer masked until the slice ends.
