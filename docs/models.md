# NonInterference: model documentation

*Prose companion to [`theories/models.v`](../theories/models.v).*

There is one generic model. Instantiating it one way gives a design that leaks a
secret interrupt through scheduling; instantiating it another way gives one that
does not. This document defines the generic model, then the two instantiations,
then one concrete system to run them on. Names are those of the source, and every
process is given with the `@` and `Ty` annotations erased (section 0 says why the
source needs them); no proof code is reproduced.

> Why one instantiation is non-interfering and the other is not belongs to
> [`noninterference.md`](noninterference.md), the companion to
> [`theories/noninterference.v`](../theories/noninterference.v). That document gives
> the security equivalences, the characterised equivalence each input and output type
> carries, and the central proof obligation.

| Model | Type | What it is |
|---|---|---|
| `model_immediate` | `Proc T_in (T_out Opub Opriv)` | Interrupts handled the ordinary way: a handler runs as soon as its interrupt is serviced. Secret interrupts leak through scheduling. |
| `model_sliced` | `Proc T_in (T_out Opub Opriv)` | Interrupt masking controlled so that a secret interrupt can be serviced without disturbing the public schedule. Like `model_immediate`, its output exposes every pool slot. |
| `model_sliced_userview` | `Proc T_in (T_out_userview Opub Opriv)` | `model_sliced` behind a projection of the pool's output that erases every slot but the two user space processes. This is the model the headline theorem is about. |

## Contents

**Part I: the generic model.**
[0. Preliminaries](#0-preliminaries-the-process-algebra) ·
[1. The generic model](#1-the-generic-model) ·
[2. Interrupt handler and slot map](#2-interrupt-handler-and-slot-map) ·
[3. Process pool](#3-process-pool) ·
[4. Stateful wrapper](#4-stateful-wrapper) ·
[5. Model state](#5-model-state) ·
[6. State transitions](#6-state-transitions) ·
[7. The generic model, and its three parameters](#7-the-generic-model-and-its-three-parameters)

**Part II: the two designs.**
[8. Side by side](#8-the-two-designs-side-by-side) ·
[9. `model_sliced_userview`](#9-model_sliced_userview)

**Part III: one concrete system.**
[10. A concrete system](#10-a-concrete-system) ·
[11. Adequacy: the example traces](#11-adequacy-the-example-traces)


## 0. Preliminaries: the process algebra

Everything below is built from a small process calculus (defined in
[`theories/definitions.v`](../theories/definitions.v)). The calculus and its
non-interference theorems are due to Rafnsson et al., *Timing-Sensitive
Noninterference through Composition* ([POST
2017](https://users.ece.cmu.edu/~lbauer/papers/2017/post2017-compose-time.pdf));
mechanising them is part of the contribution of this development. The mechanisation
departs from the paper in four respects, each proved adequate in
[`adequacy.v`](../theories/adequacy.v) and set out one at a time in
[`departures.md`](departures.md). Two are local to the security equivalences and
are taken up in
[`noninterference.md`](noninterference.md): a **characterised equivalence** replaces
the paper's L-equivalences (§1), and obliviousness asks that a process stay in one
indistinguishability class rather than in the distinguished one (§6a).

One of the other two shows up everywhere and is worth carrying while reading:
**the paper's streams of labels are finite lists
here, and definitions it gives coinductively are given inductively**. A trace is the
list of labels along zero or more reductions, and `oblivious`, for instance, is
stated over the traces a process admits rather than over an infinite stream. The
proofs are substantially simpler for it, since they never have to construct
streams. Nothing is lost, and that is a theorem rather than an assumption:
`NI_SNI` states `Trace` and `NI` over streams and proves the two readings accept
the same processes ([`departures.md` §3](departures.md)).

A process has type `Proc I O`, where `I` and `O` are its input and output types.

A process moves in one of two ways:

```text
   p ──i──▶ p'     p receives the input i
   p ──o──▶ p'     p emits the output o
```

in any order; nothing forces them to alternate. A **trace** is the sequence of
values along one such run, each marked as received or emitted, and it is all
non-interference looks at. Precise definitions are in
[`noninterference.md` §1](noninterference.md).

Throughout, *emit* means an output step and *receive* an input step.

Both kinds of step are **total** and **deterministic**. Whatever state a process is
in, it can receive any input of its type and it can emit, and in each case there is
exactly one way to do so: the successor is determined, and on an output step so is
the value emitted. The two relations are therefore functions, and
[`adequacy.v`](../theories/adequacy.v) gives them as the functions `stepI` and
`stepO` and proves the relations agree with them. Nothing in the models relies on
this, and the reader can take the arrows above at face value. It matters once
traces are compared with streams, where totality is what lets a finite run be
continued and determinism is what makes the finite runs of one stream fit together
into a single infinite one.

There are seven constructors, described here by what each does on an input step and
on an output step:

- **`out o`** is the constant process. It receives any value and is unchanged; it
  emits the fixed `o` and is unchanged.
- **`map f g p`** rewires `p` on both sides. Receiving `i`, it hands `p` the
  value `f i`. Emitting, it lets `p` emit some `o` and emits `g o` in its place.
  (`Proc I' O → Proc I O'`)
- **`sta f g v p`** gives `p` a state cell holding `v`, and *exposes* that cell in
  what it emits. Receiving `i`, the cell becomes `f i v` and `p` receives the pair
  `(f i v, i)`. Emitting, `p` emits some `o`, the cell becomes `g o v`, and the whole
  process emits the pair `(g o v, o)`, the new state alongside `p`'s value.
- **`swi b p`** is a one-bit "switch" in phase `b`, wrapping a `p` that emits values
  tagged with a Bool. Receiving `(b', i)`, the phase flips to `xor b b'` and `p`
  receives `i`. Emitting in phase `false`, it emits `None` and `p` does not step at
  all; emitting in phase `true`, `p` emits a tagged `(c, o)`, the switch emits
  `Some o` and the phase becomes `xor true c`. `swi` is how a pool slot is gated on /
  off (section 3).
- **`par p1 p2`**: receiving `i`, both `p1` and `p2` receive it. Emitting, both emit,
  and `par` emits the pair of their two values.
- **`loop p`** is feedback. Receiving `i`, `p` receives it. Emitting is two steps of
  `p`: `p` emits some `o`, that same `o` is immediately fed back to `p` as an input
  step, and `loop p` emits `o`. (`Proc I I → Proc I I`)
- **`maybe p`** makes the input optional. Receiving `None`, `p` does not step;
  receiving `Some i`, `p` receives `i`. Emitting passes straight through: `p` emits
  `o` and so does `maybe p`. (`Proc I O → Proc (Option I) O`)

> **Why `I` and `O` are drawn from `Ty`.** In the mechanisation they range over an
> inductive `Ty` (`Nat`, `Bool`, `Unit`, `Times`, `Option`, `Sum`, ...) rather than
> over Coq's `Set`, with `[t]` interpreting a `t : Ty` as the `Set` it encodes.
> Going through `Ty` rather than through `Set` directly is what makes reductions
> invertible. The negative result needs that, since refuting non-interference means
> showing a trace is *not* accepted. The cost is the explicit annotations in the
> source, which this document strips away.

The whole development ends by proving `NI` of `model_sliced_userview`. What `Trace`
and `NI` mean, and the equivalences they are indexed by, are in
[`noninterference.md` §1](noninterference.md).


# Part I: the generic model

## 1. The generic model

```coq
model runtime init handler_preroutine restore_invariant p_pub p_priv p_sched =
  reactive_system init (state_step handler_preroutine restore_invariant) def
    (pool runtime p_pub p_priv p_sched) pool_input
      : Proc T_in (T_out Opub Opriv)
```

An operating system as a single process. At its centre sits a **process pool**
(section 3): three interrupt handlers, a scheduler, two user processes. A **stateful
wrapper** (section 4) closes the pool into a self-driving whole, threading the global
state and deciding on every step whose turn it is (sections 5 and 6).

It receives interrupts, and on each output step emits one tuple holding every slot's
value. Nothing in it is committed to a security design. That is entirely the job of
the three parameters `init`, `handler_preroutine` and `restore_invariant`. Section 7
sets them out, and Part II fixes them in two different ways: once so that a secret
interrupt leaks, once so that it does not.

Sections 2 to 6 define each piece, bottom-up.


## 2. Interrupt handler and slot map

The only leaf process the generic model itself fixes is the interrupt handler. The
scheduler and the two user processes are parameters, supplied in section 10.

**`ir_handler runtime : Proc Empty THandlerOutput`**

```coq
ir_handler runtime =
  map id (fun o => if o.1 == 0 then Notify else Nothing)
    (sta (fun _ v => v) (fun _ v => v.+1 %% runtime) 0 (out tt))
```

Its state cell counts modulo `runtime` and the emitted value is read off the
*updated* cell: `Notify` when it is 0, `Nothing` otherwise. So each activation emits
`runtime - 1` `Nothing`s and then a `Notify` signalling completion, a fixed number
of output steps. Its input type is `Empty`: a handler is driven entirely by the
interrupt controller and never consumes input.

`runtime` is a parameter. The security argument needs only that all three handlers
share it, so that a secret handler's run is exactly as long as the filler run it
replaces. (`runtime = 0` degenerates: `n %% 0 = n`, so the cell never returns to 0
and the handler never signals completion. Nothing breaks; the handler simply never
finishes.)

**The slot map.** `slot_I` and `slot_O` give the input and output types of pool slot
`n`, and `slot_procs` gives its process:

| slot | process | input | output |
|---|---|---|---|
| 0 | timer-interrupt handler | `Empty` | `THandlerOutput` |
| 1 | disk-interrupt handler | `Empty` | `THandlerOutput` |
| 2 | default handler | `Empty` | `THandlerOutput` |
| 3 | scheduler (parameter `p_sched`) | `Empty` | `Nat` |
| 4 | private user process (`p_priv`) | `THandlerOutput` | `Opriv` |
| 5 | public user process (`p_pub`) | `Empty` | `Opub` |
| ≥6 | padding, `unit_proc = out tt` | `Empty` | `Unit` |

```coq
slot_procs runtime p_pub p_priv p_sched n =
  match n with
  | 0 | 1 | 2 => ir_handler runtime
  | 3 => p_sched  | 4 => p_priv  | 5 => p_pub
  | _ => unit_proc
  end
```

`Opub` and `Opriv`, the alphabets the two user processes emit over, are parameters
for the same reason the processes are: nothing in the generic model inspects a
user-slot *value*, only whether the slot produced one (section 6).

Slots 0, 1 and 2 are three *separate* handlers reusing one definition; what
distinguishes them is their own pending and mask bits in the interrupt controller
(section 5), and which interrupt sets them. Only slot 4 has a non-`Empty` input:
the private user process is the one process that consumes anything, namely the disk
handler's `Notify`. `process_pool` recurses over slot indices, so the family must be
total on `nat`; `unit_proc` exists only for that, and nothing above 5 is ever
selected.


## 3. Process pool

`process_pool` is a generic procedure for building a pool: it wires slots `0..n` into
one process, each gated by a switch so that only the slot matching the current pid is
live. Both models are built from a single instantiation of it.

```coq
process_pool cur_pid n f_initial f_I f_O T' f_proj f_pid f_proc =
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

Read a single slot `k` from the inside out. `f_proc k` is the slot's process, and
`map id (fun o => (true, o))` tags everything it emits with the constant bit `true`.
`maybe` makes the input optional, so on an input step the slot's process steps only
if handed `Some`. `swi (f_initial k)` gates it, emitting the slot's value only in
phase `true`, and the constant `true` tag closes the phase again. A selected slot
therefore takes exactly one output step and then waits to be re-selected, every
process being cooperative. The outer `map` builds the switch's input, the pair of the
bit `f_pid cur_pid == k` and the slot's payload `f_proj T' k`.

`par` lays the slots side by side and `times_on n f_O` is the nested product of all
slot outputs, each wrapped in `Option`. The net effect on an output step: the slot
whose index equals the current pid emits its own value, and every other slot emits
`None`.

**Instantiation.** What has to stay open is the handler runtime, the scheduler and
the two userspace processes, and all four enter through one argument only, `f_proc`.
Everything else can be fixed now:

```coq
pool runtime p_pub p_priv p_sched =
  process_pool cur_pid n f_initial f_I f_O T' f_proj f_pid f_proc
    : Proc (Times cur_pid T') (T_out Opub Opriv)
```

The alphabets `Opub` and `Opriv` are `pool`'s own parameters, fixed by whichever
`p_pub` and `p_priv` it is given. The nine arguments are these.

**Pids, size, and the processes.**

```coq
cur_pid   = Sum Bool Nat           (* pids, split private / public *)
n         = 5                      (* six slots, 0..5 *)
T'        = Option THandlerOutput  (* one handler output, broadcast with the pid *)
f_proc    = slot_procs runtime p_pub p_priv p_sched

f_pid     = fun pid => match pid with
                       | inl true  => 1     (* disk handler    *)
                       | inl false => 2     (* default handler *)
                       | inr 0     => 0     (* timer handler   *)
                       | inr 1     => 3     (* scheduler       *)
                       | inr 2     => 4     (* private user    *)
                       | inr 3     => 5     (* public user     *)
                       | inr n     => n
                       end

f_initial = fun n => n == 5        (* slot 5 alone starts open *)
```

The `cur_pid` split is the one choice here worth a second look: the `inl` side holds
**exactly the two private pids**, the disk and default handlers, and the `inr` side
everything public, including the timer handler, which is `inr 0`. It is a handler,
but not a private one, so the split is not "handler versus not". Drawing it on this
line is what lets the state equivalence classify a whole pid in one place, as
`eqsum private_equiv public_equiv`, with the proof case-splitting on the tag
([`noninterference.md` §7b](noninterference.md)).

**The slot types**, tabulated in section 2. `f_O` is parameterised by the two
alphabets, and this is where `Opub` and `Opriv` enter the pool's output type:

```coq
f_I            = fun n => match n with
                          | 4 => THandlerOutput  (* only slot 4 takes an input *)
                          | _ => Empty
                          end

f_O Opub Opriv = fun n => match n with
                          | 0 | 1 | 2 => THandlerOutput
                          | 3         => Nat
                          | 4         => Opriv
                          | 5         => Opub
                          | _         => Unit
                          end
```

**Routing the payload.**

```coq
f_proj = fun i n => match n with
                    | 4 => i            (* only slot 4 receives it *)
                    | _ => None
                    end
```

This is why every other slot can declare its input `Empty`: `f_proj` hands them
`None`, on which `maybe` leaves the slot's process unstepped. It has to be a `match`
rather than the `if n == 4 then i else None` it looks like. The result type
`[Option (f_I n)]` varies with `n`, and only in the `4` branch is it
`Option THandlerOutput`. It typechecks as a dependent pattern match.


## 4. Stateful wrapper

The pool receives a `(cur_pid, T')` pair and emits a product of slot values. On its own
it has no state and no way to drive itself. `reactive_system` closes it into a single
self-driving `Proc T_in T_out` by adding the global state and a feedback loop.

```coq
reactive_system state state_update def p pool_input =
  map inl (inr_or_def def)
    (loop (map id snd
      (sta state_update (fun _ v => v) state
        (map pool_input inr (maybe p)))))
```

From the inside out: `maybe p` runs the pool, idling on `None`. `map pool_input inr`
rewires it at both ends: on an input step `pool_input` builds the pool's input, and
on an output step `inr` tags the pool's output for the feedback channel.
`sta state_update ... state` holds the global state and advances it on every event,
external input or fed-back output. `loop` ties output back to input. The outer `map`
presents external inputs on the left, and on the way out applies
`inr_or_def def x = if x is inr x' then x' else def`. That substitutes `def`, the
all-`None` tuple, when there is no genuine external output yet.

`state_update` is `state_step ...` (section 6). `pool_input` decides, from the state
and the event that just occurred, whether the pool steps at all and on what:

```coq
pool_input (v, event) = if event is inr o then Some (get_cur_pid v, dI_out o) else None
```

Its result is the *optional* input of `maybe p`, so the two branches mean:

- **`event = inl i`, an external interrupt** → `None`, so the pool does not step. An
  arriving interrupt advances no process; it is only recorded in the state, by
  `set_pending` (section 6). That it does *nothing else* is a security
  requirement: an interrupt the observer may not see must not visibly move the
  state, which leaves setting a single private bit as the only thing the input step
  can afford to do. See [`noninterference.md` §7a](noninterference.md).
- **`event = inr o`, a fed-back pool output** → `Some (pid, payload)`. The `pid` is
  `get_cur_pid v`, which selects the slot that runs next. This is how the state's
  scheduling decision reaches the pool. The `payload` is `dI_out o`, the disk
  handler's slot from the output just produced, which `f_proj` (section 3) delivers
  to slot 4 alone. That is the wire carrying a disk `Notify` to the private user
  process.


## 5. Model state

The global state cell threaded by `reactive_system` has type

```coq
state_type = ((cur_pid, prev_pid), (re_sched, (ir_count, ic)))
```

| field | type | meaning |
|---|---|---|
| `cur_pid` | `Sum Bool Nat` | the pid whose slot is currently live (section 3) |
| `prev_pid` | `Option Nat` | the user pid to return to once handlers finish |
| `re_sched` | `Bool` | reschedule flag: control should go to the scheduler rather than back to the interrupted process |
| `ir_count` | `Option Nat` | the handler time-slice counter: `None` when disabled, `Some n` when `n` handler output-steps remain, `Some 0` when the slice is over |
| `ic` | `Times ir_bits (Times ir_bits ir_bits)` | the interrupt controller: one `ir_bits` per interrupt, in order default, disk, timer |
| `ir_bits` | `Times pending mask` | `pending`: an interrupt of this kind has arrived and awaits service; `mask`: service is currently blocked |

A handler is *selectable* for an interrupt kind iff it is pending and not masked
(`ir_ready`). `first_ready` picks the highest-priority ready one, in the fixed order
timer > disk > default.


## 6. State transitions

The `state_update` threaded by `reactive_system` runs once per event, and an event
is either an interrupt arriving or a pool output. `step_sum f g` is the update that
runs `f` on the first and `g` on the second, and the transition is one of these:

```coq
step_sum f g (inl i) = f i
step_sum f g (inr o) = g o

state_step handler_preroutine restore_invariant =
  step_sum set_pending
           (initiate_next(restore_invariant) ∘ handler_preroutine ∘ check_scheduler)
```

- **`set_pending`**: on an arriving interrupt, set that interrupt's `pending` bit.
  This is the whole of the input summand; that it does nothing else is a security
  requirement, argued in [`noninterference.md` §7a](noninterference.md).
- **`check_scheduler`**: on a scheduler output, set `cur_pid` to the scheduled pid.
  It reads that output with `is_sched_out`, which matches `(None, (None, (Some n, _)))`,
  so the two user slots are checked for `None`-ness and nothing more. No stage
  reads a user-slot *value*, which is why the state transition is independent of what
  userspace does.
- **`handler_preroutine`** is a parameter; see section 7.
- **`initiate_next(restore_invariant)`** decides who runs next:

  ```coq
  initiate_next bc v =
    if masks_set v then v                     (* a handler is running *)
    else let v := bc v in                     (* apply bc *)
         if first_ready v is Some ir then initiate_handler ir v
         else if is_handler_pid v             (* did handler just finish? *)
              then if get_re_sched v then initiate_scheduler v
                                   else initiate_prev_pid v
              else v                           (* stay in user space *)
  ```

  `initiate_handler` saves the current user pid to `prev_pid`, points `cur_pid` at
  the handler, sets all masks, and clears that interrupt's `pending` bit. Sitting in
  the output summand, it runs only on output events.

Why the output summand is a composition rather than one update, and what that
costs, is in [`noninterference.md` §7c](noninterference.md).


## 7. The generic model, and its three parameters

That completes it:

```coq
model runtime init handler_preroutine restore_invariant p_pub p_priv p_sched =
  reactive_system init (state_step handler_preroutine restore_invariant) def
    (pool runtime p_pub p_priv p_sched) pool_input
```

The pool, the state layout, `set_pending`, `check_scheduler` and `initiate_next`
stay fixed for both the interfering and the non-interfering model. What is left free
is a triple, and each part of it is a distinct point of control over *when a handler
is allowed to run*:

- **`init : [state_type]`** is the state the model starts in. Because a handler is
  serviceable exactly when it is pending and unmasked, the initial masks decide which
  interrupts can be serviced before anything at all has happened. It also decides
  whether the time-slice counter is enabled (`Some _`) or switched off (`None`).

- **`handler_preroutine : [T_out] -> [state_type] -> [state_type]`** runs on each
  pool *output*, immediately before `initiate_next`. It is the only place a design
  sees a handler announce completion, and so the only place it can reopen masks. It
  therefore decides **when the next handler becomes eligible**: the difference
  between reopening as soon as a handler says it is done, and reopening only at a
  fixed boundary.

- **`restore_invariant : [state_type] -> [state_type]`** is consulted by
  `initiate_next`, after the "is a handler already running" test and before
  `first_ready` picks the next one. It is the design's last chance to constrain the
  state that the choice is made from. Its real use is re-imposing an invariant that
  the compositional proof has forgotten, so that the choice comes out the same in
  two related executions
  ([`noninterference.md` §7d](noninterference.md)).

Between them: `init` says what is runnable at rest, `handler_preroutine` says when
that changes, and `restore_invariant` says what must hold when the choice is made.


# Part II: the two designs

## 8. The two designs, side by side

Both are `model` at a different triple, and that difference is the whole security
story.

| | `model_immediate` | `model_sliced` |
|---|---|---|
| **`init`** | all masks clear; counter `None` (disabled) | all masks set except the timer's; counter `Some 0` |
| **`handler_preroutine`** | `immediate_preroutine`: on a handler's `Notify`, unmask everything; if it was the timer, ask to reschedule | `sliced_preroutine`: reload the slice on a timer `Notify`, unmask at fixed boundaries, tick the slice |
| **`restore_invariant`** | `id` (no bookkeeping) | restore the time-slice invariant: force the default mask to equal the disk mask |
| **When a handler stops** | when it emits its **secret** `Notify` (*secret-driven*) | at a fixed **public** time-slice boundary (*slice-driven*) |
| **What mask changes track** | secret handler behaviour | public slice boundaries |
| **Non-interfering?** | **No** (`model_immediate_not_NI`) | **Yes** (`model_sliced_NI`, for any non-interfering userspace) |
| **Why** | a handler runs as soon as its interrupt is serviced, so a secret interrupt displaces the scheduled process and the gap is visible | handlers run only within the public slice, replacing NOP filler, so the schedule is unchanged |

Handlers must all run for the same length of time, or the schedule would again
depend on which interrupt arrived. The three handler slots therefore reuse one
`ir_handler runtime` (section 2), and the slice is `runs * runtime`, where `runs` is
the number of handler executions that occur in one time slice. A real system would
reach a fixed length by padding.

### 8a. `model_immediate`

The baseline, interrupts handled the ordinary way. It is `model` at the triple
`(initial_state_immediate, immediate_preroutine, id)`:

```coq
model_immediate runtime p_pub p_priv p_sched =
  model runtime initial_state_immediate immediate_preroutine id p_pub p_priv p_sched
```

**The initial state** disables the slice counter and leaves every controller bit
clear, so from rest every interrupt is serviceable:

```coq
initial_state_immediate = ((initial_pid, None), (false, (None, false_ic)))
```

**The handler preroutine** reacts to a handler finishing, which a handler announces
by emitting `Notify`; `is_ir_out_done` scans the three handler slots for one. The
response is to unmask everything, and if it was the timer handler, also to ask for a
reschedule:

```coq
immediate_preroutine o v =
  if is_ir_out_done o is Some ir
  then let v := unset_masks v in
       if ir is TimerInterrupt then update_re_sched v true else v
  else v
```

**`restore_invariant` is `id`.** There is no time-slice bookkeeping to do, and so no
invariant to restore.

**Why it leaks.** Nothing constrains *when* a handler runs. Since all masks are
clear, an interrupt is serviced as soon as it arrives. Its handler then runs for its
full `runtime` steps in place of whichever process was running, pushing every later
public output back by that much. `model_immediate_not_NI` turns that into a
counterexample
([`noninterference.md` §5](noninterference.md)); section 11 shows it in the model's
own traces.

### 8b. `model_sliced`

The fixed design, `model` at the triple `(initial_state_sliced,
sliced_preroutine runtime runs, restore_invariant)`:

```coq
model_sliced runtime runs p_pub p_priv p_sched =
  model runtime initial_state_sliced (sliced_preroutine runtime runs) restore_invariant
    p_pub p_priv p_sched
```

**The initial state** starts the counter at `Some 0`, so no slice is live, and masks
every interrupt but the timer:

```coq
mask_most = ((false,true), ((false,true), (false,false)))
            (* pending false everywhere; masks set for default and disk,
               clear for the timer *)
initial_state_sliced = ((initial_pid, None), (false, (Some 0, mask_most)))
```

**The handler preroutine** is a composition of three
stages:

```coq
sliced_preroutine o = check_ir_count ∘ check_handler_completed ∘ initiate_ir o
```

Read right to left: `initiate_ir` opens a slice, `check_handler_completed` reopens
the masks at a boundary inside it, and `check_ir_count` ticks the slice and closes
it. Taking them in that order:

*`initiate_ir` opens a slice.* When the timer handler completes, it loads the counter
to `time_slice runtime runs`. The slice is `runs` complete handler executions long,
so that many can take place before it ends:

```coq
time_slice runtime runs = runs * runtime
initiate_ir runtime runs o v =
  if tI_out o is Some Notify then update_ir_count v (Some (time_slice runtime runs))
  else v
```

*`check_handler_completed` reopens the masks at a boundary.* Because the slice is
*defined* as `runs * runtime`, it always ends on a handler boundary, and the counter
is a nonzero multiple of `runtime` precisely when a handler has just finished, which
is what `handler_completed` computes.

```coq
handler_completed runtime c =
  match c with
  | Some n => (n != 0) && (n %% runtime == 0)   (* on a handler boundary *)
  | None   => false
  end

check_handler_completed runtime v =
  if handler_completed runtime (ir_count v) then set_tI (unset_masks v) else v
```

*`check_ir_count` ticks, and closes.* Its `Some 0` case is the mirror image of
`check_handler_completed`: it closes the slice by masking the secret handlers and
unmasking the timer, so the only interrupt serviceable next is the public one that
starts the next slice.

```coq
check_ir_count v =
  match ir_count v with
  | Some n.+1 => update_ir_count v (Some n)                 (* tick down *)
  | Some 0    => update_ir_count (set_otherIs (unset_tI v)) None
  | None      => v
  end
```

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
are the ones left runnable.

**`restore_invariant`** sets the interrupt controller's flags from whether the
slice is live, ORing them into the state, and then forces the default mask to equal
the disk mask:

```coq
timeslice_live c = (c is Some (S n))

restore_invariant v =
  let b := timeslice_live (ir_count v) in
  let ic := (true, (None, ((b,~~b), ((false,~~b), (false,b))))) in
  let v := update_bool_state v (or_bool_state (bool_state v) ic) in
  update_ir_mask v DefaultInterrupt (get_ir_mask v DiskInterrupt)
```

*Why it is needed.* Two facts hold of every state the model can actually reach:

```text
(i)  slice live  ⇒  NOP pending, NOP and disk unmasked, timer masked
(ii) the NOP and disk masks are always toggled together
```

Both are invariants, and neither is available to the proof. Writing `state_step` as a
composition of independent stages (section 6) buys tractability at the cost of
forgetting what the previous stage established. See
[`noninterference.md` §7d](noninterference.md) for details.

**Why it does not leak.** A handler can now run only inside a slice, every handler
runs for the same `runtime` steps, and the default/NOP handler fills any part of a
slice no real interrupt claims. A secret handler run therefore takes the place of a
NOP run rather than displacing a user process: a slice containing a disk run has the
same shape as one containing only filler, and the public schedule around it is
unchanged. `model_sliced_NI` proves this
([`noninterference.md` §6](noninterference.md)); section 11 shows it in the model's
own traces.


## 9. `model_sliced_userview`

`model_sliced` still exposes the whole pool output, including handler and scheduler
activity. The final model erases from that output every slot but the two user space
processes.

```coq
parse_output o =
  match o with
  | (Some public, _)      => Some (inl public)   (* public user output *)
  | (None, (Some prv, _)) => Some (inr prv)      (* the secret syscall *)
  | _                     => None
  end

model_sliced_userview runtime runs p_pub p_priv p_sched =
  map id parse_output (model_sliced runtime runs p_pub p_priv p_sched)
    : Proc T_in (T_out_userview Opub Opriv)
```

Of the six output slots only two survive, the public one re-tagged `inl` and the
secret one `inr`. Every other slot, and any all-`None` tuple, projects to `None`.

# Part III: one concrete system

## 10. A concrete system

Nothing in Parts I and II names a user process, a scheduler, a handler length or a
slice size. This section supplies one of each, so both designs can be run.

```coq
p_pub_concrete     = out GetRequest                                    (* public user process *)
p_priv_concrete    = alternate Syscall NOP tt (fun i => i == Notify)   (* private user process *)
scheduler = map id (fun o => o.1 + 2)
              (sta (fun _ v => v) (fun _ v => v.+1 %% 2) 1 (out tt))

handler_runtime = 2      (* each handler runs for two output steps *)
slice_runs      = 2      (* a slice is two complete handler runs, so four steps *)
```

`p_pub_concrete` does nothing but repeatedly issue the public request `GetRequest`.

`p_priv_concrete` issues a `Syscall` in any cycle where it received a `Notify`, and a
harmless `NOP` otherwise. That `Notify` is the disk handler telling it a disk event
occurred, over the wire of section 4. Which of the two it emits is secret-dependent,
but that is not itself the leak: both are classified secret, so the attacker cannot
tell them apart
([`noninterference.md` §4](noninterference.md)). What must not leak is the
*scheduling*. It is built from a reusable two-phase process,

```coq
alternate x y z pred =
  map inl (fun o => if o is inr (true, _) then x else y)
    (loop (map id inr
      (sta (fun i v => if i is inl i' then v || pred i' else false)
           (fun o v => v) false (out z))))
```

which emits `x` when it has received a `pred`-matching value since it last emitted,
and `y` otherwise. A one-bit accumulator latches on a match, the loop feedback clears
it once per cycle, and the outer `map` reads the tag.

`scheduler` is a round-robin over the two user processes. The cell toggles 0/1 from
1 and the emitted value adds 2, so the pid alternates 2, 3, 2, 3, private then
public. Its input type is `Empty`: it only proposes the next process id.

```coq
model_immediate_concrete       = model_immediate       handler_runtime            p_pub_concrete p_priv_concrete scheduler
model_sliced_concrete          = model_sliced          handler_runtime slice_runs p_pub_concrete p_priv_concrete scheduler
model_sliced_userview_concrete = model_sliced_userview handler_runtime slice_runs p_pub_concrete p_priv_concrete scheduler
```


## 11. Adequacy: the example traces

Each design is exercised on two runs of the concrete system, one with no disk
interrupt and one with a disk interrupt, and each run is proved to be an accepted
trace. Reading a design's two runs against each other is what exhibits its
behaviour, so both are shown aligned, with `≠` marking every row on which they
differ.

Every output is a six-slot tuple with exactly one slot `Some` at a time, and for each
run we show only that value. A user process's value appears bare (`Get`, `NOP`,
`Sys`); everything else is labelled by the slot it came from: `sch hi` / `sch lo` for
the scheduler naming the private or the public process, and `tmr` / `dsk` / `dfl` for
the timer, disk and default handlers. A handler emits `Nth` (`Nothing`) on each step
and `Nfy` (`Notify`) on the one that completes it, so an `Nth`/`Nfy` pair is exactly
one handler run. In the user-view columns `·` is `None`.


### `model_immediate`: the leak

`trace_immediate_no_dI'` against `trace_immediate_with_dI'`.

```text
  no disk interrupt        with disk interrupt
  ──────────────────────────────────────────────
  Get                      Get
                           dI                     ← secret input
                           Get
                           dsk  Nth               ← the disk handler runs immediately
                           dsk  Nfy
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

What this shows is *when* a handler run may appear. In `model_immediate` it appears
whenever its interrupt happened to be serviced: the disk run lands in the middle of
the public output stream, and everything after it shifts down.

### `model_sliced`: the same two runs, and the projection

`trace_sliced_no_dI'` against `trace_sliced_with_dI'`, in the same layout. Each run
now carries its own `user view` column, the sequence `model_sliced_userview` emits,
i.e. that run under `parse_output`. They are two distinct traces, and the point of
the theorem is that they are *indistinguishable* at `⊥`.

```text
  no disk interrupt      with disk interrupt
  output     user view   output     user view
  ─────────────────────────────────────────────────────
  Get        Get         Get        Get
                         dI         dI         ← secret input: nothing happens, the disk
                         Get        Get          interrupt is masked until a slice opens
                         Get        Get
  tI         tI          tI         tI
  Get        Get         Get        Get
  tmr  Nth   ·           tmr  Nth   ·
  tmr  Nfy   ·           tmr  Nfy   ·
  dfl  Nth   ·        ≠  dsk  Nth   ·          ┐ the slice: two handler runs, and the
  dfl  Nfy   ·        ≠  dsk  Nfy   ·          │ whole difference between the two runs
  dfl  Nth   ·           dfl  Nth   ·          │ is that the disk handler takes the
  dfl  Nfy   ·           dfl  Nfy   ·          ┘ place of the first NOP run
  sch  hi    ·           sch  hi    ·
  NOP        NOP      ≠  Sys        Sys        ← the only surviving difference; both secret,
  tI         tI          tI         tI           so indistinguishable at ⊥
  NOP        NOP         NOP        NOP
  tmr  Nth   ·           tmr  Nth   ·
  tmr  Nfy   ·           tmr  Nfy   ·
  dfl  Nth   ·           dfl  Nth   ·          ┐
  dfl  Nfy   ·           dfl  Nfy   ·          │ second slice, identical in both runs
  dfl  Nth   ·           dfl  Nth   ·          │
  dfl  Nfy   ·           dfl  Nfy   ·          ┘
  sch  lo    ·           sch  lo    ·
  Get        Get         Get        Get
```

Three things stand out, and they are the whole argument in miniature.

**A handler run can appear in only one place.** Compare with `model_immediate`
above, where the disk handler ran the moment its interrupt was serviced. Here the
disk interrupt arrives and *nothing happens*: it is masked, so it is merely recorded
as pending, and the public process carries on emitting. Only when the timer handler
completes does a slice open, and only inside that slice may a handler run.

**Inside the slice, the disk handler substitutes for a NOP run.** That is the only
structural difference between the two runs, the `≠` at the first of the two handler
runs.

**The projection erases the substitution entirely.** Both `dsk` and `dfl` sit in
slots `parse_output` discards, so each run's user view is `·` on every handler step
and every scheduled pid. Comparing the two view columns against each other, the only
place they differ at all is the secret process reacting to its notification, `NOP`
against `Sys`, and both of those are classified secret, so an observer at `⊥` cannot
tell them apart.


## Where to go next

The security argument can be found in [`noninterference.md`](noninterference.md).
