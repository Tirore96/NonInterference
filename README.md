# NonInterference

A Rocq/Coq development proving **non-interference** for a model of an operating
system that handles interrupts. One interrupt — the disk interrupt — is secret;
the theorem says an attacker watching the system's output cannot tell whether it
occurred.

The interesting part is that a naive interrupt handler *does* leak it, and not
through any data it computes: it leaks through **scheduling**. Servicing a secret
interrupt takes CPU time away from the process that was running, and the resulting
gap in that process's output is visible. The development formalises both designs —
the one that leaks and one that does not — and proves each claim.

Both designs are expressed in a small process calculus, `Proc I O`, whose
interfaces carry the security classification; non-interference is then a property
of a closed term in that calculus. The calculus and its generic non-interference
theorems are reused from prior work — the contribution here is the OS models and
their proofs.
>>prior work, which does not include me, give a reference to the compositional non intereference paper<<

## The system being modelled

A process pool of six slots, driven by a global state and a feedback loop:

| slot | process | |
|---|---|---|
| 0, 1, 2 | timer, disk and default interrupt handlers | each runs for the same fixed number of output steps, signalling completion with `Notify` |
| 3 | the scheduler | proposes which user process runs next |
| 4 | the secret user process | consumes the disk handler's notifications |
| 5 | the public user process | emits on the public channel |

Slots 3, 4 and 5 are **parameters** of the development, not fixed processes: the
results below hold for any scheduler and any two user processes that are themselves
non-interfering at the classification their slot declares, over arbitrary output
alphabets. The concrete instance used for the example traces is a round-robin
scheduler, a `high_p` that issues a `Syscall` if the disk handler notified it and
`NOP` otherwise, and a `low_p` that repeatedly issues `GetRequest`. Only the
handlers and the padding are fixed — they are the mechanism under study.
>> What does padding refer to here? Write this more clearly.<<

Exactly one slot runs per step, chosen by the current pid. The global state holds a
`(pending, mask)` bit pair per interrupt — an interrupt is serviced when it is
pending and unmasked — plus a time-slice counter used by the good design.
>> Maybe use noninterfering instead of good (good/bad was a dichotomy we used before)<<

## The three models

Everything below refers to these. All three are in
[`theories/models.v`](theories/models.v).

| Model | Output it exposes | |
|---|---|---|
| `model_immediate` | the full pool output: one slot per process, so handler and scheduler activity is visible | the naive design; **leaks** |
| `model_sliced` | the same full pool output | the fixed design; non-interfering |
| `model_sliced_userview` | only the user-visible channel: a public output or a syscall, everything else erased | `model_sliced` behind a projection; the headline result |
>>We should have a title in the third column as well<<
The three differ along two independent axes, and it helps to keep them apart.

**Axis 1: behaviour — `model_immediate` vs `model_sliced`.** Same input and output
interface, same pool, same state layout. They differ in exactly two definitions
(`handler_preroutine` and `bool_coding`, tabulated
[below](#model_immediate-vs-model_sliced-at-a-glance)), and that difference is the
whole security story: one leaks, the other does not.

**Axis 2: observation — `model_sliced` vs `model_sliced_userview`.** Same
behaviour; they are literally the same process. `model_sliced_userview` is
`model_sliced` with a projection on its output,
`map id parse_output model_sliced`, which discards everything except the
user-visible channel. Below, `·` is `None` and `Nfy` is `Notify`:

```text
                     pub     sys     pid     dfl     dsk     tmr         parse_output
  public output   (  Get  ,   ·   ,   ·   ,   ·   ,   ·   ,   ·   )  --->   Get
  disk handler    (   ·   ,   ·   ,   ·   ,   ·   ,  Nfy  ,   ·   )  --->   ·
  syscall         (   ·   ,  Sys  ,   ·   ,   ·   ,   ·   ,   ·   )  --->   Sys
  scheduler       (   ·   ,   ·   ,   4   ,   ·   ,   ·   ,   ·   )  --->   ·
                    '-----------'   '---------------------------'
                    kept            discarded: scheduler and handler activity
```
>> Having parse_output above the projected output is confusing, it's a function, maybe it should be aligned with the arrow? I don't know, fix it.<<
Exactly one slot is `Some` per step, so each row above is one output step, not
four parallel events. `model_immediate` emits the same six-slot tuple as
`model_sliced` — the diagram is about the projection, not about the leak.

Proving non-interference at the full pool output — where the attacker sees more
than a real one ever would — is what makes the user-visible result follow by
weakening the output relation.
>> Well, since we have a parallel composition of six processes, somewhere there will be a six tuple, that's just how output reduciton of par works. Not sure what I want you to fix here<<
## Threat model

The attacker is `⊥`, the least and most exposed level of a security lattice. Each
interface classifies its values: **public** values must agree exactly at every
level, at `⊥` any two **private** values are related, so an observer there cannot tell
them apart, while above `⊥` they too must agree exactly (see the
[glossary](#glossary)).

The disk interrupt is the only secret input. The timer interrupt is public — it is
a scheduled event the attacker may as well know about, and the good design is
allowed to let scheduling depend on it. `NI in_rel out_rel p` is the standard
condition: inserting, removing, or varying secret inputs does not change the set of
traces an observer can see, at any level.
>>The reason the timer interrupt is a public event is that it changes the schedule of public processes. It has to be public.<<
>>We should explain that in_rel and out_rel are the interfaces we are talking about. Maybe interface is not a good word to use. The original paper calls them for L-equivalences (level indexed equivalences)<<
## The leak

A disk interrupt makes the disk handler run immediately, displacing whichever
process was scheduled. The handler runs for two output steps, then control returns
to the displaced process.

The attacker never sees the handler run: in the full pool output the handler's slot
is classified secret, and in the user-visible output that slot does not exist at
all. What the attacker sees is the *public* process's slot, which for those two
steps carries nothing:

```text
   model_immediate: the attacker's view of one run, without and with a disk interrupt

     step                    1      2      3      4
     no disk interrupt      Get    Get    Get    Get
     with disk interrupt    Get     ·      ·     Get
                                    '------'      '-- the displaced process resumes here
                                       |
       the disk handler runs here: the two public outputs that were
       due at steps 2 and 3 never arrive
```

Two public requests are enough to refute non-interference, and that is exactly the
counterexample `model_immediate_not_NI` constructs. The leak does not depend on which
process was displaced — interrupting the secret process produces the same gap in
the schedule.

`model_sliced` closes it by making the *timing* of handler execution independent of
which interrupts arrived. Handlers run only inside a time slice of fixed length,
which is started when the **timer** handler completes — a public event, since the
timer interrupt is public. All handlers take the same number of steps, and a
default "NOP" handler fills any part of the slice that no real interrupt claims. A secret
handler run therefore replaces a NOP run rather than displacing a user process, and
the public schedule is identical either way.
>>handler execution still depends on timer interrupt, it the disk interrupt that now has no power to interrupt user processes<<
## Results

Three machine-checked theorems, in
[`theories/noninterference.v`](theories/noninterference.v):

| Theorem | Statement | Meaning |
|---|---|---|
| `model_immediate_not_NI` | `~ NI in_rel out_relC model_immediate` | The naive design leaks: a secret disk interrupt is observable. |
| `model_sliced_NI` | `NI in_rel (out_rel Opub Opriv) (model_sliced runtime runs p_pub p_priv p_sched)` | The fixed design is non-interfering even on the full pool output — for *any* non-interfering userspace and scheduler, at any handler length and slice size. |
| `model_sliced_userview_NI` | `NI in_rel (final_out_rel Opub Opriv) (model_sliced_userview runtime runs p_pub p_priv p_sched)` | It is therefore non-interfering on the user-visible output — the headline result. |
>>handler length and slice length have not been explained yet<<
The two positive results are parametric. In full:

```coq
forall (Opub Opriv : Ty) (runtime runs : nat)
       (p_pub : Proc Empty Opub)
       (p_priv : Proc THandlerOutput Opriv)
       (p_sched : Proc Empty Nat),
  NI (publicRel Empty) (publicRel Opub) p_pub ->
  NI (privateRel THandlerOutput) (privateRel Opriv) p_priv ->
  NI (publicRel Empty) (publicRel Nat) p_sched ->
  NI in_rel (final_out_rel Opub Opriv)
     (model_sliced_userview runtime runs p_pub p_priv p_sched)
```

So the theorem is about the interrupt-and-scheduling mechanism, not about one
system: arbitrary userspace and scheduler, arbitrary output alphabets, arbitrary
handler length and slice size — the last two with no side condition, because
`time_slice runtime runs = runs * runtime` makes "the slice ends on a handler
boundary" structural rather than assumed.

What makes this available is a property of the design rather than of the
proof: the state transition never reads a user slot's output *value*, only whether
the slot produced one (`is_sch_out` matches `(None,(None,(Some n,_)))`). No user
behaviour reaches the schedule, so `fv_NI` — the one hard obligation — does not
depend on which processes fill the slots.
>>We should cut the paragraph above<<

`model_sliced_concrete_NI` and `model_sliced_userview_concrete_NI` recover the
concrete system by instantiating with `low_p_NI`, `high_p_NI` and `scheduler_NI`.
`model_immediate` stays concrete: it exists to exhibit a leak, and a
counterexample should be a single system.

Fixed, and out of scope: the pool's *shape* and *slot count*. The output
projections (`is_sch_out` and friends) are tuple patterns that hardwire two user
slots before the scheduler slot, and generalising that lands inside `fv_NI`.
>>Cut paragraph above<<

## `model_immediate` vs `model_sliced` at a glance
>>This entire section should be in the models file<<
The two models share their entire structure — the process pool, the stateful
wrapper, the state layout, and three of the four state-transition stages. They
differ in two definitions, and that difference is the whole security story.

| | `model_immediate` | `model_sliced` |
|---|---|---|
| **`handler_preroutine`** | `immediate_preroutine`: on a handler's `Notify`, unmask everything; if it was the timer, ask to reschedule | `sliced_preroutine` = `check_ir_count ∘ check_handler_completed ∘ initiate_ir`: reload the slice on a timer `Notify`, unmask at fixed boundaries, tick the slice |
| **`bool_coding`** | `id` (no bookkeeping) | `bool_coding`: restore the time-slice invariant; force the default mask to equal the disk mask |
| **Initial masks / counter** | all masks clear; counter `None` (disabled) | all masks set except the timer; counter `Some 0` |
| **When a handler stops** | when it emits its **secret** `Notify` — *secret-driven* | at a fixed **public** time-slice boundary — *slice-driven* |
| **What mask changes track** | secret handler behaviour | public slice boundaries |
| **Non-interfering?** | **No** (`model_immediate_not_NI`) | **Yes** (`model_sliced_NI`, for any non-interfering userspace) |
| **Why** | a handler runs as soon as its interrupt is serviced, so a secret interrupt displaces the scheduled process and the gap is visible | handlers run only within the public slice, replacing NOP filler, so the schedule is unchanged |

Handlers must all run for the same length of time, or the schedule would again
depend on which interrupt arrived. The three handler slots therefore reuse a single
process definition, `I_handler runtime`, and the slice is `runs * runtime` — a
whole number of handler runs by construction, so it always ends on a handler
boundary. Both `runtime` and `runs` are parameters; what the argument needs is
that the three handlers *share* a runtime, not what it is. A real system would
reach a fixed length by padding.

## Glossary
>>This section should probably be cut. We need to explain cRel somewhere, probably in the noninterference file, but we don't need the full glossary<<
Formal definitions — the actual `dis` and `rel` bodies — are in
[`docs/noninterference.md` §2](docs/noninterference.md).

| Term | Meaning |
|---|---|
| `⊥` (`\bot`) | The attacker: the least, most exposed level of the lattice. |
| **public** | Observable to all levels; compared by equality; never secret. (`publicRel`) |
| **private** | At `⊥`, any two values are related, so an observer there cannot distinguish them; above `⊥`, compared by equality like a public value. (`privateRel`) |
| **secret** | Said of a value the observer at its level may not see, so non-interference lets it vary. |
| **default / NOP handler** | Pool slot 2. It has no interrupt of its own; it exists to fill the time slice, so that a slice with a disk interrupt looks like one without. |
| **`cRel`** | A *characterised equivalence*: a per-type security relation carrying both `rel` (level-indexed indistinguishability, an equivalence) and `dis` (secrecy), where `dis l` picks out exactly one `rel l`-equivalence class. |

## Logical foundations

The development is constructive except for one import of classical logic,
`Require Import Classical` at [`theories/theorems.v:739`](theories/theorems.v). The
law of excluded middle is used only in the switch non-interference lemma `swi_NI`,
because the `aware` predicate is not constructively decidable; a decision procedure
would remove the need for it.
>>Reader has not been introduced to aware, say something like "because a premise of the theorem uses a definition `aware` which is not decidable, ......"<<
## Building

From the repository root:

```bash
make
```

This compiles the four-file chain in dependency order
(`definitions → theorems → models → noninterference`). The build requires Rocq/Coq
9.0.1 with `mathcomp`, `deriving` and `HB` (Hierarchy Builder); see
[`_CoqProject`](_CoqProject).

## Repository map

| Path | What it is |
|---|---|
| [`theories/definitions.v`](theories/definitions.v) | The process calculus (`Proc I O`), traces, `NI`, and the security relations (`publicRel`, `privateRel`, `eqpair`/`eqsum`/`eqmaybe` and variants, `fv_NI`). |
| [`theories/theorems.v`](theories/theorems.v) | Generic non-interference theorems for the calculus, one per constructor (`out_NI`, `map_NI`, `sta_NI`, `swi_NI`, `par_NI`, `loop_NI`, `maybe_NI`). These mechanise results from separate prior work; they are used here, not contributed. |
| [`theories/models.v`](theories/models.v) | The three models and everything they are built from. |
| [`theories/noninterference.v`](theories/noninterference.v) | The concrete input, output and state relations, and the three theorems above. |
| [`docs/models.md`](docs/models.md) | **What the models are** — long-form companion to `models.v`. |
| [`docs/noninterference.md`](docs/noninterference.md) | **Why they are (non-)interfering** — the security relations and the proof, companion to `noninterference.v`. |
>>Remove things in parenthesis from here<<
>>We mention prior work, throw a reference<<
## Where to read next

- For the **models** — every process, the state layout, and the design rationale
  behind the sliced design — read [`docs/models.md`](docs/models.md).
- For the **proof** — the security relations, how the generic theorems compose, and
  the one hard obligation (`fv_NI`, closure of the state relation under the state
  transition) — read [`docs/noninterference.md`](docs/noninterference.md).
