# NonInterference

A Rocq/Coq development proving **non-interference** for a model of an operating
system that handles interrupts. One interrupt, the disk interrupt, is secret;
the theorem says an attacker watching the system's output cannot tell whether it
occurred.

The interesting part is that a naive interrupt handler *does* leak it, and not
through any data it computes: it leaks through **scheduling**. Servicing a secret
interrupt takes CPU time away from the process that was running, and the resulting
gap in that process's output is visible. The development formalises both designs,
the one that leaks and the one that does not, and proves each claim.

Both designs are expressed in a small process calculus, `Proc I O`.
Non-interference is a property of a closed term in that calculus. Stating it takes a
*characterised equivalence* on the input type and one on the output type. At each
security level, such an equivalence cuts the values into classes an observer there
cannot tell apart. One of those classes is **distinguished**: it holds the values
that observer does not see at all, and it is empty when the level hides nothing.
The calculus and its generic non-interference
theorems are not ours: they are due to Rafnsson et al., *Timing-Sensitive
Noninterference through Composition*,
[POST 2017](https://users.ece.cmu.edu/~lbauer/papers/2017/post2017-compose-time.pdf).
The contribution here is the OS models and their proofs, together with the
mechanisation of that paper's theorems.

## The system being modelled

A process pool of six slots, driven by a global state and a feedback loop:

| slot | process | |
|---|---|---|
| 0, 1, 2 | timer, disk and default interrupt handlers | each runs for the same fixed number of output steps, signalling completion with `Notify` |
| 3 | the scheduler | proposes which user process runs next |
| 4 | the secret user process | consumes the disk handler's notifications |
| 5 | the public user process | emits on the public channel |

Slots 3, 4 and 5 are **parameters** of the development: the results below hold for
any scheduler and any two user processes that are themselves non-interfering at the
classification their slot declares, over arbitrary output alphabets. The concrete
instance used for the example traces is a round-robin scheduler, a
`p_priv_concrete` that issues a `Syscall` if the disk handler notified it and `NOP`
otherwise, and a `p_pub_concrete` that repeatedly issues `GetRequest`. Only the
interrupt handlers are fixed: they are the mechanism under study.

Exactly one slot runs per step, chosen by the current pid. The global state holds a
`(pending, mask)` bit pair per interrupt, plus a time-slice counter that only the
non-interfering design uses. An interrupt is serviced when it is pending and
unmasked.

## The three models

Everything below refers to these. All three are in
[`theories/models.v`](theories/models.v).

| Model | Type | Output it exposes | |
|---|---|---|---|
| `model_immediate` | `Proc TInterrupt (T_out Opub Opriv)` | the full pool output: one slot per process, so handler and scheduler activity is visible | the naive design; **leaks** |
| `model_sliced` | `Proc TInterrupt (T_out Opub Opriv)` | the same full pool output | the fixed design; non-interfering |
| `model_sliced_userview` | `Proc TInterrupt (T_out_userview Opub Opriv)` | only what the two user space processes emit: a public output or a syscall, every other slot erased | `model_sliced` behind a projection; the headline result |

`Opub` and `Opriv` are the two user processes' output alphabets. They are parameters
throughout, so both output types are written over them. The input type takes no
parameters, and all three models share it: an interrupt *is* an input. `TInterrupt`
(`T_in` in the source) has three values, `TimerInterrupt`, `DiskInterrupt` and
`DefaultInterrupt`. Delivering one is the only thing the environment can do to a
model; the model records it as pending and decides later whether to service it.

The models then differ along two independent axes, and it helps to keep them apart.

**Axis 1: behaviour (`model_immediate` vs `model_sliced`).** Same input and output
types, same pool, same state layout. Both are the *same* generic definition,
`model`, at a different triple of arguments: `init`,
`handler_preroutine`, and `restore_invariant`, tabulated in
[`docs/models.md` §8](docs/models.md). That difference is the whole security
story: one leaks, the other does not.

**Axis 2: observation (`model_sliced` vs `model_sliced_userview`).** Same
behaviour; they are literally the same process. `model_sliced_userview` is
`model_sliced` with a projection on its output,
`map id parse_output model_sliced`, which erases every slot but the two user space
processes. Below, `·` is `None` and `Nfy` is `Notify`:

```text
                     pub     sys     sch     dfl     dsk     tmr      parse_output
  public output   (  Get  ,   ·   ,   ·   ,   ·   ,   ·   ,   ·   )  ---------->   Get
  disk handler    (   ·   ,   ·   ,   ·   ,   ·   ,  Nfy  ,   ·   )  ---------->   ·
  syscall         (   ·   ,  Sys  ,   ·   ,   ·   ,   ·   ,   ·   )  ---------->   Sys
  scheduler       (   ·   ,   ·   ,   4   ,   ·   ,   ·   ,   ·   )  ---------->   ·
                    '-----------'   '---------------------------'
                    kept            discarded: scheduler and handler activity
```

Exactly one slot is `Some` per step, so each row above is a single output step.

The six-slot tuple is the natural
statement for a parallel composition, and it is the stronger non-interference claim: the attacker
sees every slot, handler and scheduler activity included. The user-visible result
then follows by weakening the output equivalence.

## Threat model

The attacker is an observer at `⊥`, the bottom of a security lattice: the higher the
level, the more it sees, so `⊥` sees the least. Each level comes with two notions,
and every classification in the development is expressed with them.

- Two values are **indistinguishable** at level `l` when the level's equivalence
  relates them: the observer receives one of them but cannot tell which.
- A value is **unobservable** at `l` when the observer does not see the event at
  all, so it can be inserted or removed without the observer noticing.

The two notions are tied together. At each level the equivalence partitions a type
into classes of indistinguishable values, and the unobservable values are required
to be exactly one of those classes, the **distinguished class**. It is empty when
the level hides nothing. One such partition per level, each with its distinguished
class, makes a **characterised equivalence**: `cEquiv` in the source
([`docs/noninterference.md` §1](docs/noninterference.md)). Every classification
below is an instance of it.

The two extremes are the ones used most. A **public** value is observable at every
level and indistinguishable only from itself: every class a singleton, and the
distinguished class empty. A **private** value is unobservable at `⊥`, where all
private values are therefore indistinguishable: one class, and it is the
distinguished one. Above `⊥` a private value is observable and values must agree
exactly. (Formally,
`public_equiv` and `private_equiv`, in
[`docs/noninterference.md` §2](docs/noninterference.md).)

For interrupts, the input of the models, the characterised equivalence `in_equiv`
marks the disk interrupt unobservable at `⊥`. The other interrupts are
left observable and all values are indistinguishable only from itself.
Of the three interrupts the disk one is the only secret.

`NI in_equiv out_equiv p` is then the noninterference statement: at every level,
inserting or removing inputs that are unobservable there, or swapping inputs that
are indistinguishable there, leaves the traces that observer can see unchanged. The
classification lives entirely in `in_equiv` and `out_equiv`, one characterised
equivalence on the input type and one on the output type. Their equivalence part is
the *L-equivalences* of the original paper; the distinguished class is what makes
insertion and deletion possible at all. Every claim made above about what is public
or secret is a statement about those two, which are given in
[`docs/noninterference.md` §4](docs/noninterference.md).

## The leak

A disk interrupt makes the disk handler run immediately, displacing whichever
process was scheduled. The handler runs for its full length, then control returns
to the displaced process. Below, and in the counterexample, that length is two
output steps, the concrete instance of the parameter `runtime`.

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
process was displaced: interrupting the secret process produces the same gap in the
schedule.

`model_sliced` closes it by taking away the disk interrupt's power to interrupt a
user process. Handler execution still depends on the timer, since the **timer**
handler's completion starts the time slice. That dependence is public and therefore
harmless. What a secret interrupt can no longer do is pick the moment a handler
runs. Handlers run only inside the slice and all take the same number of steps, and
a default "NOP" handler fills any part of the slice that no real interrupt claims.
A secret handler run therefore replaces a NOP run
rather than displacing a user process, and the public schedule is identical either
way.

## Results

Three machine-checked theorems, in
[`theories/noninterference.v`](theories/noninterference.v):

| Theorem | Statement | Meaning |
|---|---|---|
| `model_immediate_not_NI` | `~ NI in_equiv out_equivC model_immediate_concrete` | The naive design leaks: a secret disk interrupt is observable. |
| `model_sliced_NI` | `NI in_equiv (out_equiv Opub Opriv) (model_sliced runtime runs p_pub p_priv p_sched)` | The fixed design is non-interfering even on the full pool output, for *any* non-interfering userspace and scheduler, at any handler length and slice size. |
| `model_sliced_userview_NI` | `NI in_equiv (out_equiv_userview Opub Opriv) (model_sliced_userview runtime runs p_pub p_priv p_sched)` | It is therefore non-interfering on the user-visible output, the headline result. |

Two of the parameters are numbers. The **handler length** `runtime` counts the output
steps every handler takes before it signals completion with `Notify`. The **slice
size** `runs` counts the complete handler runs that fit in one time slice. A slice
therefore lasts `runs * runtime` output steps and always ends on a handler boundary.

The two positive results are parametric. In full:

```coq
forall (Opub Opriv : Ty) (runtime runs : nat)
       (p_pub : Proc Empty Opub)
       (p_priv : Proc THandlerOutput Opriv)
       (p_sched : Proc Empty Nat),
  NI (public_equiv Empty) (public_equiv Opub) p_pub ->
  NI (private_equiv THandlerOutput) (private_equiv Opriv) p_priv ->
  NI (public_equiv Empty) (public_equiv Nat) p_sched ->
  NI in_equiv (out_equiv_userview Opub Opriv)
     (model_sliced_userview runtime runs p_pub p_priv p_sched)
```

So the theorem covers the interrupt-and-scheduling mechanism in general:
arbitrary userspace and scheduler, arbitrary output alphabets, arbitrary handler
length and slice size. The last two carry no side condition. `time_slice runtime
runs = runs * runtime` makes the slice end on a handler boundary by construction.

`model_sliced_concrete_NI` and `model_sliced_userview_concrete_NI` recover the
concrete system by instantiating with `p_pub_concrete_NI`, `p_priv_concrete_NI`
and `scheduler_NI`.
`model_immediate` is parametric in the same way, but the counterexample is stated
at the concrete instance `model_immediate_concrete`: exhibiting a leak needs only
one system.

## Logical foundations

The development is constructive except for one import of classical logic,
`Require Import Classical` at [`theories/theorems.v:739`](theories/theorems.v). The
law of excluded middle appears only in the switch non-interference lemma `swi_NI`.
A premise of that lemma uses the predicate `aware`, which is not constructively
decidable. A decision procedure for `aware` would remove the need for excluded
middle.

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
| [`theories/definitions.v`](theories/definitions.v) | The process calculus, traces, `NI`, and the security equivalences. |
| [`theories/theorems.v`](theories/theorems.v) | Generic non-interference theorems for the calculus, one per constructor. These mechanise results from Rafnsson et al., *Timing-Sensitive Noninterference through Composition*, [POST 2017](https://users.ece.cmu.edu/~lbauer/papers/2017/post2017-compose-time.pdf); this repository uses them as prior work. |
| [`theories/models.v`](theories/models.v) | In three parts: the skeleton both designs share, ending in the generic `model`; the two designs, as `model` at two triples of arguments; and one concrete system, with the example traces. |
| [`theories/noninterference.v`](theories/noninterference.v) | The concrete input, output and state equivalences, and the three theorems above. |
| [`docs/models.md`](docs/models.md) | **What the models are.** Long-form companion to `models.v`. |
| [`docs/noninterference.md`](docs/noninterference.md) | **Why they are (non-)interfering.** The security equivalences and the proof, companion to `noninterference.v`. |

## Where to read next

- For the **models**, read [`docs/models.md`](docs/models.md): every process, the
  state layout, and the design rationale behind the sliced design.
- For the **proof**, read [`docs/noninterference.md`](docs/noninterference.md): the
  security equivalences, how the generic theorems compose, and the one hard
  obligation (`fv_NI`, closure of the state equivalence under the transition).
