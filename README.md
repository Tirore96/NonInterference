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

## The system being modelled

A process pool of six slots, driven by a global state and a feedback loop:

| slot | process | |
|---|---|---|
| 0, 1, 2 | timer, disk and default interrupt handlers | each runs for exactly two output steps, emitting `Nothing` then `Notify` |
| 3 | round-robin scheduler | proposes which user process runs next |
| 4 | `high_p`, the secret user process | issues a `Syscall` if the disk handler notified it, otherwise `NOP` |
| 5 | `low_p`, the public user process | repeatedly issues `GetRequest` |

Exactly one slot runs per step, chosen by the current pid. The global state holds a
`(pending, mask)` bit pair per interrupt — an interrupt is serviced when it is
pending and unmasked — plus a time-slice counter used by the good design.

## The three models

Everything below refers to these. All three are in
[`theories/models.v`](theories/models.v).

| Model | Output it exposes | |
|---|---|---|
| `model_immediate` | the full pool output: one slot per process, so handler and scheduler activity is visible | the naive design; **leaks** |
| `model_sliced` | the same full pool output | the fixed design; non-interfering |
| `model_sliced_userview` | only the user-visible channel: a public output or a syscall, everything else erased | `model_sliced` behind a projection; the headline result |

`model_immediate` and `model_sliced` differ in exactly two definitions. The difference
between the two *outputs* is what `model_sliced_userview` adds — one emits a tuple with
a slot per process, the other keeps only the user-visible channel:

```text
  model_sliced, one output step        model_sliced_userview, the same step
  ( · , · , · , · , Notify , · )  ──▶  ·          disk handler ran: erased
  ( Get , · , · , · , · , · )     ──▶  Get        public output: kept
  ( · , Syscall , · , · , · , · ) ──▶  Syscall    syscall: kept
    │   │   │   │     │     │
    │   │   │   └─────┴─────┴── the three handler slots ─┐
    │   │   └── scheduler pid ─────────────────────────── these never survive
    │   └── syscall (secret)
    └── public output
```

Proving non-interference at the full pool output — where the attacker sees more
than a real one ever would — is what makes the user-visible result follow by
weakening the output relation.

## Threat model

The attacker is `⊥`, the least and most exposed level of a security lattice. Each
interface classifies its values: **public** values must agree exactly at every
level, **private** values are free at `⊥` and public above it (see the
[glossary](#glossary)).

The disk interrupt is the only secret input. The timer interrupt is public — it is
a scheduled event the attacker may as well know about, and the good design is
allowed to let scheduling depend on it. `NI in_rel out_rel p` is the standard
condition: inserting, removing, or varying secret inputs does not change the set of
traces an observer can see, at any level.

## The leak

A disk interrupt makes the disk handler run immediately, displacing whichever
process was scheduled. The handler runs for two output steps, then control returns
to the displaced process.

The attacker never sees the handler run: in the full pool output the handler's slot
is classified secret, and in the user-visible output that slot does not exist at
all. What the attacker sees is the *public* process's slot, which for those two
steps carries nothing:

```text
   model_immediate, the attacker's view of one run, without and with a disk interrupt

     step                 1      2      3      4
     no disk interrupt   Get    Get    Get    Get
     disk interrupt      Get     ·      ·     Get
                                └──┬──┘        └─ the displaced process resumes
                       the disk handler runs here; two public
                       outputs that were due never arrive
```

Two public requests are enough to refute non-interference, and that is exactly the
counterexample `model_immediate_not_NI` constructs. The leak does not depend on which
process was displaced — interrupting the secret process produces the same gap in
the schedule.

`model_sliced` closes it by making the *timing* of handler execution independent of
which interrupts arrived. Handlers run only inside a time slice of fixed length,
which is started when the **timer** handler completes — a public event, since the
timer interrupt is public. All handlers take the same two steps, and a default
"NOP" handler fills any part of the slice that no real interrupt claims. A secret
handler run therefore replaces a NOP run rather than displacing a user process, and
the public schedule is identical either way.

## Results

Three machine-checked theorems, in
[`theories/noninterference.v`](theories/noninterference.v):

| Theorem | Statement | Meaning |
|---|---|---|
| `model_immediate_not_NI` | `~ NI in_rel out_rel model_immediate` | The naive design leaks: a secret disk interrupt is observable. |
| `model_sliced_NI` | `NI in_rel out_rel model_sliced` | The fixed design is non-interfering even on the full pool output. |
| `model_sliced_userview_NI` | `NI in_rel final_out_rel model_sliced_userview` | It is therefore non-interfering on the user-visible output — the headline result. |

## `model_immediate` vs `model_sliced` at a glance

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
| **Non-interfering?** | **No** (`model_immediate_not_NI`) | **Yes** (`model_sliced_NI`) |
| **Why** | a handler runs as soon as its interrupt is serviced, so a secret interrupt displaces the scheduled process and the gap is visible | handlers run only within the public slice, replacing NOP filler, so the schedule is unchanged |

Handlers must all run for the same length of time, or the schedule would again
depend on which interrupt arrived. The three handler slots therefore reuse a single
process definition, `I_handler`, two output steps long, and the slice is sized to a
whole number of those runs. A real system would reach a fixed length by padding.

## Glossary

Formal definitions — the actual `dis` and `rel` bodies — are in
[`docs/noninterference.md` §2](docs/noninterference.md).

| Term | Meaning |
|---|---|
| `⊥` (`\bot`) | The attacker: the least, most exposed level of the lattice. |
| **public** | Observable to all levels; compared by equality; never secret. (`publicRel`) |
| **private** | Not observable to `⊥` — free there, public above. (`privateRel`) |
| **secret** | Said of a value the observer at its level may not see, so non-interference lets it vary. |
| **default / NOP handler** | Pool slot 2. It has no interrupt of its own; it exists to fill the time slice, so that a slice with a disk interrupt looks like one without. |
| **`cRel`** | A *characterised equivalence*: a per-type security relation carrying both `rel` (level-indexed indistinguishability, an equivalence) and `dis` (secrecy), where `dis l` picks out exactly one `rel l`-equivalence class. |

## Logical foundations

The development is constructive except for one import of classical logic,
`Require Import Classical` at [`theories/theorems.v:739`](theories/theorems.v). The
law of excluded middle is used only in the switch non-interference lemma `swi_NI'`,
because the `aware` predicate is not constructively decidable; a decision procedure
would remove the need for it.

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

## Where to read next

- For the **models** — every process, the state layout, and the design rationale
  behind the sliced design — read [`docs/models.md`](docs/models.md).
- For the **proof** — the security relations, how the generic theorems compose, and
  the one hard obligation (`fv_NI`, closure of the state relation under the state
  transition) — read [`docs/noninterference.md`](docs/noninterference.md).
