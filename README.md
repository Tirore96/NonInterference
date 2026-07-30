# NonInterference

A Rocq/Coq development proving **non-interference** for a small model of an
operating system with interrupt handling: a secret (disk) interrupt cannot be
inferred by an attacker who observes only user-visible output. It contrasts a
baseline design that *leaks* the secret through scheduling with a "good" design
whose handling *provably* does not.

The work is built on a small process calculus (`Proc I O`) and a lattice of
security levels; the security condition is stated relationally (per-interface
*characterised equivalences*, `cRel`) and the top result is a machine-checked `NI`
theorem.

## The argument in one picture

The leak in `model_bad` is a **scheduling** leak. A disk interrupt makes the disk
handler run *right away*, displacing whichever process was scheduled. Every
handler runs for exactly **two** output steps — `Nothing` then `Notify` — so two
steps of the public schedule are consumed before control is handed back to the
process that was displaced.

The attacker never sees the handler run. In the full pool output the handler has
its own slot and that slot is secret, so `Some _` there is indistinguishable from
`None`; in the user-visible output the handler's slot does not exist at all. What
the attacker *can* see is the public process's slot, and for those two steps it
reads `None`:

```text
   model_bad — the attacker's view of the same run, without and with a disk interrupt

     step                 1      2      3      4
     no disk interrupt   Get    Get    Get    Get
     disk interrupt      Get     ·      ·     Get
                                └──┬──┘        │
                       the disk handler's two   └─ control handed back to the
                       steps; two public          public process, which resumes
                       outputs that were due
                       never arrive
```

Nothing about this depends on *which* process was displaced: had the disk
interrupt landed on the private process instead, the same two-step displacement —
and the same visible gap in the schedule — would occur.

The good design closes the leak by never letting a secret interrupt change *when*
anything runs. Handlers run only inside a fixed, public time slice, and all take
the same two steps, so a secret handler run merely takes the place of the
NOP-handler filler that would otherwise occupy the slice. The public schedule is
identical either way:

```text
   model_bad   : a handler starts on arrival and stops when it emits its secret
                 "Notify" ⇒ scheduling and mask timing depend on the secret ⇒ LEAKS
   model_good  : handlers run only within a fixed, public time slice, all of the
                 same length ⇒ scheduling depends only on public data
                            ⇒ NON-INTERFERING
```

This comes in two versions, and the distinction matters for what is being claimed:
`model_good` is proved non-interfering on the **full pool output**, where handler
and scheduler slots are still visible but security-classified, and
`wrapped_model_good` on the **user-visible output**, where `parse_output` has
erased everything but the public output and the syscall. The second is the
headline result; the first is what it is built from.

## Threat model

The attacker is the least — most exposed — security level `⊥`; every interface of
the model classifies its values as **public** or **private** relative to that
lattice (see the glossary below). The only genuine secret input is the disk
interrupt; the timer interrupt is a public, scheduled event, and the model is
free to let scheduling depend on it. `NI ... p` says: varying or
inserting/removing secret inputs never changes the set of traces an observer at
any level can see — in particular, the `⊥`-observer cannot tell whether a disk
interrupt occurred.

## Results

Three machine-checked theorems (in
[`theories/noninterference.v`](theories/noninterference.v)):

| Theorem | Statement | Meaning |
|---|---|---|
| `model_bad_not_NI` | `~ NI in_rel out_rel model_bad` | The baseline model **leaks**: a secret disk interrupt is observable. |
| `model_good_NI` | `NI in_rel out_rel model_good` | The good model is non-interfering on the full pool output. |
| `wrapped_model_good_NI` | `NI in_rel final_out_rel wrapped_model_good` | The final model is non-interfering on the **user-visible** output — the headline result. |

## `model_bad` vs `model_good` at a glance

Both models share the entire generic structure (process pool, stateful wrapper,
state layout, and three of the four `state_step` stages). They differ in exactly
two places — `handler_preroutine` and `bool_coding` — and that difference is the
whole security story.

| | `model_bad` | `model_good` |
|---|---|---|
| **`handler_preroutine`** | `bad_preroutine`: on a handler's `Notify`, unmask everything; if it was the timer, ask to reschedule | `good_preroutine` = `check_ir_count ∘ check_handler_completed ∘ initiate_ir`: reload the slice on a timer `Notify`, unmask at fixed boundaries, tick the slice |
| **`bool_coding`** | `id` (no bookkeeping) | `bool_coding`: bake the reachable time-slice invariant back in; force the default mask to equal the disk mask |
| **Initial masks / counter** | all masks clear; counter `None` (disabled) | all masks set except the timer; counter `Some 0` |
| **When a handler stops** | when it emits its **secret** `Notify` — *secret-driven* | at a fixed **public** time-slice boundary — *slice-driven* |
| **What mask changes track** | secret handler behaviour | public slice boundaries |
| **Non-interfering?** | **No** (`model_bad_not_NI`) | **Yes** (`model_good_NI`) |
| **Why** | completion timing leaks the secret interrupt via scheduling | scheduling depends only on the public slice, so the secret never shows |

Because all masks are **public**, handler run-time must be **fixed** (a
variable, secret-dependent run-time would leak through the public masks as they
toggle). The good model fixes every handler at two output steps — all three
handlers are the same process, `I_handler` — and sizes the time slice to a whole
number of those runs; a real system would reach that fixed length by padding.

## Glossary

The definitive, formal versions of these — the actual `dis` and `rel` bodies — are
in [`docs/noninterference.md` §2](docs/noninterference.md).

| Term | Meaning |
|---|---|
| `⊥` (`\bot`) | The attacker: the least, most-exposed observer level. |
| **public** | Observable to all levels; compared by equality; never secret. (`publicRel`) |
| **private** | Not observable to `⊥` (secret at `⊥`, public above). (`privateRel`) |
| **secret** | Informal property "`dis` holds at the observer's level" — the thing NI lets vary. |
| **default / NOP handler** | The same thing: pool slot 2. Present only for privacy, as the indistinguishable partner of the disk handler; it has no interrupt of its own. |
| **`cRel`** | A *characterised equivalence*: a per-type security relation carrying both `rel` (level-indexed indistinguishability, an equivalence) and `dis` (secrecy), where `dis l` picks out exactly one `rel l`-equivalence class. |

## Logical foundations

The development is constructive except for one import of classical logic —
`Require Import Classical` at [`theories/theorems.v:739`](theories/theorems.v). The
law of excluded middle is used only in the switch non-interference lemma
`swi_NI'`, because the `aware` predicate is not constructively decidable (a
decision procedure could replace it).

## Building

From the repository root:

```bash
make
```

This compiles the four-file chain in dependency order
(`definitions → theorems → models → noninterference`). The build requires Rocq/Coq
9.0.1 with `mathcomp`, `paco`, `deriving`, `Equations`, and `HB`
(Hierarchy Builder); see [`_CoqProject`](_CoqProject).

## Repository map

| Path | What it is |
|---|---|
| [`theories/definitions.v`](theories/definitions.v) | The process calculus (`Proc I O`), traces, `NI`, and the security relations (`publicRel`, `privateRel`, `eqpair`/`eqsum`/`eqmaybe` and variants, `fv_NI`). |
| [`theories/theorems.v`](theories/theorems.v) | Generic non-interference theorems for the calculus, one per constructor (`out_NI`, `map_NI`, `sta_NI`, `swi_NI`, `par_NI`, `loop_NI`, `maybe_NI`). These mechanise results from separate prior work; they are used here, not contributed. |
| [`theories/models.v`](theories/models.v) | The three concrete models and everything they are built from. |
| [`theories/noninterference.v`](theories/noninterference.v) | The concrete `in_rel`/`out_rel`/state relations and the three theorems above. |
| [`docs/models.md`](docs/models.md) | **What the models are** — long-form companion to `models.v`. |
| [`docs/noninterference.md`](docs/noninterference.md) | **Why they are (non-)interfering** — the `cRel`s, the interface relations, and the `fv_NI` proof, companion to `noninterference.v`. |

## Where to read next

- To understand the **models**, start with [`docs/models.md`](docs/models.md).
- To understand the **proof** — the security relations and the one hard obligation
  (`fv_NI`, closure of the state relation under the state transition) — read
  [`docs/noninterference.md`](docs/noninterference.md).
