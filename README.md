# NonInterference

A Rocq/Coq development proving **non-interference** for a small model of an
operating system with interrupt handling: a secret (disk) interrupt cannot be
inferred by an attacker who observes only user-visible output. It contrasts a
baseline design that *leaks* the secret through scheduling with a "good" design
whose fixed-length, publicly-masked interrupt handling *provably* does not.

The work is built on a small process calculus (`Proc I O`) and a lattice of
security levels; the security condition is stated relationally (per-interface
"myrels") and the top result is a machine-checked `NI` theorem.

## The argument in one picture

```text
   secret disk interrupt ──▶ ┌───────────────┐ ──▶ user-visible output
                             │  the OS model  │
   public timer interrupt ─▶ └───────────────┘ ──▶ (attacker observes this)

   model_bad   : handler stops when it emits its secret "Notify"
                 ⇒ mask/scheduling timing depends on the secret ⇒ LEAKS
   model_good  : handler stops on a fixed, public time-slice boundary
                 ⇒ scheduling depends only on public data ⇒ NON-INTERFERING
```

## Threat model

The attacker is the least (most exposed) security level `⊥`. A value is **public**
if it is observable to every level (compared by equality everywhere) and
**private** if it is *not* observable to `⊥` (secret there, public above). The only
genuine secret input is the disk interrupt; the timer interrupt is a public,
scheduled event. `NI ... p` says: varying or inserting/removing secret inputs never
changes the set of traces an observer at any level can see — in particular, the
`⊥`-observer cannot tell whether a disk interrupt occurred.

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
toggle). The good model fixes every handler at two output steps, derived from the
public time slice; a real system would reach that fixed length by padding.

## Glossary

| Term | Meaning |
|---|---|
| `⊥` (`\bot`) | The attacker: the least, most-exposed observer level. |
| **public** | Observable to all levels; compared by equality; never secret. (`publicRel`) |
| **private** | Not observable to `⊥` (secret at `⊥`, public above). (`privateRel`) |
| **secret** | Informal property "`dis` holds at the observer's level" — the thing NI lets vary. |
| **default / NOP handler** | The same thing: pool slot 2. Present only for privacy, as the indistinguishable partner of the disk handler; it has no interrupt of its own. |
| **myrel** | A per-type security relation carrying both `rel` (indistinguishability) and `dis` (secrecy). |

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
| [`theories/theorems.v`](theories/theorems.v) | Generic non-interference theorems for the calculus (`par_NI`, `sta_NI`, `swi_NI`, map/output-weakening). |
| [`theories/models.v`](theories/models.v) | The three concrete models and everything they are built from. |
| [`theories/noninterference.v`](theories/noninterference.v) | The concrete `in_rel`/`out_rel`/state relations and the three theorems above. |
| [`docs/models.md`](docs/models.md) | **What the models are** — long-form companion to `models.v`. |
| [`docs/noninterference.md`](docs/noninterference.md) | **Why they are (non-)interfering** — the myrels, the interface relations, and the `fv_NI` proof, companion to `noninterference.v`. |

## Where to read next

- To understand the **models**, start with [`docs/models.md`](docs/models.md).
- To understand the **proof** — the security relations and the one hard obligation
  (`fv_NI`, closure of the state relation under the state transition) — read
  [`docs/noninterference.md`](docs/noninterference.md).
