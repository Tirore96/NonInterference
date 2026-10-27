# NonInterference

Rocq mechanisation accompanying the paper *Timing-Sensitive Non-Interference for
Interrupt Handling, Compositionally and Mechanically* (draft in [`tex/`](tex/)).
The paper is the reference for everything here; this file only says where things
are.

An operating system with interrupt handling is modelled as one process in the
calculus of Rafnsson et al., *Timing-Sensitive Noninterference through
Composition*,
[POST 2017](https://users.ece.cmu.edu/~lbauer/papers/2017/post2017-compose-time.pdf).
Ordinary interrupt handling leaks whether a secret disk interrupt occurred, through
the schedule alone. Servicing interrupts only inside publicly timed slices, with
unused handler runs filled by a dummy handler, removes the leak, for any scheduler
and user processes that are themselves non-interfering.

## Results

| Rocq | Paper | Axioms |
|---|---|---|
| `out_NI`, `map_NI`, `sta_NI`, `swi_NI`, `par_NI`, `loop_NI`, `maybe_NI` ([`theorems.v`](theories/theorems.v)) | Theorem 1 (composition) | none |
| `model_immediate_not_NI` ([`noninterference.v`](theories/noninterference.v)) | Theorem 2 (the leak) | none |
| `model_sliced_NI` ([`noninterference.v`](theories/noninterference.v)) | Theorem 3 (no leak) | none |
| `model_sliced_userview_NI` ([`noninterference.v`](theories/noninterference.v)) | Corollary 1 | none |
| `restore_invariant_noop` ([`models.v`](theories/models.v)) | Theorem 4 | none |
| `NI_paper`, `ObliviousDis_iff`, `NI_lEquiv` ([`adequacy.v`](theories/adequacy.v)) | §VII-A: our definitions equal the original's | none |
| `model_immediate_not_NI_paper`, `model_sliced_NI_paper` ([`adequacy.v`](theories/adequacy.v)) | Theorems 2 and 3 in the original's terms | none |

Every result depends only on the two parameters `d` and `L` that fix the security
lattice: no classical logic and no uniqueness of identity proofs. Reductions are
inverted through determinism of reduction (`inv_*` lemmas in
[`definitions.v`](theories/definitions.v)), not by dependent elimination.

## Files

| File | Contents |
|---|---|
| [`theories/definitions.v`](theories/definitions.v) | the calculus, traces, `NI`, the equivalences |
| [`theories/theorems.v`](theories/theorems.v) | the composition theorems of Rafnsson et al. |
| [`theories/models.v`](theories/models.v) | the generic model, both interrupt policies, a concrete system and its traces |
| [`theories/noninterference.v`](theories/noninterference.v) | the model's equivalences and Theorems 2 and 3 |
| [`theories/adequacy.v`](theories/adequacy.v) | the original definitions, their equivalence with ours, the main results in the original's terms |

## Building

Requires Rocq 9.0.1 with `mathcomp`, `deriving`, Hierarchy Builder and `paco` (see
[`_CoqProject`](_CoqProject)). From the repository root:

```bash
make
```

To check the axioms of a result, compile a file such as

```coq
From NonInterference.theories Require Import noninterference.
Print Assumptions model_sliced_NI.
```
