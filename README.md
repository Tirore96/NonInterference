# NonInterference

Rocq mechanisation accompanying the paper *Timing-Sensitive Non-Interference for
Interrupt Handling, Compositionally and Mechanically*, which is kept in a separate
repository.
The paper is the reference for everything here; this file only says where things
are.

An operating system with interrupt handling is modelled as one process in the
calculus of Rafnsson et al., *Timing-Sensitive Noninterference through
Composition*,
[POST 2017](https://users.ece.cmu.edu/~lbauer/papers/2017/post2017-compose-time.pdf).
Immediate interrupt handling, which services an interrupt as soon as it can, leaks whether a secret disk interrupt occurred, through
the schedule alone. Servicing interrupts only inside publicly timed slices, with
unused handler runs filled by a dummy handler, removes the leak, for every scheduler
and pair of user processes of the model.

## Results

| Rocq | Paper | Axioms |
|---|---|---|
| `out_NI`, `map_NI`, `sta_NI`, `swi_NI`, `par_NI`, `loop_NI`, `maybe_NI` ([`theorems.v`](theories/theorems.v)) | Theorem 1 (composition) | none |
| `sta_NI_pred` ([`theorems.v`](theories/theorems.v)) | Theorem 2 (composition of a state cell under an invariant; our addition) | none |
| `model_immediate_userview_not_NI` ([`noninterference.v`](theories/noninterference.v)) | Theorem 3 (the leak, in the user view) | none |
| `model_immediate_not_NI` ([`noninterference.v`](theories/noninterference.v)) | §V-A: the leak in the full view | none |
| `model_sliced_userview_NI` ([`noninterference.v`](theories/noninterference.v)) | Theorem 4 (no leak in the user view, for every scheduler and pair of user processes) | none |
| `model_sliced_NI` ([`noninterference.v`](theories/noninterference.v)) | §V-A: no leak in the full view | none |
| `model_policy_NI` ([`noninterference.v`](theories/noninterference.v)) | Theorem 5 (any policy meeting three obligations is non-interfering) | none |
| `model_timer_unmasked_NI` ([`noninterference.v`](theories/noninterference.v)) | a second instance of Theorem 5, the timer left unmasked at boundaries | none |
| `sliced_run_gated` ([`model_sliced.v`](theories/model_sliced.v)) | §V-B: the slice invariant holds of every reachable state | none |
| `NI_paper`, `ObliviousDis_iff`, `NI_lEquiv` ([`adequacy.v`](theories/adequacy.v)) | Appendix: our definitions equal the original's | none |
| `model_immediate_not_NI_paper`, `model_sliced_NI_paper` ([`adequacy.v`](theories/adequacy.v)) | Theorems 3 and 4 in the original's terms | none |

Every result depends only on the two parameters `d` and `L` that fix the security
lattice: no classical logic and no uniqueness of identity proofs. Reductions are
inverted through determinism of reduction (`inv_*` lemmas in
[`definitions.v`](theories/definitions.v)), not by dependent elimination.

## Files

| File | Contents |
|---|---|
| [`theories/definitions.v`](theories/definitions.v) | the calculus, traces, `NI`, the equivalences |
| [`theories/theorems.v`](theories/theorems.v) | the composition theorems of Rafnsson et al. |
| [`theories/generic_model.v`](theories/generic_model.v) | the generic model |
| [`theories/concrete_system.v`](theories/concrete_system.v) | a concrete system, trace tactics, the state along a run (`run_states_model`) |
| [`theories/model_immediate.v`](theories/model_immediate.v) | the immediate policy, its concrete instance, traces and state rows |
| [`theories/model_sliced.v`](theories/model_sliced.v) | the sliced policy, the slice invariant, the user view, its concrete instance, traces and state rows |
| [`theories/model_timer_unmasked.v`](theories/model_timer_unmasked.v) | the sliced policy with the timer left unmasked at boundaries, its concrete instance, traces and state rows |
| [`theories/noninterference.v`](theories/noninterference.v) | the model's equivalences, Theorems 3, 4 and 5, Corollaries 1 and 2 |
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
