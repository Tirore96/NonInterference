# Departure from the original proof shape: an inductive invariant instead of restore_invariant

Recorded 2026-11-03, when the decision was taken. The detailed chain (definitions,
Hoare triples, composition) is §7 of `section5-restore-invariant.md`.

## The original shape

- The calculus of Rafnsson et al. gives one composition theorem per constructor.
  For `sta f g v p`, `sta_NI` asks that the state updates `f` and `g` be
  non-interfering on **every** pair of related states (`fv_NI`), reachable or not,
  and that `f` be equivalence-preserving on unobservable inputs (`f_EP`).
- The sliced policy is secure only because of a property that holds of the states
  it actually reaches: outside a slice the secret handlers are masked, inside one
  a handler is running or one is queued. On arbitrary related pairs this fails:
  two related states outside a slice with the disk and NOP handlers unmasked, the
  disk handler pending in one of them only, make `initiate_next` start a secret
  handler in one state and return to user space in the other (S versus U; the
  pid's tag is public).
- The original model therefore contained a proof-only function,
  `restore_invariant`, a parameter of the generic `model` applied inside
  `initiate_next` just before the choice. It wrote the policy's shape into the
  state (NOP pending in a slice, disk and NOP masked outside, NOP mask = disk mask),
  so the relational proof could assume that shape on every pair. Theorem 5
  (`restore_invariant_noop`) then showed it was the identity on reachable states,
  so the model with the function behaves like the policy without it (for
  `runtime ≠ 1`; at `runtime = 1` it was not the identity and cost each slice its
  last run).

## What was wrong with the explanation

The paper (V-C) and earlier notes explained the function by "stage-by-stage
composition forgets what earlier stages establish". That is a secondary effect at
most. The real cause: `sta_NI` quantifies over all related pairs, and the
policy's guarantee holds only **inductively** (true of the initial state,
preserved by every step); no single step establishes it from an arbitrary state.
Even a monolithic proof of the step would face the same unreachable pairs.

## The new shape

- **A new composition theorem, `sta_NI_pred`** (theorems.v, section
  `StaInvariant`, our addition, like sum types): if a predicate `P` holds of the
  initial state and the state updates preserve it, `fv_NI` and `f_EP` are needed
  only for states in `P`. Its proof is `sta_NI`'s with `P` threaded through the
  `lthread` lemmas: every state the proof hands to `f` or `g` is reached from the
  initial state by `f` and `g`.
- **An inductive invariant stated directly**, not as "the image of a function":
  `secret_gated` (outside a slice the secret handlers are masked; inside one, a
  handler is running; their masks agree), and at the choice point
  `secret_gated_at_boundary` (the same, allowing the handler-boundary shape that
  `queue_secret_run` establishes). From the latter, the one fact the security
  argument consumes: `secret_ready_iff_slice` (when no handler is running, a
  secret handler is ready exactly when a slice is open; slice-openness is public).
- **The model loses `restore_invariant`**; Theorem 5 disappears, and its role is
  taken by the invariant theorem (every reachable state is `secret_gated`), which
  is now *used* (it discharges `sta_NI_pred`'s preservation obligation).
- **The stage split stays**, but now passes a single-state fact from the service
  policy to `initiate_next` (`fv_NI_comp_on`), instead of only relatedness.

## Consequences

- One more departure from the original calculus, of the same kind as sums: a new
  composition theorem, proved from the definitions; the original theorems are
  untouched.
- The slice counter becomes a plain natural number with 0 meaning "outside a
  slice" (no option type). The counter is the number of output steps until the
  slice closes: opening loads `runs * runtime + 1` (the handler runs plus the
  closing step), `1` is the closing step, `0` is no slice. The boundary test is on
  the counter minus the closing step, so the policy's behaviour is unchanged.
- Behaviour changes only at `runtime = 1`, where the last run of a slice is no
  longer lost (it was `restore_invariant` that masked it). The traces and state
  rows are at `runtime = 2`; the counter values in the state rows shift by one
  (the encoding), the runs do not.
- Theorem 4 keeps holding for every runtime: `runtime ≠ 1` was needed only for the
  invariant under the old counter encoding, where the closing step `Some 0` read
  as "outside a slice".
- The relational proof of `initiate_next` shrank from a ~600-line case analysis
  to ~25 lines: `state_rel_bot` says that at level ⊥ two states are related
  exactly when their public fields (`pub_view`) agree, and the scheduler and
  handler bookkeeping computes public fields from public fields
  (`pub_view_initiate_handler`, `pub_view_leave_handlers`).
- The paper must be updated later: Section III (no `restore_invariant` in
  `initiate_next` or `model`), IV (counter encoding, runtime = 1 remark), V (the
  new story and the chain), VI (`sta_NI_pred` as an addition), and Theorem 5.

## As implemented (2026-11-03)

| Step | Rocq name | File |
|---|---|---|
| counter: 0 none, 1 closing, n+2 running | `slice_count := Nat`, `tick_slice` | models.v |
| definitions | `slice_open`, `handler_boundary`, `gated`, `secret_gated`, `secret_gated_at_boundary`, `secret_ready`, `secret_ready_iff_slice` | models.v |
| U1 | `sliced_init_gated` | models.v |
| U2 | `set_pending_gated` | models.v |
| U3 | `sliced_service_gated` | models.v |
| U4 | `initiate_next_gated` | models.v |
| U5, U6 | `state_step_gated`, `sliced_run_gated` | models.v |
| U7 | `secret_gated_at_boundary_ready` | models.v |
| R8 | `set_pending_NI`, `set_pending_EP` | noninterference.v |
| R9 | `sliced_service_NI` (all pairs) | noninterference.v |
| R11 | `initiate_next_NI_on` (via `state_rel_bot`) | noninterference.v |
| R10, R12 | `sliced_output_NI_on`, `fv_NI_step_sum_on` | noninterference.v |
| R14 | `model_sliced_NI` via `sta_NI_pred` with `P := secret_gated` | noninterference.v |

No hypothesis on `runtime`. Removed: `restore_invariant`, `timeslice_live`,
`sliced_inv`, `choice_inv`, `choice_state`, `restore_invariant_id`,
`restore_invariant_noop`, `slice_at_boundary_ge2`, `sta_comp`, `f_EP_comp`.
`model`, `state_step` and `initiate_next` lost their `restore_invariant`
parameter. The traces are unchanged except that every counter value in the
state rows shifts by one. `Print Assumptions` (ci/axioms.v, which now also lists
`sta_NI_pred` and `sliced_run_gated`): only `d` and `L`.
