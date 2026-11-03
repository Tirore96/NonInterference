# Section V: the state update, restore_invariant, and the plan

Working notes from the review of Section V (2026-11-03). They record what the
Rocq proof actually does with `restore_invariant`, the insights from the
discussion, and the plan for restructuring Section V. The red `\todo` comments in
`tex/sections/proof.tex` are still in place; this file is the longer record.

## 1. Where the state update sits in the proof

`model_sliced` is `reactive_system` (Section III-E): an outer `map`, a `loop`, an
inner `map id snd`, then `sta f g v (map pool_input inr (maybe pool))`. Once the
outer map and the loop are peeled off, the goal is `sta_NI` (Theorem 1(3)), with two
obligations on the state update `f = state_step`:

- `f_EP` (PE in the paper): an unobservable event leaves the state related to
  itself. Only a disk interrupt is unobservable, and `set_pending` only sets a
  private bit, so this is trivial, but illustrative: it is why an interrupt may
  only record that it is pending.
- `fv_NI` (NI(≐E, ≐V, ≐V)): related events take related states to related states.
  `state_step = step_sum set_pending (output lane)`, and ≐E never relates an input
  to an output, so `fv_NI_step_sum` splits it by cases on the event:
  - input: `set_pending` writes one private bit; trivial;
  - output: the output lane, a composite of six stages. This is where all the
    work is.

## 2. The output lane: six stages and their obligations

Order of application (`state_step`'s output summand is
`initiate_next restore_invariant ∘ sliced_service ∘ check_scheduler`, and
`sliced_service = check_slice_count ∘ check_handler_completed ∘ initiate_ir`):

| # | stage | reads | writes |
|---|---|---|---|
| 1 | `check_scheduler` | scheduler's output (public) | current pid |
| 2 | `initiate_ir` | timer handler's output (public) | counter, reschedule flag |
| 3 | `check_handler_completed` | counter | at a boundary: unmask disk/NOP, mask timer, NOP pending := true |
| 4 | `check_slice_count` | counter | tick; at `Some 0`: mask disk/NOP, unmask timer, counter := None |
| 5 | `restore_invariant` | counter, disk mask | NOP pending, masks (see §4) |
| 6 | `initiate_next` (the choice) | masks, pending bits, pid, prev pid, reschedule flag | pid, prev pid, masks, one pending bit |

Stages 1–5 read only public fields and public output slots, so on related
arguments they write the same values (private bits included): routine.
Stage 6 reads the private pending bits: the only non-trivial one.

`fv_NI_comp` proves the composite stage by stage. Each stage's obligation
quantifies over *all* pairs of related states, so the only thing that passes from
one stage to the next is relatedness. What an earlier stage establishes about its
result (e.g. stage 3 just made NOP pending; stage 4 just masked disk/NOP) is
forgotten. This is the "forgetting" that `restore_invariant` repairs.

Note: `restore_invariant` is applied once, inside `initiate_next`, after rule 1
(all masks set) and before rules 2–4. It is stage 5 above and appears nowhere else.
`model_immediate` instantiates it with `id`.

## 3. How the proof of `initiate_next` uses restore_invariant: case by case

Not as a chain: the proof of stage 6 (noninterference.v, from "initiate_next: the
outermost stage") splits into cases, and each case uses a different fact.
Throughout, `v ≐V v'` at ⊥, and `w = restore_invariant v`, `w' = restore_invariant v'`.

- **A. Rule 1 (all masks set).** Masks are public, so `masks_set v = masks_set v'`:
  both states continue, or neither. No use of restore_invariant.
- **B. Timer ready.** `ready_cases2P` first needs `ir_ready w timer = ir_ready w'
  timer`. Timer pending and timer mask are public, and restore_invariant writes the
  timer mask from the (public) counter, so they agree. Both start the timer handler.
  Use of restore_invariant: trivial (only because the goal is about w, w').
- **C. Timer not ready.** `ready_aux2`: each of w, w' has the disk handler first,
  the NOP handler first, or no secret handler ready. Nine combinations:
  - **C1. Secret in both (disk/disk, disk/NOP, NOP/disk, NOP/NOP).** Both start a
    handler: the pid becomes `inl b` with `b` private, all masks are set (public,
    equal), one pending bit is cleared (private). Related. **No use of
    restore_invariant.** Different secret handlers in the two states are
    explicitly allowed: which one runs is private.
  - **C2. Secret in one, none in the other (4 combinations).** Closed by
    `exfalso`, the only essential use of restore_invariant. Why this case must be
    impossible: the state with a ready secret handler starts it and enters S (pid
    `inl _`), while the other falls through to rule 3 or 4 and returns to, or
    continues, a user process or the scheduler (pid `inr _`), i.e. stays in U.
    The current pid's tag is public (≐^{H∘} + ≐^L), so the two states would be
    unrelated, and the attacker would see S in one run and U in the other. Why it
    is impossible after restore_invariant: if a secret handler is ready in w, the
    disk or NOP handler is unmasked, so (by §4) a slice is open; then the NOP handler
    is pending in both w and w' and the NOP mask equals the disk mask, which is
    public; so the NOP handler is ready in w' too. Contradiction.
  - **C3. None in both.** Rules 3/4: `is_handler_pid` (pid tag, public) and
    `get_re_sched` (public) agree; restore_invariant does not touch them. Use:
    trivial.

**Key insight for the paper:** restore_invariant does not make the same secret
handler run in both states (C1 explicitly allows disk in one and NOP in the
other). It makes *both run a secret handler, or neither*: otherwise one state
enters S while the other returns to U, and the pid's public tag exposes it.

## 4. The invariants: `sliced_inv`, `choice_inv`, and restore_invariant

"Open slice" = `timeslice_live`: the counter is `Some n` with `n > 0`.
(`Some 0` means the slice is closing; `None` means no slice.)

- **`sliced_inv v`** (models.v): the invariant **between steps**, true of every
  state the sliced policy reaches (`sliced_run_inv`, proved by `sliced_inv_step`:
  every event preserves it).
  1. NOP mask = disk mask;
  2. in an open slice, all masks are set (a handler is running);
  3. outside a slice, the disk mask is set (hence, by 1, the NOP mask too).
- **`choice_inv w`**: the invariant **at the choice point**, i.e. on the state
  `initiate_next` receives, after `check_scheduler` and the service policy
  (`choice_state o v`). Same as `sliced_inv`, except that inside an open slice it
  also allows a **handler boundary**: the masks of disk and NOP are open, the
  timer is masked and the NOP handler is pending (stage 3 has just queued the
  filler).
  1. NOP mask = disk mask;
  2. in an open slice: all masks set, **or** (NOP pending ∧ timer masked ∧ disk
     and NOP unmasked);
  3. outside a slice: disk masked.
  `choice_inv_step`: `sliced_inv v → choice_inv (choice_state o v)`.
- Why two: between steps, a handler is always running inside a slice; the service
  policy then runs before the choice and, at a boundary, opens the masks and queues
  the NOP handler. So the state the choice sees has one more shape than the states
  between steps.
- **`restore_invariant w`** writes into `w`: in an open slice, NOP pending := true
  and timer mask := true; outside, disk mask := true and NOP mask := true; in both,
  NOP mask := disk mask. Every state it returns satisfies the shape `initiate_next`
  needs whenever not all masks are set.
- `restore_invariant_id`: `choice_inv w ∧ ¬masks_set w → restore_invariant w = w`.
  With `choice_inv_step` and `sliced_run_inv` this gives Theorem 5
  (`restore_invariant_noop`): on every reachable state where it is applied, it is
  the identity.

## 5. Insights recorded

- **Theorem 5 is not used by the non-interference proof.** `restore_invariant_noop`
  appears in noninterference.v only in a comment; no lemma depends on it. It shows
  that the hook does not change the model's behaviour (so Theorem 4 is about the
  sliced policy as intended), which is more than naming, but secondary.
- **What is forgotten** is the link between the counter and the secret handlers'
  bits (§4); stage-by-stage composition passes only relatedness.
- **Restricting ≐V is impossible** (a characterised equivalence is reflexive on
  every value); **arguing over reachable states only** would lose the
  per-constructor structure.
- **Simplification idea: NOP pending := true unconditionally** in restore_invariant.
  - For non-interference it works and likely simplifies C2: after it, the NOP
    handler is always pending and its mask equals the disk mask, so a secret
    handler is ready exactly when the NOP mask is clear, which is public. The
    counter no longer matters for this argument.
  - **It breaks Theorem 5 as stated**: outside a slice a reachable state can have
    the NOP pending bit clear (the NOP handler cleared it when it ran the last
    filler), and restore_invariant would set it, so it is no longer the identity.
    Observable behaviour is unchanged (NOP is masked outside a slice, and the next
    slice sets the bit anyway), so Theorem 5 would have to become a statement about
    behaviour, not an identity.
- **Predicate instead of function (to explore).** Remove restore_invariant from
  the model; make the invariant an assumption of the proof and a theorem that every
  stage preserves it.
  - Gains: no proof-only hook in the model; `model` loses a parameter; Sections
    III-D/E and IV get simpler; Theorem 5 becomes "the invariant is an invariant"
    (pieces exist: `sliced_inv_step`, `choice_inv_step`, `sliced_run_inv`).
  - Costs: `sta_NI` quantifies over all related states, so a new composition
    theorem is needed: if the initial state satisfies P and the state updates
    preserve P, it suffices to prove `fv_NI` (and `f_EP`) for related states that
    both satisfy P. Inside the lane, `fv_NI_comp` needs a pre/postcondition
    version, since the condition at the choice (`choice_inv`) differs from the one
    between steps (`sliced_inv`). The forgetting moves into those conditions, so it
    removes less than it first seems, but it pushes an essential part of the proof
    into the metatheory, which is interesting in itself.
  - New theorems go at the bottom of theorems.v (prior work above stays untouched).

## 6. Plan for Section V (keep)

Restructure V-B around `sta`:
1. Route the reader: after peeling off the outer map and the loop, the goal is
   `sta_NI`.
2. Its obligations: `f_EP`, trivial but illustrative (an interrupt only sets a
   private bit); then `fv_NI`.
3. `fv_NI` by cases on the event: input (trivial, `set_pending`); output (the six
   stages of §2), leading to the forgetting story, possibly in its own subsection
   (decide when there is a draft).
4. The overview of the six stages' obligations (§2), and the case analysis of
   `initiate_next` (§3), including why C2 must be impossible (S vs U, public tag).
5. Theorem 5 last, as the secondary result that the hook changes nothing.

The function-vs-predicate decision (§5) changes how steps 3–5 are told; draft with
the function, or settle the predicate first.
