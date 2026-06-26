# Plan sketch — sta_NI' / swi_NI' over a reachability-restricted relation

Iterable sketch; refine as we go. See `contradiction.txt` for the why.

## Where we are
- `eqpair_P (eqpair_R …) P` ≡ `eqpair_R` (vacuous; proved: `dis_eq`, `rel_eq`,
  `premise_collapses`). Dead.
- `eqpair_dom` (direct-predicate lawful combinator) is built and `Qed`'d in-session,
  but with `P = image(f)` its premises (`f_EP` ∧ `Hclo`) are contradictory for
  non-surjective `f` on a disclosed input (`contradiction.txt` §1–4).
- **Fix:** use `P = reachability` (closed under `f` AND `g`), relax `f_EP` to that
  domain, thread the invariant through `lthread`. Then the contradiction dissolves
  (`contradiction.txt` Correction section).
- Fallback if the relation route stalls: domain-indexed `NI_dom` (no `Hclo`).

## Already proven in-session — verified scripts saved in `current_files/snippets.v`
That file holds the ready-to-paste blocks (do NOT rely on chat history):
- `eqpair_dom` combinator (`Defined`) + the `Arguments` line to add.
- `aware_false_closure` (`Qed`) — bool-side closure from `aware true`.
- `swi_NI'_shape` — the `swi_NI'` statement, type-checks (proof `Abort`ed/TODO).
- `dis_eq` / `rel_eq` / `NI_ext` / `premise_collapses` — the collapse sanity lemmas.
- `sta_conv_dom` — converse lemma over `eqpair_dom` (assembled from the Qed'd
  `eqpair_P` version; re-check when pasting).
Caveat noted in the file: those use `P = Pf = image(f)`; switch `P` to reachability
(steps 2–3 below). `eqpair_dom` is generic in `P` and is reused unchanged.

## Steps (relation route)
1. **Add `eqpair_dom` + `Arguments eqpair_dom {V I} VRel IRel P Hclo`** to `current.v`.
   (Implicit args bite otherwise — do this first.)
2. **Define reachability predicate** `P_reach : [V] -> Prop` (or on pairs `(w,i)`):
   `w = v0 ∨ (∃ i v', f i v' = w) ∨ (∃ o v', g o v' = w)`. Decide pair- vs
   state-level. If not `VRel`-closed, define `P := VRel`-saturation (closed by
   construction) and prove `Hclo` trivially.
3. **Relax `f_EP`** to `dis IRel l i -> P v -> rel VRel l (f i v) v`. Adjust the
   `sta_NI'` signature to take this + the `Hclo` for `P`.
4. **Strengthen the forward decomposition / `lthread`** to carry "every threaded
   state ∈ P" (preserved by `v0`, `f`, `g`). This is the main new work; it feeds the
   relaxed `f_EP` at the surgery sites.
5. **Re-derive `sta_NI'` over `eqpair_dom P`** (adapt current `sta_conv'`/`sta_NI'`):
   - clause 1: `eqpair_dom` left branch (`rel_refl`, `Hii`) — no `P` needed.
   - clauses 2/3: discharge `dis = dis IRel ∧ P (w,i)` from the lthread reachability
     invariant + `Hclo`; handle the `insert` out-of-range case (`n > size t ⇒
     insert n a t = t`, short-circuit).
6. **`aware_false_closure` + `swi_NI'` statement** (already done) — land them.
7. **`eqpair_dom` map-congruence lemma** (`f_NI`/`f_PU` threading `eqpair_dom P` →
   `eqpair_dom Q` through a map's input fn) — keystone for chaining `sta`→`map`→`swi`.
8. **Cleanup**: remove `eqpair_P`, unfinished `collapse_test`; `rocq_compile_file`
   + `rocq_assumptions`.

## START HERE — gating decision before any coding
**Answer Q2 first; it decides whether the entire relation route is worth pursuing.**
The reachability restriction only helps if the states `p` actually mishandles lie
OUTSIDE the `VRel`-closure of the reachable set — i.e. `p`'s bad states must be
`VRel`-separated from reachable states. If they are NOT (some bad state is
`VRel`-related to a reachable one), the `VRel`-saturation pulls them back in, the
restriction gains nothing, and the relation route (`eqpair_dom`) is dead for this
model — **switch to the `NI_dom` domain-indexing fallback, which needs no `Hclo`.**
Do not paste/instantiate any of the heavy steps (2–7) until Q2 is settled.

## Open questions to resolve early (cheapest first)
- (Q2) **[GATING]** Are `p`'s mishandled states `VRel`-separated from the reachable
  set? If not → abandon the relation route, use `NI_dom`. Answer before steps 4–7.
- (Q1) Is `P_reach` `VRel`-closed in the model, or must we saturate? (decides step 2)
- (Q3) Does relaxed `f_EP` actually discharge the `n=0` `lthread` step
  `rel VRel l v (f i v)` given the reachability invariant reaches that `v`?

## Files
- `current_files/current.v` — all defs/lemmas.
- Reuse from `NonInterference.theorems`: `map_NI`, `aware`, `eqmaybe_swi`,
  `swi_trace`, `swi_conv`, `dis_rel_dis(2)`, `myrel_rule1/2`, `rel_refl/sym/trans`,
  `NI_reduceI/O`, `lthread_*`, `f_EP`, `f_NI`, `f_PU`.

## Verification
`rocq_compile_file current_files/current.v` clean; `rocq_assumptions` on
`sta_NI'`/`swi_NI'` shows only standard/imported axioms.
