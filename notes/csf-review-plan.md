# Plan: applying the CSF presentation review

Status: awaiting approval. Nothing below is applied yet. The 34 `\todo` comments in
`tex/` mark where each item goes. They are removed as they are done; your own open
todos (citations, AI acknowledgment, Ge et al., unwritten conclusion paragraphs) stay.

**Rule for the whole plan:** the other CSF papers inform only how we present things.
No definition, wording, example or result of theirs enters the paper. The only trace
of them is the Related Work citations, in our own words, checked against the paper.

Order: Rocq first, because the paper must not state a lemma the mechanisation lacks.
Additions come before trimming, so the page budget is measured against the final
content. After each stage: build, render the changed pages and look at them.

## Stage 1: Rocq, factor out the two hard steps

Only reorganises the proof of `model_sliced_NI` in `theories/noninterference.v`; the
theorem statement does not change.

- **State-cell lemma:** the `sta` step for any inner process, wrapping the
  `sta_NI_pred` block at lines 972-978. Roughly: if `p` is in
  `NI(state_type_equiv x_R events, out_equiv)`, then `sta input_update output_update
  sliced_init p` is in `NI(events, state_type_equiv x out_equiv)`. Straightforward:
  all its parts are already separate lemmas.
- **Slot lemmas:** the six slots are near-duplicate inline blocks (lines 1027-1250),
  four using awareness and two using obliviousness. Aim for one lemma per group,
  parametric in the slot's index and process. The paper's single display then becomes
  one lemma with two cases.
- **Fallback:** if the slots resist one generic statement, state a lemma per slot,
  with the paper's lemma as their conjunction. I will tell you if that happens.
- **Check:** `make`, `sh ci/check_axioms.sh`, regenerate `mechlinks.tex`. Update the
  stale paper numbers only in comments I touch.

## Stage 2: Section V (changes 1 and 2)

- Run-in head "Proof outline" on the opening chain; the displays and the prose between
  them stay. The two "hard step" sentences forward-reference the lemmas by name.
- State-cell lemma stated at the end of V-C, after the invariant lemma; the existing
  "obligations now follow" sentences become its proof.
- Slot lemma stated in V-D, with that subsection's displays as its proof.
- Short "Proof of Theorem 4" closing the section: chain, two lemmas, hypotheses on `p_n`.
- Move Corollary 2's proof to IV-B and cut it to its last sentences, matching
  Corollary 1. Section V then proves only Theorem 4, so its opening sentence changes.

## Stage 3: Notation and titles (layout)

- Calligraphic letters for the model's own equivalences: V, Q and F, like I, O, U.
  Update Figs. 9 and 11. Theorems 1 and 2 keep the calculus's overset notation.
- Decide `B`, `O_n`, `Y_n`, `I_n` by looking at the result: these are per-slot
  metavariables of Theorem 1's instantiation, so they may stay as they are.
- Readable names next to the Rocq links on Theorems 2-4, Corollaries, Definitions 6-7
  and the lemmas. The links stay.
- Proof environment for Corollary 1. Check Fig. 10 stays legible.

## Stage 4: Section VI, Related Work (changes 3 and 4)

- **Scope paragraph** in VI, from our own development only: Theorem 3 is for the
  concrete system and Theorem 4 is parametric; pool shape and slot count are fixed;
  the corollaries are not restated in the original's terms; listings are hand-typed.
  Sections VI-A and VI-B cover the departures and are not repeated.
- **"Generated" sentence:** you confirmed the figures came from an earlier session.
  The lemmas exist for the state rows of Figs. 5 and 8 (`immediate_states_*`,
  `sliced_states_*`), and `fig-sliced.tex` and `fig-ordinary.tex` cite them. No script
  is in the repo, so a reader could not rerun it. Reword to "the figures show these
  rows", and compare the rows against the lemmas once while there.
- Name the files holding the two lemmas; add a proof-size number only if it is honest.
- **Citations:** Zagieboylo et al. as one contrasting clause. Rafnsson and Sabelfeld
  (2014) and Vassena et al. (2017) one clause each. Verify entries via Crossref, and
  reread the cited passage before writing the clause.

## Stage 5: Wording and consistency

- Introduction: "one of them hard" aligned with Section V's two steps.
- Section IV: the cryptic clause after "never which secret handler ran", the awkward
  end of the user-view sentence, the "pays off here" filler, "Section V proves both".
- Background: thread from "the two obligations" to the two lemmas.
- `\cref{def:ni}` replaces the hard-coded "Definition 1".
- Conclusion: scope paragraph and "The model and a real system" kept apart.

## Stage 6: Page budget

Target: confirm the limit in the current CSF call first (my notes say 12 pages
excluding references and AI acknowledgment; double-blind). The body is about 14 pages
today, and needs room for your two conclusion paragraphs, so aim for roughly 2.3 pages
of cuts. The numbers below are estimates, measured as I go.

| Cut | Estimate (pages) |
|---|---|
| Introduction: one statement each of policy and result, departures to one line | 0.4 |
| Background: opening, prose after Definition 2, examples after the predicates | 0.5 |
| Section III: one listing for `model`, helper names no later section needs | 0.2 |
| Section V: repeated term listing; shorter Corollary 2 proof; notation savings | 0.3 |
| Section VI: Invariants paragraph, interrupt history, some of VI-B | 0.3 |
| **Total** | **about 1.7** |

These cuts alone probably do not reach the target. **I will stop and ask before any
larger cut.** Options then, in the order I would look at them: shrink Fig. 2 (a
full-width reduction-rules figure), condense VI-B further, or merge the state rows in
Figs. 5 and 8. I will not remove figures or subsections without asking.

## What this plan does not do

- Write your two conclusion paragraphs or the user-input todos.
- Change any theorem statement, the model, or the policies.
- Commit: I commit only when you say. I suggest committing the current state as a base
  before Stage 1, and one commit per stage after it, so each can be reviewed alone.
