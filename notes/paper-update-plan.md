# Plan: bring the paper up to commit 1240d04 (no restore_invariant)

Written 2026-11-03. The code changes this plan follows:
- `restore_invariant` and Theorem 5 are gone.
- The slice counter is a plain Nat: 0 means no slice, 1 is the closing step,
  n+2 means running.
- `check_scheduler` is folded into `initiate_next` as `apply_scheduler_choice`.
- The service stages are now `observe_timer_output` then `tick_slice`.
  `tick_slice` subsumes `check_handler_completed` and `check_slice_count`.
- `immediate_service` is renamed `observe_handler_output`.
- The proof goes through the new `sta_NI_pred` with the invariant `secret_gated`.

Background: `notes/invariant-departure.md`; `notes/section5-restore-invariant.md` §7.

Conventions: todo first, then fix. Blue `\changed{}` marks are used during review
and removed after. Edit with the Edit tool. Use "policy", not "design". Avoid
"X, not Y" phrasing.

## Decisions to take first

1. **Where `sta_NI_pred` is stated.**
   - (a) In II-D, as a new theorem right after Theorem 1. It is generic calculus,
     and it is our addition, like sums.
   - (b) In V-C, where it is used.

   Recommendation: (a). V then only *applies* theorems, VI lists it among our
   additions, and the intro's third contribution names it.
2. **Overview of the stage obligations: figure or table.** The user asked earlier
   for "an overview of the security obligation of each of the stages in this output
   chain".
   - A new figure in V-B would show the output lane as boxes, with the invariant
     between them, `secret_gated → [service_policy] → secret_gated_at_boundary →
     [initiate_next] → secret_gated`, and under each box the fields it reads and
     writes and its relational obligation.

   Recommendation: the figure. It replaces the two inline stage pipelines (III-D,
   IV-B) as the one picture of the lane, so those two can shrink or go.
3. **Should the history of `restore_invariant` appear in the paper?**
   Recommendation: no. The paper presents the final model. Cut VI's "Proof devices"
   paragraph, or replace it with one sentence: the model contains nothing that only
   the proof needs.
4. **Should `state_rel_bot` / `pub_view` appear?** ("at Lo, related iff public
   fields agree".)
   Recommendation: yes, one sentence in V-A. It makes "routine" exact: a stage
   that computes public fields from public fields is NI.

## Section by section

### III. An Operating System as One Process (model.tex)
- **III-C, the global state.**
  - Slice counter bullet: "the number of output steps until the slice closes; 0
    outside a slice".
  - Fig. 4 (fig-model.tex): the slice counter type changes from `Nat + 1` to `Nat`.
    Its shading stays public.
- **III-D, who runs next.**
  - Inline pipeline figure: the output step has two stages, `service_policy` then
    `initiate_next`. The scheduler choice is now the first thing `initiate_next`
    does. The "writes" labels need redistributing: the current pid moves under
    `initiate_next`.
  - Prose: three stages become two; drop the `check_scheduler` sentence.
  - Say once that `initiate_next` first adopts the scheduler's proposal.
  - `initiate_next` listing: drop the `restore_invariant` parameter and its `let`,
    and add `let v := apply_scheduler_choice o v in` as the first line, with a
    comment.
  - Delete "Between rules 1 and 2 … hook used only by the proof".
- **III-E, the generic model.**
  - The `model` listing loses `restore_invariant`.
  - Delete the paragraph "The remaining argument, restore_invariant, …"; the
    interrupt policy is now exactly the model's open arguments.
  - Last paragraph: "need no condition" now holds without the runtime exception.
    Check that nothing hedges on runtime = 1.
- **Old todo, model.tex:2** ("do a pass here, consider the handler just added").
  Unclear whether it is stale; ask the user.

### IV. Two Interrupt Policies (designs.tex, fig-ordinary.tex, fig-sliced.tex)
- **IV-A.**
  - `immediate_init` counter: `None` becomes `0`.
  - Listing and prose: `immediate_service` becomes `observe_handler_output`. Say why
    the name fits: it observes every handler's output, and the policies differ in
    which output they observe.
  - Delete "restore_invariant is the identity".
  - Fig. 5 caption: rename the stage.
- **IV-B.**
  - Rewrite the counter paragraph. 0 means no slice. Opening loads
    runs·runtime + 1: the runs, then one closing step. 1 is the closing step. The
    old argument for an option ("0 could not tell closing from closed") goes; the
    +1 is the answer to it.
  - `sliced_init`: counter `0`. Delete "Its counter, Some 0, is an empty slice …".
  - Inline pipeline: two stages, `observe_timer_output` → `tick_slice`. It could
    go entirely if decision 2 adopts the V figure; keep a minimal one here otherwise.
  - Listings:
    - `observe_timer_output` loads `(runs * runtime).+1`.
    - Replace the `check_handler_completed` listing with `tick_slice` (match on
      `0 | 1 | n.+2`, with `queue_secret_run` and `close_slice`).
    - Introduce `slice_at_boundary runtime m := runtime ∣ m`; the old
      `handler_completed` text becomes this.
  - Prose: rename everything; the filler explanation stays.
  - Delete the footnote about one-step handlers.
- **Fig. 7 (phases).**
  - State labels: U and T show counter `0`; S shows `n+1, …, 1`.
  - Arrows:
    - T→S: `observe_timer_output`.
    - The S self-loop: `tick_slice` (boundary: `queue_secret_run`).
    - S→U: "counter at 1: slice closes", `tick_slice` (`close_slice`).
  - Caption: "reaches zero" becomes "reaches its closing step"; the counter is
    loaded with runs·runtime + 1.
- **Fig. 8 (run-sliced).**
  - Counter rows become `0,0,0,0,0,0,4,3,2,1,0,0` in both runs, from
    `sliced_states_*`.
  - The "open" and "closing" braces stay where they are (steps 7–9 and 10). Check
    against the new values: 10 is the step with counter 1.

### V. The Security Proof (proof.tex) — the substantive rewrite
- **Intro and the layer bullets.**
  - The `sta` bullet now cites the invariant version: `sta_NI_pred` with
    P = `secret_gated`. Its obligations: P holds initially and is preserved by `f`
    and `g`; NI and PE of `f` are needed only on P-states.
  - Keep the existing red todos; they are about presentation and still apply. The
    one at l.87–90 (sta's `g` and the input equivalence) is now more relevant,
    since `sta_NI_pred` makes `g` and P explicit.
- **V-A, the state equivalence.**
  - Add the `pub_view` sentence (decision 4).
  - The NOP-pending bullet still holds as written.
- **V-B, the state update.**
  - Output lane = `initiate_next ∘ service_policy`, two stages, each proved
    separately (fv_NI_comp); `service_policy` itself splits into
    `observe_timer_output` and `tick_slice`. This answers the todos at l.164–168
    ("what is s?"): delete them once done.
  - Replace the six-item list with the stage overview (decision 2).
  - Keep the paragraph on the fatal case (secret handler in one state, none in the
    other).
  - Name the fact: `secret_ready_iff_slice` — when no handler is running, a secret
    handler is ready iff a slice is open. This answers the todo at l.196–198
    ("about to choose" is informal, give it a name).
  - Keep "the ordinary policy fails here and in the service policy", with the
    stage renamed.
- **V-C, renamed from "Restoring the invariant" to "The slice invariant".**
  Rewrite completely, in this order:
  1. The problem. NI quantifies over all related pairs, but the fact holds only
     inductively: true initially and preserved, established by no single step.
     This is not "composition forgets", as the old text claimed; even a one-piece
     proof meets the unreachable pairs.
  2. The tool: `sta_NI_pred`, referenced from II-D if decision 1 is (a).
  3. The invariant, as a Definition (`gated`, `secret_gated`,
     `secret_gated_at_boundary`). Say that `handler_boundary` is what
     `queue_secret_run` establishes, so the disjunction follows the `if` in
     `tick_slice`.
  4. The chain as Hoare triples: U2, U3, U4, a lemma for `sliced_run_gated`, and
     the bridge U7. Say which triple discharges which obligation of `sta_NI_pred`.
  5. The relational step for `initiate_next` under `secret_ready_iff_slice`.
  6. One sentence: the model is unchanged on reachable states and contains no
     proof-only code.

  Delete Theorem 5 (`thm:noop`), `c_o(v)`, the runtime ≠ 1 paragraph, and the
  `sliced_inv`/`choice_inv` paragraph.
- **V-D, gating.** Unchanged, apart from the existing todos. Recheck the wrapfigure
  (Fig. 9) placement after V-C changes length.
- **V-E, requirements.**
  - The todo says to cut this subsection; that is still the user's call.
  - If it stays, the second bullet's reference to `sec:restore` becomes the new
    V-C label.
  - The intro's second contributions bullet cites this subsection.

### VI. Mechanisation (mechanisation.tex)
- Tab. I: models.v row: "Thm. 5" becomes "the slice invariant".
- "Proof devices" paragraph: per decision 3.
- Add `sta_NI_pred` as our second addition beside sums, in VI or VI-B, saying that
  the original theorems are untouched.

### I. Introduction, and the abstract in main.tex
- Third contribution: add "a composition theorem for stateful processes under a
  state invariant".
- Check the abstract for any mention of the hook. (The grep found none in
  main.tex, but re-read it.)

### Cross-references and checks
- Labels to retarget: `thm:noop` (mechanisation.tex), `sec:restore`
  (proof.tex ×3, designs.tex ×2), `sec:update`.
- `mechlinks.tex` regenerates from theories/ via latexmk. Every `\m{…}` for a
  removed name must go, or the build warns: `restore_invariant`,
  `restore_invariant_noop`, `sliced_inv`, `choice_inv`, `check_scheduler`,
  `initiate_ir`, `check_handler_completed`, `check_slice_count`,
  `handler_completed`, `immediate_service`.
- Page budget: the body must end on p. 12. V-C gets shorter (no Thm 5, no runtime
  paragraph); the new figure costs about a third of a column.
- Build: `latexmk -g` in tex/; copy main.pdf back; verify figure and section
  numbers against the PDF.

## Order of work
1. Decisions 1–4 with the user.
2. III and IV: mechanical renames, listings, Figs. 4, 5, 7, 8 and the inline
   pipelines.
3. II-D `sta_NI_pred` (if decision 1 is (a)), then V-B and V-C.
4. VI, intro, cross-references; build and check the layout.
5. Review pass with blue marks; remove them on the user's OK; commit.
