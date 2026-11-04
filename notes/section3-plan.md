# Plan: restructure Section III around the layers of the process

Written 2026-11-04, updated the same day: the output update is now in `g` (the user
chose to keep it). Approved and carried out 2026-11-04 in `tex/sections/model.tex`,
uncommitted at the time of writing. The state-update figure was then cut at the user's
request, so the figure numbers after Fig. 4 moved down by one. The section was then
trimmed and split: Definition 3 and the user view are now Section IV,
`tex/sections/attacker.tex`, and the visible equivalence is a former in Definition 2.
The listings of `sta`, `loop`, `pool_input`, the slot and `initiate_next` were cut.

## The state updates, as the code now has them

`reactive_system`:
`loop (map id (fun x => inr x.2) (sta input_update output_update v (map pool_input id (maybe p))))`

- `f` = `input_update`: `set_pending` on `inl`, identity on `inr`.
- `g` = `output_update`: `initiate_next o \o (advance_policy \o observe_policy o)`.
- The input type of `f` stays a sum because `loop` forces input type = output type.
  The `inr` case exists only for the fed-back output, which finds the state updated.
- The loop is still needed: a `swi` opens only on an input. After an output, the only
  way to tell the pool the next pid is an input, and only `loop` supplies one. `loop`
  is atomic (`reduce_loopO`), so no input arrives between the update and the feedback.

Verified in Rocq: `make` and the axiom check are green. A scratch proof, not in the repo,
shows the model has the same traces with the output update in `f` or in `g`.
`run_states_model` (`concrete_system.v`, new) shows row n of `run_states es` is the state the model
holds after n+1 events of a trace `es` at `public_equiv`, which covers the four runs.

## The layers, inside out, as the code has them

1. `swi` gate around `maybe` around each process, one per slot
2. `par` of the slots: the pool
3. `maybe`
4. `map pool_input id`
5. `sta input_update output_update init`
6. `map id (fun x => inr x.2)`
7. `loop`
8. `map inl (inr_or_def no_output)`: this is `model`
9. `map id parse_output`: this is `userview`

## Points where the outline needs care

- **Loop:** its first job is delivering the pid. Without it no switch reopens after
  the first step. The private user's input is the second job.
- **Layer 6:** the outline omits this map. It sits inside the loop because `loop` needs
  equal input and output types: it drops the state and tags the output `inr`. That same
  constraint forces the sum.
- **`maybe`:** there are two, per slot (only the private user gets an input) and on the
  pool. The pool's one is the proof device: the behaviour could be had with a pid that
  names no slot, but that input would not be unobservable, so the `PU` side condition
  of `map` would fail. Reasoned, not tried. It discards every interrupt, the timer's too.
- **U, T, S:** currently defined in III-B through the output tuple. They move to the
  processes subsection.

## New order

- **III-A Interrupt handling (new).** The mechanism with no calculus: an interrupt
  sets a pending bit; a handler starts when pending and unmasked; masks make handlers
  non-preemptive; on completion control returns to the interrupted process, or to the
  scheduler if the reschedule flag is set; the timer drives scheduling; the disk
  interrupt is the secret. NOP as a handler nothing raises, used in IV.
- **III-B The processes.** Grouped U (two users, scheduler), T, S (disk, NOP).
  `ir_handler` listing, kept.
- **III-C The pool.** Layers 1 to 3. Gating, one step per selection, the six-tuple.
- **III-D The state.** Layers 4 and 5. Fields mapped back to III-A. `f` records an
  interrupt as pending and decides nothing. `g` is the policy: the holes for IV are
  `observe_policy` and `advance_policy`, followed by `initiate_next` and its four rules.
  Fig. 5 (parked).
- **III-E The loop.** Layer 7, and layer 6. Its two jobs. Here the `inr` case of `f`
  gets its explanation: the fed-back output finds the state already updated, and the
  pool reads the new pid from it. The private user's input, absorbing the orange note in
  III-A today.
- **III-F The generic model.** Layer 8, `model` listing, interrupt policy, then
  Definition 3 (`I`, `O`) and the attacker's view.
- **III-G The user view.** Layer 9, Definitions 4 and 5. Closes with why the private
  user's input matters: it makes the disk interrupt visible in this trace.
- The parametricity paragraph stays at the end of III-F or III-G.

## Knock-on changes from moving the update into g

- `model.tex`: the `model` and `reactive_system` listings, `step_sum` (l. 175) and the
  paragraph on `state_update` and `map id snd` (ll. 247-250). These go in the rewrite.
- `fig-update.tex` (Fig. 5): its caption cites `state_step`, and the figure has to show
  `f` and `g`. It is parked, so its change waits for the user.
- `proof.tex`: "two lanes of `state_step`" and `fv_NI_step_sum_on` (ll. 165-166) become
  the `f` and `g` obligations of `sta_NI_pred`. `map id snd` is named at ll. 66 and 82.
  "Output lane" (ll. 168, 236, 261, `fig-lane.tex`) could stay as a name for `g`, or go.
- `mechanisation.tex` l. 31: "computed by the model's own transition" can now cite
  `run_states_model`.
- `mechlinks.tex`: regenerated by `mechlinks.py`. `step_sum`, `fv_NI_step_sum`,
  `fv_NI_step_sum_on` and `f_EP_step_sum` are gone, so any `\m{}` citing them must go.

## Knock-on changes from splitting models.v

`models.v` is now `generic_model.v`, `concrete_system.v`, `model_immediate.v` and
`model_sliced.v`. tex/ has not followed yet:

- **The paper does not build until this is fixed.** `mechlinks.py` l. 16 lists `models.v`
  in `FILES`, and `.latexmkrc` stops if the script fails. Replace it with the four files,
  in dependency order.
- `mechanisation.tex` l. 22: the Tab. I row for `models.v` and its `\mechlines{models.v}`
  become rows for the four files.
- Source comments naming `models.v`: `fig-ordinary.tex` l. 32, `fig-sliced.tex` ll. 6, 30,
  `fig-lane.tex` l. 3, `fig-update.tex` l. 1, `fig-model.tex` l. 58. "Section 11" there is
  now the traces in the policy files.
- `tex/README.md` l. 11 uses `\mechfile{theories/models.v}{models.v}` as its example.

## Other knock-on changes

- Labels kept on their new homes: `sec:pool`, `sec:global-state`, `sec:state`,
  `sec:parameters`. `sec:interface` needs splitting: "three kinds of step" in IV and
  the disk-is-unobservable reference in V point to different places now.
- V's opening layer list follows the same order and could cite III's layers. Its todos
  on naming each map would then be largely answered.
- Remove the todo at the top of model.tex and the orange note, since this covers both.
- Definition numbers stay in order; figure sources may move; recheck float pairs.
