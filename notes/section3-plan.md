# Plan: restructure Section III around the layers of the process

Written 2026-11-04. Nothing in tex/ has been changed for this yet. Fig. 5 is parked.

## Why output updates go through the loop

From the rules of Fig. 2 (reasoned from the rules, not tried in Rocq):

- The loop is needed: a `swi` opens only on an input. After an output, the only way
  to tell the pool the next pid is an input, and only `loop` supplies one.
- Running the output update in `f` is not needed. `loop` emits `(g o v, o)` from `sta`
  and then feeds `o` back as an input. `map id snd` drops the emitted state. So doing
  the output lane in `g`, with `f` the identity on outputs, gives the pool the same
  `(new state, o)`. Same states, same outputs.
- The proof gains nothing from `f` either. PE only constrains interrupts, since an
  output is never unobservable, and the NI obligation on the output lane is the same.
- No recorded rationale found in notes or git messages. It looks historical.

Possible change: `f` = `set_pending` on `inl`, identity on `inr`; `g` = the output lane
on `T_out`; move the `inr` tag out of `sta`:
`loop (map id (inr \o snd) (sta f g v (map pool_input id (maybe p))))`.
Then `g` carries the policy and `sliced_output_NI_on` is exactly its `sta_NI_pred`
obligation. Cost: `reactive_system`, `state_step`, the trace tactics and the map layers
of `model_sliced_NI`. Size unknown until tried.

## The layers, inside out, as the code has them

1. `swi` gate around `maybe` around each process, one per slot
2. `par` of the slots: the pool
3. `maybe`
4. `map pool_input inr`
5. `sta state_update (fun _ v => v) init`
6. `map id snd`
7. `loop`
8. `map inl (inr_or_def no_output)`: this is `model`
9. `map id parse_output`: this is `userview`

## Points where the outline needs care

- **Loop:** its first job is delivering the pid. Without it no switch reopens after
  the first step. The private user's input is the second job.
- **Layer 6:** the outline omits `map id snd`. It sits inside the loop because `loop`
  needs equal input and output types. That same constraint forces the sum.
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
- **III-D The state.** Layers 4 and 5. Fields mapped back to III-A. `f` and `g`, with
  the holes for IV. `initiate_next` and its four rules. Fig. 5 (parked).
- **III-E The loop.** Layer 7, and layer 6. Its two jobs. The private user's input,
  absorbing the orange note in III-A today.
- **III-F The generic model.** Layer 8, `model` listing, interrupt policy, then
  Definition 3 (`I`, `O`) and the attacker's view.
- **III-G The user view.** Layer 9, Definitions 4 and 5. Closes with why the private
  user's input matters: it makes the disk interrupt visible in this trace.
- The parametricity paragraph stays at the end of III-F or III-G.

## Knock-on changes

- Labels kept on their new homes: `sec:pool`, `sec:global-state`, `sec:state`,
  `sec:parameters`. `sec:interface` needs splitting: "three kinds of step" in IV and
  the disk-is-unobservable reference in V point to different places now.
- V's opening layer list follows the same order and could cite III's layers. Its todos
  on naming each map would then be largely answered.
- Remove the todo at the top of model.tex and the orange note, since this covers both.
- Definition numbers stay in order; figure sources may move; recheck float pairs.
