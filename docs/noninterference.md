# NonInterference — proof / security-relation documentation

*Prose companion to [`theories/noninterference.v`](../theories/noninterference.v).*

**Purpose.** [`models.md`](models.md) explains WHAT the three models are. This
file explains WHY the good model is non-interfering and the bad one is not, stated
in terms of the security relations (`cRel`s, *characterised equivalences*): which
relation each interface carries, what "public" and "secret" mean formally, and the
one genuinely hard proof obligation — that the state relation is preserved by the state transition
(`fv_NI`), which is where the compositional structure of `state_step` and
`bool_coding` earn their keep.

Everything here is read off the definitions in
[`theories/definitions.v`](../theories/definitions.v) and
[`theories/noninterference.v`](../theories/noninterference.v).

> **Logical foundations.** The development imports classical logic —
> `Require Import Classical` at [`theories/theorems.v:739`](../theories/theorems.v).
> The law of excluded middle is used in one place, the switch non-interference
> lemma `swi_NI'`, because the `aware` predicate is not constructively decidable
> in the logic (a decision procedure could be used instead). Everything else is
> constructive.

## Contents

1. [Characterised equivalences (`cRel`): the framework and levels](#1-characterised-equivalences-crel-the-framework-and-levels)
2. [Base relations: `publicRel`, `privateRel`](#2-base-relations-publicrel-privaterel)
3. [Composite relations](#3-composite-relations)
4. [The model interfaces: `in_rel`, `out_rel`, `final_out_rel`](#4-the-model-interfaces-in_rel-out_rel-final_out_rel)
5. [`model_bad` is not non-interfering](#5-model_bad-is-not-non-interfering)
6. [`model_good` and `wrapped_model_good` are non-interfering](#6-model_good-and-wrapped_model_good-are-non-interfering)
7. [The state relation and `fv_NI` — the hard part](#7-the-state-relation-and-fv_ni--the-hard-part)
8. [Model limitations](#8-model-limitations)


## 1. Characterised equivalences (`cRel`): the framework and levels

A `cRel` over a Coq type `A` ([`definitions.v`](../theories/definitions.v)) is a
record whose two key fields are

```text
rel l x y   x and y are indistinguishable to an observer at level l
dis l x     x is "secret" (may be varied freely) at level l
```

`rel l` is required to be an equivalence, and `dis` *characterises* it — hence the
name — through the field

```text
dis l a0 -> forall a1, dis l a1 <-> rel l a0 a1
```

that is, if `a0` is secret at `l` then its `rel l`-equivalence class is exactly the
set of values secret at `l`. The remaining two fields are monotonicity: both `rel`
and `dis` are inherited downwards along the level order, so a lower (more exposed)
observer distinguishes no more than a higher one.

Levels form a lattice with least element `⊥` (written `\bot`). `⊥` is the most
exposed observer — the attacker. `NI IRel ORel p` quantifies over every level; the
decisive case is `l = ⊥`, where secret inputs and outputs may be varied and NI
demands that `p`'s set of traces does not change. So "`p` is non-interfering"
means: a `⊥`-observer, watching only the public parts of `p`'s output, cannot tell
whether a secret input was present.


## 2. Base relations: `publicRel`, `privateRel`

Throughout, **public** and **private** are precise, opposite classifications:

- **public** = observable to *all* levels (compared by equality everywhere; never
  secret).
- **private** = *not* observable to `⊥` (secret at `⊥`, where the attacker may vary
  it freely; public — compared by equality — at every higher level).
- **secret** is the informal property "`dis` holds at the observer's level" — the
  thing NI lets vary.

**`publicRel A`**

```text
dis l x = False        rel l x y = (x = y)
```

A public value is never secret and is compared by exact equality at every level.
It can be neither inserted, removed, nor varied without an observer noticing.

**`privateRel A`**

```text
dis l x = (l = ⊥)      rel l x y = (l ≠ ⊥ ∧ x = y) ∨ (l = ⊥)
```

A private value is secret exactly at `⊥` (there any two values are related and
both count as `dis`) and public — compared by equality — at every higher level.
This is the "secret channel": at the attacker level `⊥` the value is free. The
syscall output and the secret handler outputs carry this relation; the interrupt
input carries a stricter custom relation (see `in_rel` in section 4).


## 3. Composite relations

**`eqpair IRel ORel : cRel [Times I O]`** — relate pairs componentwise:
`(a,b) ~ (a',b')` iff `a ~ a'` and `b ~ b'`.

**`eqpair_LR` / `eqpair_R`** — variants of `eqpair` that differ only in when the
*pair* counts as secret (`dis`). Plain `eqpair` is never secret as a pair
(`dis = False`); relatedness is purely componentwise. The gated variants make the
pair itself secret:

```text
eqpair_LR  the pair is secret at l iff BOTH components are secret at l
           (dis = dis IRel ∧ dis ORel).
eqpair_R   the pair is secret at l iff the RIGHT component is secret at l
           (dis = dis ORel); the left component's secrecy is irrelevant.
```

(`eqpair_L` is the mirror image, gating on the left component.) This matters for
the switch/handler pairs: when a component is secret, the pair as a whole may be
varied, so two related states can carry different values there.

**`eqsum IRel ORel : cRel [Sum I O]`** — relate a `Sum` tag-by-tag: `inl a ~
inl a'` iff `a ~ a'` (by `IRel`); `inr b ~ inr b'` iff `b ~ b'` (by `ORel`). An
`inl` is never related to an `inr`, at any level, and the sum itself is never
secret (`dis = False`) regardless of the component relations — so the *tag* is
always public, even when the payload underneath is not.

**`eqmaybe VRel` and variants (`eqmaybe_top` / `eqmaybe_false` / `eqmaybe_swi`)** —
relate `Option` values. On `Some`/`Some` they defer to `VRel`; the only difference
between the variants is a level-predicate `P` deciding *who can see `None`*. In
`eqmaybe_dis`, `None` is secret at `l` exactly when `¬P l`, i.e. `P l` = "the
observer at `l` can observe `None`":

```text
eqmaybe       P l = True        None is public: everyone can see it.
eqmaybe_top   P l = (l ≠ ⊥)     everyone but ⊥ can see None; None is secret
                                only at the attacker level ⊥.
eqmaybe_false P l = False       nobody can see None; None is secret at every
                                level (a value whose very presence is hidden).
eqmaybe_swi   P l = aware BRel  those who are "aware" per a Bool relation BRel
                                can see None; used to gate a switch branch.
```

The mixed case follows from the characterisation (section 1): `Some v ~ None` at
`l` iff *both* are secret at `l`, i.e. iff `¬P l` and `dis VRel l v`. So `None` can
stand in for `Some v` exactly when `v` is itself a secret the observer may not
see.


## 4. The model interfaces: `in_rel`, `out_rel`, `final_out_rel`

**`in_rel : cRel [T_in]`** = `TInterrupt_rel`, a CUSTOM relation (not
`privateRel`). Its secrecy predicate is

```text
ir_dis l ir = (ir = DiskInterrupt ∧ l = ⊥)
```

so only the disk interrupt is secret, and only at `⊥`. Unlike `privateRel` — where
at `⊥` *every* value is secret and mutually related — here just the disk interrupt
is free; every other interrupt (the timer interrupt in particular) stays public
and must be matched exactly, even at `⊥`. This is deliberate: the timer is a
public, scheduled event, so only the disk interrupt is a genuine secret input. NI
is exactly the guarantee that its presence cannot be inferred from the output.

**`out_rel : cRel [T_out']`** (full pool output, for `model_bad` / `model_good`)

```text
eqpair (eqmaybe publicRel)               public user output   (exact)
  (eqpair (eqmaybe privateRel)           syscall              (secret at ⊥)
    (eqpair (eqmaybe publicRel)          scheduler pid        (exact)
      (eqpair (eqmaybe_top privateRel)   handler output       (secret)
        (eqpair (eqmaybe_top privateRel) handler output       (secret)
          (eqmaybe publicRel)))))        handler output       (public)
```

The three handler-output components correspond to the three handler slots, in
order default/NOP, disk, timer: the first two are secret, the third is public.
That third slot is the TIMER handler: it reacts only to timer interrupts, which
are public scheduled events (see `in_rel` above), so neither the fact that it is
running nor what it outputs is secret. The disk slot is secret because the disk
interrupt is; the default/NOP slot must be secret too, because it is the disk
slot's indistinguishable partner — a slice step is filled by one or the other, and
an observer able to tell those two slots apart could tell which. The
public user output and the scheduler pid are public; the syscall is secret at `⊥`.

**`final_out_rel : cRel [T_out]`** (user-visible output, for `wrapped_model_good`)

```text
eqmaybe_false (eqsum publicRel privateRel)
```

Only the user-visible channel survives `parse_output`: a public user output on the
left (exact) or the secret syscall on the right (secret at `⊥`).


## 5. `model_bad` is not non-interfering

`model_bad_not_NI : ~ NI in_rel out_rel model_bad`.

The witness exhibits one `⊥`-trace that `model_bad` admits without the secret
input but not with it. Concretely:

- Take a trace the process admits that contains two outputs from the public user
  process (a run of two ordinary public requests).
- Insert a disk interrupt at the FRONT of the trace. This is legal at `⊥` because
  the disk interrupt is secret there (`ir_dis`), so NI requires the trace set to be
  unchanged by the insertion.
- Consuming the interrupt sets the disk pending flag. After the next public
  output, that pending flag causes the disk handler to be scheduled — so the step
  where we expected the SECOND public output instead runs the handler.
- The `⊥`-observer sees the difference directly: the public output component is
  `None` where the interrupt-free trace produced `pub_get'`.

So a secret input has changed the public projection of the trace: NI fails. (The
good model avoids this precisely because the disk handler runs on fixed, public
slice boundaries rather than in immediate response to the interrupt.)

> **Note on counterexample length.** The witness deliberately uses a short trace:
> the proof drives it by `inversion` on the reduction relation, which is expensive,
> so a long trace would be impractical to discharge.


## 6. `model_good` and `wrapped_model_good` are non-interfering

```text
model_good_NI         : NI in_rel out_rel model_good.
wrapped_model_good_NI : NI in_rel final_out_rel wrapped_model_good.
```

`wrapped_model_good = map id parse_output model_good`, and `wrapped_model_good_NI`
is obtained from `model_good_NI` by pushing the output through `parse_output`
(output weakening: `parse_output` maps `out_rel`-related outputs to
`final_out_rel`-related ones).

`model_good_NI` is assembled from the generic composition theorems for the process
algebra, applied to the concrete processes of [`models.md`](models.md). There is one
theorem per constructor, and the proof of `model_good_NI` is essentially the term
`model_good` read outside-in with each layer discharged by its theorem:

| layer of `model_good` | theorem | what it gives you |
|---|---|---|
| the outer `map inl (inr_or_def def)` and every interface rewiring | `map_NI` | `NI IRel' ORel p → NI IRel ORel' (map f g p)`, given `f_NI`/`f_PU` for `f` and `f_NI` for `g` |
| `loop` (the feedback tying output back to input) | `loop_NI` | `NI IRel IRel p → NI IRel IRel (loop p)` — note input and output relations must coincide |
| `sta` (the global state cell) | `sta_NI` / `sta_NI'` | `NI (eqpair_R VRel IRel) ORel p → NI IRel (eqpair VRel ORel) (sta f g v p)`, given `fv_NI` for both state updates — **this is where section 7 is discharged** |
| `maybe` (a slot or the pool idling) | `maybe_NI` | `NI IRel ORel p → NI (eqmaybe_false IRel) ORel (maybe p)` |
| `par` (laying the pool slots side by side) | `par_NI` | `NI IRel ORel1 p1 → NI IRel ORel2 p2 → NI IRel (eqpair ORel1 ORel2) (par p1 p2)` |
| `swi` (gating each slot on/off) | `swi_NI` / `swi_NI'` | `NI IRel (eqpair_LR BRel ORel) p → NI (eqpair_LR BRel IRel) (eqmaybe_swi ORel BRel) (swi b p)`, given awareness-or-obliviousness at every level |
| the leaves (`out o`) | `out_NI` | a constant process is trivially non-interfering |
| `parse_output` on top of `model_good` | `map_NI` again | output weakening, giving `wrapped_model_good_NI` |

Two things to read off the table. First, each theorem *derives* the composite's
relations from its parts' rather than taking them as given — which is why the
concrete relations of section 4 look the way they do: `out_rel`'s nest of `eqpair`s
is the shape `par_NI` forces on a pool output, and its `eqmaybe`s are what
`swi_NI` forces on a gated slot. Second, every one of these is mechanical for our
models *except* the `fv_NI` side conditions of `sta_NI`. That is the one genuinely
hard obligation, and it is section 7.

> The generic theorems in [`theories/theorems.v`](../theories/theorems.v) are a
> mechanisation of results from separate prior work, not a contribution of this
> development; only their statements are used here.


## 7. The state relation and `fv_NI` — the hard part

### 7a. `stateType_rel`: which state fields are public, which secret

```text
stateType_rel : cRel [stateType]
  = eqpair pids_rel bool_state_rel
    pids_rel       = eqpair (eqsum privateRel publicRel) publicRel
    bool_state_rel = eqpair publicRel (eqpair publicRel ic_rel)
    ic_rel         = eqpair hidden_pending (eqpair hidden_pending public_pair)
    hidden_pending = eqpair privateRel publicRel      (pending secret, MASK public)
    public_pair    = eqpair publicRel publicRel
```

Reading off the security classification of the state (the `stateType` layout is in
[`models.md` §4](models.md)):

- **masks: PUBLIC everywhere.** This is the formal content of "all masks are
  public": every mask bit sits under `publicRel`, so it must agree across two
  related executions.
- **pending bits of the two secret handlers (disk, default): secret**
  (`hidden_pending` pairs a private pending with a public mask); the timer
  handler's controller pair is public (`public_pair`).
- **`cur_pid`** (`Sum Bool Nat`, under `eqsum privateRel publicRel`): the `inl`/`inr`
  *tag* is public — `eqsum` never relates an `inl` to an `inr` (section 3), so
  whether a handler is running at all is visible. What is secret is the `Bool`
  *inside* the `inl`: at `⊥` `inl true` and `inl false` are related, so an observer
  cannot tell the disk handler from the default/NOP handler. The user/scheduler pid
  (`inr n`) is public. **`prev_pid`:** public.
- **`re_sch` and `ir_count`** (the time slice): public.

So across two `⊥`-related states, the masks, the slice, the scheduler/user pid and
`re_sch` must match; only the secret handlers' pending bits and the handler bit
inside `cur_pid` may differ.

### 7b. `fv_NI` and the composition-breakdown technique

`fv_NI IRel ORel VRel f` := for all `l`, all inputs `i ~ i'` (`rel IRel`) and all
states `v ~ v'` (`rel VRel`), the outputs are related:
`rel ORel l (f i v) (f i' v')`. The core obligation for the good model is

```text
fv_NI (eqsum in_rel out_rel) stateType_rel stateType_rel
      (state_step good_preroutine bool_coding)
```

— `stateType_rel` is closed under the state transition. `state_step` is a
composition ([`models.md` §5](models.md)), and `fv_NI_comp` discharges `fv_NI` of a
composition from `fv_NI` of the parts. Combined with
`fv_NI_step_left` / `fv_NI_step_right` (which lift a stage to the
`eqsum in_rel/out_rel` event), the obligation splits into one small, independent
goal per stage:

```text
state_step good_preroutine bool_coding  =
    initiate_next(bool_coding) ∘ handler_preroutine ∘ step1 ∘ step0
                    │                    │              │       │
   ─────────────────┴────────────────────┴──────────────┴───────┴───────────────
   stage                     lifted by        per-stage fv_NI obligation
   ─────────────────────────────────────────────────────────────────────────────
   step0 (input)             step_left        arriving interrupt sets a pending
                                              bit; related in ⇒ related states
   step1 (output)            step_right       scheduler pid is public, so the
                                              cur_pid update agrees
   handler_preroutine        step_right       slice bookkeeping reads only public
     (good_preroutine)                        ir_count / masks ⇒ agrees
   initiate_next(bool_coding) step_right      THE HARD ONE: related states must
                                              pick the SAME branch of "what runs
                                              next" — see 7c
```

- **Benefit:** each stage is a self-contained `fv_NI` goal.
- **Cost — and this is the crux:** each stage is proved over ALL pairs of related
  states, so it may not assume that its input came from the previous stage. The
  composition forgets the restricted, reachable subset the earlier stage produces.
  Every stage must therefore hold for states that never actually arise together.

### 7c. `bool_coding`: re-establishing the forgotten invariant

The reachable invariant that matters (good model; the substance is in
[`models.md` §8](models.md), `bool_coding` note): while the time slice is live, the
NOP (default) handler's pending bit is true, the disk and NOP masks are false and
the timer mask is true; and the disk and NOP masks are always toggled together
(kept in sync).

Because `fv_NI_comp` forgets this, `bool_coding` re-bakes it into the state just
before `initiate_next` runs:

- it ORs in a controller pattern derived from `timeslice_live` — which reads only
  `ir_count`, a PUBLIC field, so the pattern is equal across two related states —
  restoring "slice live ⇒ NOP pending, disk/NOP unmasked, timer masked";
- it forces the default (NOP) mask to equal the disk mask. On any state that
  already satisfies the invariant this is a no-op, but stated unconditionally it
  lets the `sta` non-interference argument assume the two masks are in sync without
  having to recover that fact from an earlier stage.

In effect `bool_coding` is the proof's way of writing the reachable-state invariant
back into the state, since the compositional `fv_NI` proof cannot carry it across
stages. That is why, in the pipeline above, the hard `initiate_next` stage can
assume related states take the same branch: `bool_coding` runs first and makes the
mask bits (which decide the branch) agree.


## 8. Model limitations

Two deliberate simplifications keep the NI proof tractable. Both (a) and (b) are
genuine limitations of the model, not of the technique, and both could in principle
be lifted at the cost of a harder `fv_NI` (section 7); (c) collects the remaining
modelling choices.

**(a) Only one secret interrupt.** The model has a single secret interrupt — the
disk interrupt. The NOP (default) handler is present purely for privacy: it exists
to be the indistinguishable partner of the disk handler, and has no interrupt of
its own. A richer model with several secret interrupts would need a correspondingly
richer indistinguishability argument.

**(b) Same-length handler execution.** Every handler runs for the same fixed number
of output steps. This is what lets all masks be public (7a): because handlers
finish on public time-slice boundaries rather than after a secret-dependent number
of steps, the mask bits never encode secret timing, so they can safely be compared
by equality.

The payoff is exactly in the final stage. With public masks, two related states
`v` and `v'` agree on all mask bits, so they take the SAME branches through
`initiate_next` ("what runs next"). `fv_NI` for that stage is then a same-branch
argument.

Making handlers variable-length — the more flexible design — would force the masks
to be private (a secret handler's running time would otherwise leak through the
public mask toggles). Then `v` and `v'` could take DIFFERENT branches in
`initiate_next`, and proving `fv_NI` across those diverging branches is
substantially harder. That trade-off — flexibility of execution time against the
difficulty of the final-stage `fv_NI` — is the reason the model fixes handler
length.

**(c) Further modelling choices, baked in rather than argued for.** These are not
known to be security-relevant, but a reader should see them:

- **One output step per selection.** In `process_pool` each slot's output is tagged
  with the constant `true`, which closes its switch after a single output. Every
  process is therefore cooperative and advances exactly one step per selection;
  preemption within a step is not modelled ([`models.md` §2](models.md)).
- **No interrupt nesting.** All masks are set while a handler runs, so a handler can
  never itself be interrupted. A design permitting nesting is out of scope.
- **Fixed sizes.** The pool is six slots and the time slice is `Some 4` — exactly
  two handler activations. Nothing in the argument turns on the specific numbers,
  but neither is it stated for a general slice length.
