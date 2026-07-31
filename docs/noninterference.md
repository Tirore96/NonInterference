# NonInterference — proof / security-relation documentation

*Prose companion to [`theories/noninterference.v`](../theories/noninterference.v).*

Where [`models.md`](models.md) describes the three models, this document gives the
security argument: the relations the proof is stated in, the classification each
interface receives, and how the two results are proved. It covers what "public" and
"private" mean formally, how the counterexample for `model_immediate` is built, how the
generic theorems compose to give `model_sliced`, and the single substantial proof
obligation — that the state relation survives the state transition (`fv_NI`), which
is what the compositional structure of `state_step` and the auxiliary `bool_coding`
exist to make manageable.

Definitions are as given in
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
5. [`model_immediate` is not non-interfering](#5-model_immediate-is-not-non-interfering)
6. [`model_sliced` and `model_sliced_userview` are non-interfering](#6-model_sliced-and-model_sliced_userview-are-non-interfering)
7. [The state relation and `fv_NI` — the hard part](#7-the-state-relation-and-fv_ni--the-hard-part)
8. [Model limitations](#8-model-limitations)


## 1. Characterised equivalences (`cRel`): the framework and levels

Every interface in the development carries a `cRel`
([`definitions.v`](../theories/definitions.v)) — a level-indexed relation
describing what an observer at each level can tell about values of that type. It
has two key fields:

```text
rel l x y   x and y are indistinguishable to an observer at level l
dis l x     x is distinguished at level l — the observer may not see it,
            so non-interference is allowed to vary it
```

Levels form a lattice; `⊥` (written `\bot`) is the least and most exposed level,
and is the attacker. Two further fields make both `rel` and `dis` monotone
downwards along the lattice, so a lower observer distinguishes no more than a
higher one.

The remaining field is what makes a `cRel` more than a pair of relations, and gives
it its name. `rel l` is an equivalence, and `dis l` is required to be exactly one
of its equivalence classes:

```text
dis l a0  ->  forall a1, dis l a1 <-> rel l a0 a1
```

Read left to right: once one value is distinguished at `l`, the values related to
it are precisely the other distinguished ones. So the distinguished values form a
single indistinguishable blob, and everything outside it is compared exactly. That
is the "characterised" in *characterised equivalence*: `dis` is not extra
information, it is a distinguished class of `rel`.

### What `NI` says

```coq
NI IRel ORel p := forall l, NI_l IRel ORel l p
```

and `NI_l` ([definitions.v:229](../theories/definitions.v)) is three clauses, all
quantified over traces `t`, positions `n`, and using `insert n (inl i) t` to place
an input `i` at position `n`:

| clause | statement | reading |
|---|---|---|
| substitution | `rel IRel l i i'` → `Trace (insert n i t)` → `Trace (insert n i' t)` | swapping an input for an indistinguishable one keeps it a trace |
| insertion | `dis IRel l i` → `Trace t` → `Trace (insert n i t)` | a distinguished input may be added anywhere |
| deletion | `dis IRel l i` → `Trace (insert n i t)` → `Trace t` | and removed again |

Traces are compared through `ORel` at level `l`, so the outputs an observer
"sees" are only determined up to `rel ORel l`. Together the clauses say: the set of
traces visible at `l` is unchanged by anything the observer at `l` is not supposed
to see. The decisive instance is `l = ⊥`. Note that the counterexample for
`model_immediate` (section 5) refutes the *insertion* clause — inserting a disk interrupt
into a legal trace does not leave a legal trace.


## 2. Base relations: `publicRel`, `privateRel`

Two words are used throughout, and they are not synonyms:

- **public** / **private** classify an *interface*. A public interface is compared
  by equality at every level and is never distinguished. A private interface is
  distinguished at `⊥` — the attacker may vary it freely — and compared by equality
  at every level above.
- **distinguished** is the per-level property `dis l x`. It is what
  non-interference is permitted to vary, and it is relative to a level: a private
  value is distinguished at `⊥` and not distinguished anywhere else.

("Secret" is used only informally, as a synonym for distinguished at the attacker's
level.)

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

**`in_rel : cRel [T_in]`** is `TInterrupt_rel`, defined directly rather than as
`privateRel TInterrupt`, because only *one* of the interrupts is secret:

```text
ir_dis l ir = (ir = DiskInterrupt ∧ l = ⊥)
```

Under `privateRel`, every interrupt would be distinguished at `⊥` — the timer
included — and non-interference would then also forbid the schedule from depending
on the timer, which `model_sliced` relies on. `TInterrupt_rel` distinguishes only
the disk interrupt, so the timer must still be matched exactly even at `⊥`. This
makes the theorem say the right thing: the timer is a public scheduled event, the
disk interrupt is the secret, and it is the disk interrupt's presence that cannot
be inferred.

**`out_rel Opub Opriv : cRel [T_out' Opub Opriv]`** (full pool output, for
`model_immediate` / `model_sliced`)

```text
eqpair (eqmaybe publicRel)               public user output   (exact)
  (eqpair (eqmaybe privateRel)           syscall              (secret at ⊥)
    (eqpair (eqmaybe publicRel)          scheduler pid        (exact)
      (eqpair (eqmaybe_top privateRel)   handler output       (secret)
        (eqpair (eqmaybe_top privateRel) handler output       (secret)
          (eqmaybe publicRel)))))        handler output       (public)
```

The three handler components are the three handler slots, in order default/NOP,
disk, timer. The timer slot is public: it reacts only to timer interrupts, which
are public scheduled events, so neither its running nor its output is secret. The
disk slot is private because the disk interrupt is, and the default/NOP slot must
be private too — it is the disk slot's indistinguishable partner, since a slice
step is filled by one or the other and an observer able to tell those two slots
apart could tell which ran.

**The choice of `eqmaybe` variant is where scheduling secrecy lives, and it differs
between the handlers and the private user process.** Both carry `privateRel`
payloads, but:

```text
sys slot  eqmaybe     privateRel    None is PUBLIC
                                    → that high_p produced an output is visible;
                                      only Syscall-versus-NOP is hidden

dfl, dsk  eqmaybe_top privateRel    None is distinguished at ⊥
                                    → at the attacker's level, a handler output is
                                      indistinguishable from no output at all, so
                                      *whether the handler ran* is hidden too
```

That difference is the formal content of "the leak is in the scheduling". For
`high_p` it suffices to hide the value, because when it runs is public anyway. For
the two secret handlers it is precisely the *fact of running* — the scheduling —
that must be hidden, and `eqmaybe_top` is what hides it: it lets `Some o` at a step
be related to `None`, so a run of the disk handler and a step where nothing
happened are the same observation. Section 6 shows the proof obligation this
creates.

**`final_out_rel Opub Opriv : cRel [T_out Opub Opriv]`** (user-visible output, for
`model_sliced_userview`)

```text
eqmaybe_false (eqsum publicRel privateRel)
```

Only the user-visible channel survives `parse_output`: a public user output on the
left (exact) or the secret syscall on the right (secret at `⊥`).


## 5. `model_immediate` is not non-interfering

`model_immediate_not_NI : ~ NI in_rel out_relC model_immediate`.

`model_immediate` is concrete throughout — a counterexample should exhibit a
single system, so it is instantiated at the concrete user processes and alphabets.

Non-interference requires, among other things, that inserting a secret input
anywhere in a trace leaves it a trace. The counterexample refutes that clause with
a two-step trace:

1. Start from `[out_get'; out_get']` — two ordinary requests from the public user
   process, which `model_immediate` admits.
2. Insert a disk interrupt at the front. The insertion is permitted because the
   disk interrupt is secret at `⊥` (`ir_dis`), so non-interference demands the
   result still be a trace.
3. It is not. Consuming the interrupt sets the disk pending bit. The first
   `out_get'` still goes through, because `initiate_next` runs on output events and
   the newly scheduled handler only takes effect from the following step. That
   following step belongs to the disk handler, so the second `out_get'` cannot
   occur: the public output slot carries `None` where the interrupt-free trace
   carried `out_get'`.

A secret input has changed what the `⊥`-observer can see, so `model_immediate` is not
non-interfering. The disk handler goes on to run its second step before control
returns to the public process, but the first displaced output is already enough.

`model_sliced` escapes this because a handler runs only at fixed, publicly determined
slice boundaries rather than immediately on arrival of its interrupt.


## 6. `model_sliced` and `model_sliced_userview` are non-interfering

```coq
forall (Opub Opriv : Ty)
       (p_pub : Proc Empty Opub)
       (p_priv : Proc THandlerOutput Opriv)
       (p_sched : Proc Empty Nat),
  NI (publicRel Empty) (publicRel Opub) p_pub ->
  NI (privateRel THandlerOutput) (privateRel Opriv) p_priv ->
  NI (publicRel Empty) (publicRel Nat) p_sched ->
  NI in_rel (out_rel Opub Opriv)       (model_sliced p_pub p_priv p_sched)
  /\ NI in_rel (final_out_rel Opub Opriv) (model_sliced_userview p_pub p_priv p_sched)
```

(the two conjuncts are `model_sliced_NI` and `model_sliced_userview_NI`).

`model_sliced_userview = map id parse_output model_sliced`, and `model_sliced_userview_NI`
is obtained from `model_sliced_NI` by pushing the output through `parse_output`
(output weakening: `parse_output` maps `out_rel`-related outputs to
`final_out_rel`-related ones).

**Why the result is parametric.** The theorem is about the interrupt-and-scheduling
mechanism, not about one system: the scheduler and both user processes are
arbitrary, subject only to being non-interfering at the classification their slot
declares, and their output alphabets are arbitrary too. What makes this available
is a property of the design rather than of the proof. The state transition never
reads a user slot's output *value* — `is_sch_out` matches
`(None,(None,(Some n,_)))`, inspecting the two user slots only for `None`-ness — so
no user behaviour reaches the schedule, and `fv_NI` (section 7), the one hard
obligation, does not mention the slot processes at all. The three hypotheses are
consumed at exactly three leaves of the assembly below, where the concrete proof
previously used `low_p_NI`, `high_p_NI` and `scheduler_NI`. Those three lemmas
survive as the instantiation that recovers the concrete system
(`model_sliced_concrete_NI`, `model_sliced_userview_concrete_NI`).

`model_sliced_NI` is assembled from the generic composition theorems, applied to the
pool of [`models.md`](models.md). There is one theorem per
constructor of the calculus, so the proof follows the structure of the term
`model_sliced` itself, discharging one layer at a time from the outside in:

| layer of `model_sliced` | theorem | what it gives |
|---|---|---|
| the outer `map inl (inr_or_def def)` and every interface rewiring | `map_NI` | `NI IRel' ORel p → NI IRel ORel' (map f g p)`, given `f_NI`/`f_PU` for `f` and `f_NI` for `g` |
| `loop` (the feedback tying output back to input) | `loop_NI` | `NI IRel IRel p → NI IRel IRel (loop p)` — note input and output relations must coincide |
| `sta` (the global state cell) | `sta_NI` / `sta_NI'` | `NI (eqpair_R VRel IRel) ORel p → NI IRel (eqpair VRel ORel) (sta f g v p)`, given `fv_NI` for both state updates — **this is where section 7 is discharged** |
| `maybe` (a slot or the pool idling) | `maybe_NI` | `NI IRel ORel p → NI (eqmaybe_false IRel) ORel (maybe p)` |
| `par` (laying the pool slots side by side) | `par_NI` | `NI IRel ORel1 p1 → NI IRel ORel2 p2 → NI IRel (eqpair ORel1 ORel2) (par p1 p2)` |
| `swi` (gating each slot on/off) | `swi_NI` / `swi_NI'` | `NI IRel (eqpair_LR BRel ORel) p → NI (eqpair_LR BRel IRel) (eqmaybe_swi ORel BRel) (swi b p)`, given awareness-or-obliviousness at every level |
| the leaves | `out_NI`, or a hypothesis | the handler and padding leaves are constant processes, so `out_NI`; the scheduler and user slots are where the three parametricity hypotheses are consumed |
| `parse_output` on top of `model_sliced` | `map_NI` again | output weakening, giving `model_sliced_userview_NI` |

Each theorem *derives* the composite's relations from those of its parts rather
than taking them as given. This is why the interface relations of section 4 have
the shape they do: `out_rel`'s nest of `eqpair`s is what `par_NI` imposes on a pool
output, and its `eqmaybe`s are what `swi_NI` imposes on a gated slot.

Two of these layers carry real content for our models. `sta_NI`'s `fv_NI` side
conditions are section 7. `swi_NI`'s side condition is the rest of this section.

### 6a. Gating a slot: why `falseRel`, and where obliviousness is needed

Every pool slot is gated by a `swi` whose bit says "is this slot the currently
selected pid". The bit is computed by mapping the current pid through `my_f_pid`
and comparing it with the slot index, so the `cRel` chosen for that Bool decides
what an observer learns from the gate. `swi_NI` demands, at every level:

```coq
aware BRel true l  \/  oblivious (eqpair_R BRel ORel) p l
```

`aware BRel true l` says a value related to `true` must *be* `true` and must not be
distinguished — the observer can trust the gate. `oblivious ORel p l` says the
opposite kind of thing about the gated process: every output it can ever produce is
distinguished at `l`, so the observer learns nothing from it either way.

**The `falseRel` trick, for slots whose identity is public.** `falseRel`
([definitions.v:261](../theories/definitions.v)) is equality on booleans, with
`dis l b := ~~ b /\ l = ⊥` — that is, `false` is the distinguished value, and only
at `⊥`. It is well-formed as a `cRel` precisely because `false` is the *only*
distinguished value, so it forms a single class (section 1).

This is the right relation for a public slot. Deriving the gate bit from a pid
maps every id other than this slot's to `false`, and `false` being distinguished is
what lets that map preserve distinguishedness — a distinguished pid goes to a
distinguished bool. Meanwhile `true` is never distinguished, so
`falseRel_aware : forall l, aware falseRel true l`
([noninterference.v:218](../theories/noninterference.v)) holds at *every* level, and
`swi_NI`'s obligation is discharged by the left disjunct outright.

**Where that is not available.** The two secret handlers cannot use it: whether
they are running is exactly what must be hidden (section 4). Their proofs instead
split on the level:

| slot | process | `swi_NI` obligation discharged by |
|---|---|---|
| 5 | `low_p`, public | `aware`, at every level |
| 4 | `high_p`, private | `aware`, at every level |
| 3 | scheduler | `aware`, at every level |
| 0 | timer handler | `aware`, at every level |
| 2 | default/NOP handler | `oblivious` at `⊥`; `aware` above |
| 1 | disk handler | `oblivious` at `⊥`; `aware` above |

Two things are worth reading off this table. First, the private user process
`high_p` uses the *same* `aware` argument as the public one — its secrecy is
carried entirely by the `privateRel` payload inside `eqmaybe_swi`, not by the gate.
The split is not public-versus-private; it is "everything except the two secret
handlers".

Second, obliviousness is needed *only at the attacker's level*. Above `⊥`,
`privateRel` collapses to equality, so the handler's gate is trustworthy and the
`aware` branch applies as usual. At `⊥` the proof builds an `ObliviousTrace`,
whose every output step must satisfy `dis ORel l o` — which holds because the
handler slots were classified `eqmaybe_top privateRel`, making both `Some o` and
`None` distinguished there. This is the point where the classification chosen in
section 4 pays for itself: had those slots been `eqmaybe privateRel`, `None` would
be public, obliviousness would fail, and there would be no way to hide that the
handler ran.

> The generic theorems in [`theories/theorems.v`](../theories/theorems.v)
> mechanise results from separate prior work; the mechanisation replaces the
> original coinductive definitions with inductive ones (`oblivious` above is one
> such), which avoids constructing streams throughout the proofs.


## 7. The state relation and `fv_NI` — the hard part

### 7a. What constrains the classification

`stateType_rel` assigns a classification to every field of the global state, and in
isolation that assignment would look arbitrary — nothing stops one writing down any
relation at all. What pins it down is that `sta_NI` needs **two** side conditions on
the state update, and they push in opposite directions:

```coq
fv_NI IRel VRel VRel f  :=  rel IRel l i i' -> rel VRel l v v' ->
                            rel VRel l (f i v) (f i' v')
f_EP  IRel VRel f       :=  dis IRel l i -> rel VRel l (f i v) v
```

`fv_NI` says the update maps related states to related states. `f_EP` — *equivalence
preserving* — says something stronger and less obvious: if the **input** is
distinguished at `l`, the update must leave the state where it was, up to `rel
VRel l`. An input the observer may not see must not visibly move the state.

These two squeeze the classification from both sides:

- **`f_EP` forces fields written by a secret input to be private.** A disk
  interrupt is distinguished at `⊥`, and `step0` responds by setting the disk
  pending bit. For `f_EP` to hold, the resulting state must still be `⊥`-related to
  the original — so the disk pending bit *cannot* be public. The same argument
  covers the default handler's pending bit.
- **`fv_NI` forces fields that decide control flow to be public.** `initiate_next`
  branches on the mask bits; if two `⊥`-related states could disagree there, they
  would take different branches and produce unrelated states. So the masks must be
  compared by equality.

Both constraints must hold simultaneously, which is why the interrupt controller is
classified *per bit* rather than wholesale: `hidden_pending` pairs a **private
pending** bit with a **public mask** bit. That pairing is not a stylistic choice —
it is the only assignment satisfying both obligations.

### 7b. `stateType_rel`: the resulting classification

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

### 7c. `fv_NI` and the composition-breakdown technique

`fv_NI IRel ORel VRel f` := for all `l`, all inputs `i ~ i'` (`rel IRel`) and all
states `v ~ v'` (`rel VRel`), the outputs are related:
`rel ORel l (f i v) (f i' v')`. The core obligation for `model_sliced` is

```text
fv_NI (eqsum in_rel out_rel) stateType_rel stateType_rel
      (state_step sliced_preroutine bool_coding)
```

— `stateType_rel` is closed under the state transition. `state_step` is a
composition ([`models.md` §5](models.md)), and `fv_NI_comp` discharges `fv_NI` of a
composition from `fv_NI` of the parts. Combined with
`fv_NI_step_left` / `fv_NI_step_right` (which lift a stage to the
`eqsum in_rel/out_rel` event), the obligation splits into one small, independent
goal per stage:

```text
state_step sliced_preroutine bool_coding  =
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
     (sliced_preroutine)                        ir_count / masks ⇒ agrees
   initiate_next(bool_coding) step_right      THE HARD ONE: related states must
                                              pick the SAME branch of "what runs
                                              next" — see 7d
```

The gain is that each stage becomes a self-contained goal. The price is that each
stage is proved over *all* pairs of related states and so cannot assume its input
came from the stage before it. Splitting the composition discards the restricted,
reachable set of states the earlier stage actually produces, and every stage must
then hold even for states that never arise together in a real run. Section 7c is
how that is recovered.

### 7d. `bool_coding`: re-establishing the forgotten invariant

The reachable invariant that matters (`model_sliced`; the substance is in
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

Two simplifications keep the proof tractable. Both are limitations of the model
rather than of the technique, and either could be lifted at the cost of a harder
`fv_NI` (section 7). A third group collects the remaining modelling choices.

**(a) Only one secret interrupt.** The model has a single secret interrupt — the
disk interrupt. The NOP (default) handler is present purely for privacy: it exists
to be the indistinguishable partner of the disk handler, and has no interrupt of
its own. A richer model with several secret interrupts would need a correspondingly
richer indistinguishability argument.

**(b) Same-length handler execution.** Every handler runs for the same fixed number
of output steps. This is what lets all masks be public (7b): because handlers
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

**(c) Further modelling choices.** These are built into the construction rather
than argued for, and nothing here claims they are without consequence:

- **One output step per selection.** In `process_pool` each slot's output is tagged
  with the constant `true`, which closes its switch after a single output. Every
  process is therefore cooperative and advances exactly one step per selection;
  preemption within a step is not modelled ([`models.md` §2](models.md)).
- **No interrupt nesting.** All masks are set while a handler runs, so a handler can
  never itself be interrupted. A design permitting nesting is out of scope.
- **The slice length is a constant, not a parameter.** What the design actually
  requires is that the slice be a **multiple of the handler runtime**, so that it
  ends on a handler boundary and `handler_completed` stays in step with the
  handlers. The model fixes the runtime at 2 and the slice at 4 — two handler runs —
  and `handler_completed` accordingly *enumerates* the boundaries (`Some 2`,
  `Some 4`) rather than computing them. Nothing in the security argument turns on
  those particular numbers, but the general statement is not what has been proved.
- **Fixed pool size and layout.** Six slots, of which the last is padding. The
  processes in the scheduler and user slots are parameters, but their *number* and
  *position* are not: the output projections of `models.v` §5 (`is_sch_out`,
  `tI_out`, `dI_out`, `default_I_out`) are tuple patterns that hardwire two user
  slots before the scheduler slot. Varying the count changes the state transition
  and so lands inside `fv_NI`.
