# NonInterference — proof / security-relation documentation

*Prose companion to [`theories/noninterference.v`](../theories/noninterference.v).*

[`models.md`](models.md) describes the three models; this document gives the
security argument. Definitions are as given in
[`definitions.v`](../theories/definitions.v) and
[`noninterference.v`](../theories/noninterference.v).

> **Logical foundations.** Classical logic is imported at
> [`theories/theorems.v:739`](../theories/theorems.v) and used in one place, the
> switch lemma `swi_NI'`, because `aware` is not constructively decidable (a
> decision procedure would do instead). Everything else is constructive.

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

Every interface carries a `cRel`
([`definitions.v`](../theories/definitions.v)), a level-indexed relation saying what
an observer at each level can tell about values of that type:

```text
rel l x y   x and y are indistinguishable to an observer at level l
dis l x     x is unobservable at level l, so non-interference is allowed
            to vary it freely
```

Levels form a lattice whose least and most exposed level `⊥` is the attacker. Both
fields are monotone downwards: whatever a level relates stays related below it, and
whatever is unobservable at a level stays unobservable below it. A lower observer
sees less.

The remaining field gives the record its name. `rel l` is an equivalence, and the
unobservable values must form one of its classes:

```text
dis l a0  ->  forall a1, dis l a1 <-> rel l a0 a1
```

Take any unobservable value. The values related to it are the other unobservable
ones and nothing else. So whatever an observer at `l` can see gets compared by the
underlying relation, while whatever it cannot see collapses into a single class.

### What `NI` says

```coq
NI IRel ORel p := forall l, NI_l IRel ORel l p
```

and `NI_l` ([definitions.v:229](../theories/definitions.v)) is three clauses, all
quantified over traces `t` and positions `n`, with `insert n (inl i) t` placing an
input `i` at position `n`:

| clause | statement | reading |
|---|---|---|
| substitution | `rel IRel l i i'` → `Trace (insert n i t)` → `Trace (insert n i' t)` | swapping an input for an indistinguishable one keeps it a trace |
| insertion | `dis IRel l i` → `Trace t` → `Trace (insert n i t)` | an unobservable input may be added anywhere |
| deletion | `dis IRel l i` → `Trace (insert n i t)` → `Trace t` | and removed again |

Traces are compared through `ORel` at `l`, so outputs are determined only up to
`rel ORel l`. Together the clauses say that the set of traces visible at `l` is
unchanged by anything the observer at `l` may not see. The case that matters is
`l = ⊥`; the counterexample of section 5 refutes the *insertion* clause.


## 2. Base relations: `publicRel`, `privateRel`

**public** and **private** classify an *interface*, whereas **unobservable** is the
per-level property `dis l x`. ("Secret" is used informally for unobservable
at `⊥`.)

```text
publicRel A    dis l x = False        rel l x y = (x = y)
privateRel A   dis l x = (l = ⊥)      rel l x y = (l ≠ ⊥ ∧ x = y) ∨ (l = ⊥)
```

A public value can be neither inserted, removed, nor varied without an observer
noticing. A private value is secret at `⊥` and nowhere else. There the relation is
total, so the value may be inserted, removed or replaced unnoticed; higher up it is
compared by equality like any public one. The syscall output and the secret handler
outputs carry `privateRel`. The interrupt input carries a stricter custom relation
(section 4).


## 3. Composite relations

**`eqpair IRel ORel : cRel [Times I O]`** — relate pairs componentwise:
`(a,b) ~ (a',b')` iff `a ~ a'` and `b ~ b'`.

**`eqpair_LR` / `eqpair_R`** — variants of `eqpair` differing only in when the
*pair* counts as secret. Plain `eqpair` never is (`dis = False`); the gated
variants make the pair itself secret, so two related states can carry different
values there:

```text
eqpair_LR  secret at l iff BOTH components are secret at l
eqpair_R   secret at l iff the RIGHT component is (the left is irrelevant)
```

(`eqpair_L` is the mirror image.)

**`eqsum IRel ORel : cRel [Sum I O]`** — relate a `Sum` tag-by-tag, `inl` by
`IRel` and `inr` by `ORel`. An `inl` is never related to an `inr` at any level, and
the sum itself is never secret, so the *tag* is always public even when the payload
underneath is not.

**`eqmaybe VRel` and variants (`eqmaybe_top` / `eqmaybe_false` / `eqmaybe_swi`)** —
relate `Option` values. On `Some`/`Some` they defer to `VRel`; they differ only in
a level-predicate `P l` = "the observer at `l` can see `None`", `None` being secret
exactly when `¬P l`:

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
`l` iff both are secret there, i.e. iff `¬P l` and `dis VRel l v`. `None` can stand
in for `Some v` only when `v` is itself a secret the observer may not see.


## 4. The model interfaces: `in_rel`, `out_rel`, `final_out_rel`

**`in_rel : cRel [T_in]`** is `TInterrupt_rel`, a custom relation whose `dis` field
is `ir_dis` and whose `rel` field relates two interrupts when both are unobservable
or the two are equal:

```text
ir_dis l ir = (ir = DiskInterrupt ∧ l = ⊥)
```

So the disk interrupt alone is unobservable, and only at `⊥`. Every other
interrupt, the timer included, has to be matched even there. Taking
`privateRel TInterrupt` would hide the timer as well, and non-interference would
then forbid the schedule from depending on it, which is the whole basis of
`model_sliced`. Singling out the disk interrupt gives the theorem the reading we
want: the timer is a public scheduled event, and the disk interrupt's presence is
what an attacker cannot infer.

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

The three handler components are the slots default/NOP, disk, timer. The timer slot
is public, since it reacts only to public scheduled events. The disk slot is
private because the disk interrupt is, and the default/NOP slot has to be private
as well: a slice step is filled by one or the other, so the two must look alike.

**Scheduling secrecy lives in the choice of `eqmaybe` variant.** The handlers and
the private user process both carry `privateRel` payloads, but:

```text
sys slot  eqmaybe     privateRel    None is PUBLIC
                                    → that high_p produced an output is visible;
                                      only Syscall-versus-NOP is hidden

dfl, dsk  eqmaybe_top privateRel    None is unobservable at ⊥
                                    → at the attacker's level, a handler output is
                                      indistinguishable from no output at all, so
                                      *whether the handler ran* is hidden too
```

That difference is the formal content of "the leak is in the scheduling". For
`high_p` hiding the value suffices, since when it runs is public anyway. For the
two secret handlers the *fact of running* must be hidden as well, and `eqmaybe_top`
does it by letting `Some o` relate to `None`: a disk handler run and a step where
nothing happened become the same observation. Section 6a discharges the resulting
obligation.

**`final_out_rel Opub Opriv : cRel [T_out Opub Opriv]`** (user-visible output, for
`model_sliced_userview`)

```text
eqmaybe_false (eqsum publicRel privateRel)
```

Only the user-visible channel survives `parse_output`: a public user output on the
left (exact) or the secret syscall on the right (secret at `⊥`).


## 5. `model_immediate` is not non-interfering

`model_immediate_not_NI : ~ NI in_rel out_relC model_immediate_concrete`.

`model_immediate` is parametric like `model_sliced`, but a counterexample should
exhibit a single system, so the refutation is stated at `model_immediate_concrete`,
the instance at the concrete user processes, scheduler and alphabets
([`models.md` §10](models.md)).

Non-interference requires that inserting a secret input anywhere in a trace leaves
it a trace. The counterexample refutes that clause with a two-step trace:

1. Start from `[out_get'; out_get']`, two ordinary requests from the public user
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

A secret input has changed what the `⊥`-observer sees. `model_sliced` escapes this
because a handler runs only at publicly determined slice boundaries, never on
arrival of its interrupt.


## 6. `model_sliced` and `model_sliced_userview` are non-interfering

```coq
forall (Opub Opriv : Ty) (runtime runs : nat)
       (p_pub : Proc Empty Opub)
       (p_priv : Proc THandlerOutput Opriv)
       (p_sched : Proc Empty Nat),
  NI (publicRel Empty) (publicRel Opub) p_pub ->
  NI (privateRel THandlerOutput) (privateRel Opriv) p_priv ->
  NI (publicRel Empty) (publicRel Nat) p_sched ->
     NI in_rel (out_rel Opub Opriv)
          (model_sliced runtime runs p_pub p_priv p_sched)
  /\ NI in_rel (final_out_rel Opub Opriv)
          (model_sliced_userview runtime runs p_pub p_priv p_sched)
```

(the two conjuncts are `model_sliced_NI` and `model_sliced_userview_NI`).

`model_sliced_userview = map id parse_output model_sliced`, and the second conjunct
follows from the first by output weakening: `parse_output` maps `out_rel`-related
outputs to `final_out_rel`-related ones.

**Why the result is parametric.** The theorem covers the mechanism at every
instance. The scheduler, both user processes, their alphabets, the handler length
and the slice size are all arbitrary, with no side condition beyond the one built
into `time_slice runtime runs = runs * runtime`. The design is what makes this
available: the state transition never reads a user slot's output *value*
(`is_sch_out` matches `(None,(None,(Some n,_)))`, inspecting the user slots only
for `None`-ness), so no user behaviour reaches the schedule and `fv_NI` (section 7)
never mentions the slot processes. The three hypotheses are consumed at three
leaves of the assembly below; instantiating them with `low_p_NI`, `high_p_NI` and
`scheduler_NI` recovers the concrete system (`model_sliced_concrete_NI`,
`model_sliced_userview_concrete_NI`).

`model_sliced_NI` is assembled from the generic composition theorems, one per
constructor of the calculus, so the proof follows the structure of the term itself
from the outside in:

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
than taking them as given, which accounts for the shape of the interface relations
in section 4: `par_NI` imposes `out_rel`'s nest of `eqpair`s on a pool output, and
`swi_NI` imposes its `eqmaybe`s on a gated slot.

Two of these layers carry substantial side conditions. `sta_NI`'s are section 7,
and `swi_NI`'s occupy the rest of this one.

### 6a. Gating a slot: why `falseRel`, and where obliviousness is needed

Every pool slot is gated by a `swi` whose bit says "is this slot the currently
selected pid", computed by mapping the current pid through `my_f_pid` and comparing
with the slot index. The `cRel` chosen for that Bool decides what an observer
learns from the gate; `swi_NI` demands, at every level:

```coq
aware BRel true l  \/  oblivious (eqpair_R BRel ORel) p l
```

Under `aware BRel true l` a value related to `true` must *be* `true` and must not
be unobservable, so the observer can trust the gate. Under `oblivious ORel p l`
every output the gated process can produce is unobservable at `l`, so the observer
learns nothing from it either way.

**The `falseRel` trick, for slots whose identity is public.** `falseRel`
([definitions.v:261](../theories/definitions.v)) is equality on booleans with
`dis l b := ~~ b /\ l = ⊥`, making `false` the unobservable value and only at `⊥`.
It is a well-formed `cRel` because `false` is the *only* unobservable value, so it
forms a single class (section 1).

Deriving the gate bit from a pid sends every id other than this slot's to `false`,
and since `false` is unobservable, that map preserves unobservability. `true` never
is, so `falseRel_aware : forall l, aware falseRel true l`
([noninterference.v:218](../theories/noninterference.v)) holds at *every* level and
discharges `swi_NI` by the left disjunct outright.

**Where that is not available.** The two secret handlers cannot use it, since
whether they are running is the very thing that must be hidden (section 4). Their
proofs split on the level:

| slot | process | `swi_NI` obligation discharged by |
|---|---|---|
| 5 | `low_p`, public | `aware`, at every level |
| 4 | `high_p`, private | `aware`, at every level |
| 3 | scheduler | `aware`, at every level |
| 0 | timer handler | `aware`, at every level |
| 2 | default/NOP handler | `oblivious` at `⊥`; `aware` above |
| 1 | disk handler | `oblivious` at `⊥`; `aware` above |

The line falls between the two secret handlers and everything else, which includes
the private user process: `high_p` uses the same `aware` argument as the public
one, its secrecy carried by the `privateRel` payload inside `eqmaybe_swi` while its
gate stays trustworthy.

Obliviousness is needed *only at the attacker's level*. Above `⊥`, `privateRel`
collapses to equality, so the gate is trustworthy and `aware` applies. At `⊥` the
proof builds an `ObliviousTrace`, whose every output step must satisfy
`dis ORel l o`. That holds because the handler slots were classified
`eqmaybe_top privateRel`, which makes both `Some o` and `None` unobservable there.
Had they been classified `eqmaybe privateRel`, `None` would be public,
obliviousness would fail, and nothing would hide that the handler ran.

> The generic theorems in [`theories/theorems.v`](../theories/theorems.v)
> mechanise results from separate prior work; the mechanisation replaces the
> original coinductive definitions with inductive ones (`oblivious` above is one
> such), which avoids constructing streams throughout the proofs.


## 7. The state relation and `fv_NI` — the hard part

### 7a. What constrains the classification

`stateType_rel` assigns a classification to every field of the global state. What
pins that assignment down is that `sta_NI` needs **two** side conditions on the
state update, and they push in opposite directions:

```coq
fv_NI IRel VRel VRel f  :=  rel IRel l i i' -> rel VRel l v v' ->
                            rel VRel l (f i v) (f i' v')
f_EP  IRel VRel f       :=  dis IRel l i -> rel VRel l (f i v) v
```

`fv_NI` says the update maps related states to related states. `f_EP`, for
*equivalence preserving*, asks for more: if the **input** is unobservable at `l`,
the update has to leave the state where it was, up to `rel VRel l`. An input the
observer may not see must not visibly move the state.

These squeeze the classification from both sides:

- **`f_EP` forces fields written by a secret input to be private.** A disk
  interrupt is unobservable at `⊥` and `record_pending` responds by setting the
  disk pending bit; for `f_EP` to hold, the result must still be `⊥`-related to the
  original, so that bit cannot be public. Likewise the default handler's.
- **`fv_NI` forces fields that decide control flow to be public.** `initiate_next`
  branches on the mask bits; two `⊥`-related states disagreeing there would take
  different branches and produce unrelated states.

Both must hold at once, so the interrupt controller has to be classified *per bit*:
`hidden_pending` pairs a **private pending** bit with a **public mask** bit, the
only assignment that satisfies both obligations.

**Why an arriving interrupt does nothing but record itself.** `f_EP` also dictates
the shape of the input stage, and it does so on security grounds. A disk interrupt
is unobservable at `⊥`, so receiving one has to leave the state `⊥`-related to what
it was. No decision can be taken on an input step: the model cannot start a
handler, reassign `cur_pid`, clear a mask or move the slice counter, since all four
are compared by equality at `⊥`.

That leaves writing to a *private* field and nothing else. `record_pending` sets
the interrupt's pending bit, which is private for just this reason, and touches
nothing else, so `f_EP` goes through. The other three stages of `state_step` are
`step_right`s and so act as the identity on an input event.

Everything the interrupt eventually causes is deferred to a later output step,
where the input is no longer the thing being varied. Hence `initiate_next` sits
inside a `step_right` ([`models.md` §6](models.md)), and `pool_input` returns
`None` on an input event to keep the pool from stepping
([`models.md` §4](models.md)).

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

Reading off the classification (the `stateType` layout is in
[`models.md` §5](models.md)):

- **masks: public everywhere.** Every mask bit sits under `publicRel`, so it must
  agree across two related executions.
- **pending bits of the two secret handlers (disk, default): secret**
  (`hidden_pending` pairs a private pending with a public mask); the timer
  handler's controller pair is public (`public_pair`).
- **`cur_pid`** (`Sum Bool Nat`, under `eqsum privateRel publicRel`): the `inl`/`inr`
  *tag* is public (section 3), so whether a handler is running at all is visible.
  The secret is the `Bool` *inside* the `inl`. At `⊥`, `inl true` and `inl false`
  are related, so an observer cannot tell the disk handler from the default/NOP
  one. The user/scheduler pid `inr n` is public, as is **`prev_pid`**.
- **`re_sch` and `ir_count`** (the time slice): public.

So across two `⊥`-related states only the secret handlers' pending bits and the
handler bit inside `cur_pid` may differ.

### 7c. `fv_NI` and the composition-breakdown technique

The core obligation for `model_sliced` is that `stateType_rel` is closed under the
state transition:

```text
fv_NI (eqsum in_rel out_rel) stateType_rel stateType_rel
      (state_step sliced_preroutine bool_coding)
```

`state_step` is a composition ([`models.md` §6](models.md)), and `fv_NI_comp`
discharges `fv_NI` of a composition from `fv_NI` of the parts. With
`fv_NI_step_left` / `fv_NI_step_right` lifting a stage to the
`eqsum in_rel/out_rel` event, the obligation splits into one independent goal per
stage:

```text
state_step sliced_preroutine bool_coding  =
    initiate_next(bool_coding) o handler_preroutine o apply_schedule o record_pending

   stage                        lifted by    per-stage fv_NI obligation
   ---------------------------------------------------------------------------------
   record_pending (input)       step_left    arriving interrupt sets a pending bit;
                                             related inputs give related states
   apply_schedule (output)      step_right   scheduler pid is public, so the
                                             cur_pid update agrees
   handler_preroutine           step_right   slice bookkeeping reads only the public
     (sliced_preroutine)                     ir_count and masks, so it agrees
   initiate_next(bool_coding)   step_right   THE HARD ONE: related states must pick
                                             the SAME branch of "what runs next"
                                             -- see 7d
```

The gain is that each stage becomes a self-contained goal. The price is that each
is proved over *all* pairs of related states and cannot assume its input came from
the stage before it. Splitting the composition discards the reachable set the
earlier stage actually produces, leaving every stage to hold even for states that
never arise in a real run. Section 7d recovers what is lost.

### 7d. `bool_coding`: re-establishing the forgotten invariant

Two facts hold of every state `model_sliced` can reach: while the time slice is
live, the NOP (default) handler's pending bit is true, the disk and NOP masks are
false and the timer mask is true; and the disk and NOP masks are always toggled
together. Because `fv_NI_comp` forgets them, `bool_coding` re-bakes them into the
state just before `initiate_next` runs:

- it ORs in a controller pattern derived from `timeslice_live`, restoring "slice
  live ⇒ NOP pending, disk/NOP unmasked, timer masked". Since `timeslice_live`
  reads only the public `ir_count`, the pattern is equal across two related states;
- it forces the default (NOP) mask to equal the disk mask. On any state that
  already satisfies the invariant this is a no-op, but stated unconditionally it
  lets the `sta` non-interference argument assume the two masks are in sync without
  having to recover that fact from an earlier stage.

The hard `initiate_next` stage can then assume related states take the same branch,
because `bool_coding` has already run and made the deciding mask bits agree.


## 8. Model limitations

Two simplifications keep the proof tractable. Both are limitations of the model
rather than of the technique, and either could be lifted at the cost of a harder
`fv_NI` (section 7).

**(a) Only one secret interrupt.** The NOP (default) handler exists purely for
privacy, as the disk handler's indistinguishable partner, and has no interrupt of
its own. Several secret interrupts would need a correspondingly richer
indistinguishability argument.

**(b) Same-length handler execution.** Every handler runs for the same fixed number
of output steps, which is what lets all masks be public (7b). Handlers finish on
public time-slice boundaries, never after a secret-dependent number of steps, so
the mask bits never encode secret timing.

The payoff comes in the final stage. With public masks, two related states agree on
all mask bits and take the same branches through `initiate_next`. Variable-length
handlers would force the masks private, since a secret handler's running time would
otherwise leak through the public mask toggles, and `fv_NI` would then have to be
proved across diverging branches. Avoiding that is why the model fixes handler
length.

**(c) Further modelling choices**, built into the construction rather than argued
for:

- **One output step per selection.** In `process_pool` each slot's output is tagged
  with the constant `true`, closing its switch after a single output. Every process
  is cooperative and advances one step per selection; preemption within a step goes
  unmodelled ([`models.md` §3](models.md)).
- **No interrupt nesting.** All masks are set while a handler runs, so a handler can
  never itself be interrupted.
- **Slice length is a parameter.** The theorem holds for every `runtime` and `runs`
  with no side condition, because nothing in the argument inspects a numeral. The
  `fv_NI` stages that read the counter first establish that it is *public*, then
  case on it abstractly, treating `handler_completed` as an opaque boolean and the
  counter as `None` / `Some 0` / `Some n.+1`. The design does require the slice to
  end on a handler boundary, but that is structural, since
  `time_slice runtime runs = runs * runtime`. Degenerate values are covered too: at
  `runtime = 0` a handler never signals completion and at `runs = 0` the slice
  closes immediately, and both systems remain non-interfering while simply doing
  less. One genuine constraint survives, that all three handlers share a single
  `runtime`, which `slot_procs` enforces by construction.
- **Fixed pool size and layout.** Six slots, the last of them padding. The
  scheduler and user slot *processes* are parameters, but their number and position
  are fixed by the output projections `is_sch_out`, `tI_out`, `dI_out` and
  `default_I_out`, tuple patterns that hardwire two user slots before the scheduler
  slot. Varying the count changes the state transition and lands inside `fv_NI`.
