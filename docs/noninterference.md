# NonInterference: proof and security-equivalence documentation

*Prose companion to [`theories/noninterference.v`](../theories/noninterference.v).*

[`models.md`](models.md) describes the three models; this document gives the
security argument. Definitions are as given in
[`definitions.v`](../theories/definitions.v) and
[`noninterference.v`](../theories/noninterference.v).

> **Logical foundations.** Classical logic is imported at
> [`theories/theorems.v:737`](../theories/theorems.v) and used in one place, the
> case split on `aware` inside `swi_NI`, because `aware` is not constructively
> decidable (a decision procedure would do instead). Everything else is
> constructive.

## Contents

1. [Characterised equivalences (`cEquiv`): the framework and levels](#1-characterised-equivalences-cequiv-the-framework-and-levels)
2. [Base equivalences: `public_equiv`, `private_equiv`](#2-base-equivalences-public_equiv-private_equiv)
3. [Composite equivalences](#3-composite-equivalences)
4. [The model's equivalences: `in_equiv`, `out_equiv`, `out_equiv_userview`](#4-the-models-equivalences-in_equiv-out_equiv-out_equiv_userview)
5. [`model_immediate` is not non-interfering](#5-model_immediate-is-not-non-interfering)
6. [`model_sliced` and `model_sliced_userview` are non-interfering](#6-model_sliced-and-model_sliced_userview-are-non-interfering)
7. [The state equivalence and `fv_NI`: the hard part](#7-the-state-equivalence-and-fv_ni-the-hard-part)
8. [Model limitations](#8-model-limitations)


## 1. Characterised equivalences (`cEquiv`): the framework and levels

One `cEquiv` ([`definitions.v`](../theories/definitions.v)) is fixed for the input
type and one for the output type. Each carries two level-indexed fields, which
together say what an observer at a given level can tell about values of that type:

```text
rel l x y   x and y are indistinguishable to an observer at level l
dis l x     x is unobservable at level l, so non-interference is allowed
            to vary it freely
```

Levels form a lattice, and the attacker sits at its least level `⊥`. Both fields are
monotone downwards: whatever a level relates stays related below it, and whatever is
unobservable at a level stays unobservable below it. A lower observer sees less.

The remaining fields give the record its name. `rel l` is an **equivalence**, so at
each level it partitions the type into classes; and `dis l` is **characterised** as
one of them:

```text
dis l a0  ->  forall a1, dis l a1 <-> rel l a0 a1
```

Take any unobservable value. The values related to it are the other unobservable
ones and nothing else. So at each level a `cEquiv` cuts the type into classes an
observer there cannot tell apart, and one of them is the **unobservable class**, the
one the observer does not see at all. That class is empty whenever the level hides
nothing, as under `public_equiv` below, and the characterisation holds vacuously
there.

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


## 2. Base equivalences: `public_equiv`, `private_equiv`

**public** and **private** name a whole `cEquiv`, the one a type is given, whereas
**unobservable** is the per-level property `dis l x`. ("Secret" is used informally
for unobservable at `⊥`.)

```text
public_equiv A    dis l x = False        rel l x y = (x = y)
private_equiv A   dis l x = (l = ⊥)      rel l x y = (l ≠ ⊥ ∧ x = y) ∨ (l = ⊥)
```

These are the two extremes of the class picture of section 1. Under `public_equiv`
every class is a singleton and the unobservable class is empty. At any level, then,
a public value can be neither inserted, removed, nor varied without an observer
noticing. Under `private_equiv` the whole type collapses to a single class at `⊥`,
and that class is the unobservable one. Non-interference may therefore insert,
remove or replace such a value freely. At every other level `private_equiv` is
`public_equiv`: singleton classes, and the unobservable class empty.


## 3. Composite equivalences

Each family is one construction that takes *which values are secret* as a parameter.
The variants below are that one construction at different values of the parameter.
The rest follows from the characterisation of section 1: values of the same shape
are related componentwise, and values of different shape only by both being secret.

**`eqpair IRel ORel : cEquiv [Times I O]`** relates pairs componentwise:
`(a,b) ~ (a',b')` iff `a ~ a'` and `b ~ b'`. Nothing is secret (`dis = False`).
The model's own equivalences are built from this one, so it stays a definition in
its own right rather than an instance carrying a secrecy case that never fires.

**`eqpair_L` / `eqpair_R` / `eqpair_LR`** (`eqpair_aux`) are the gated variants,
where the *pair* may be secret and two related states can then differ there:

```text
eqpair_L   secret at l iff the LEFT component is (the right is irrelevant)
eqpair_R   secret at l iff the RIGHT component is
eqpair_LR  secret at l iff BOTH components are
```

**`eqsum IRel ORel : cEquiv [Sum I O]`** and **`eqsum_L`** (`eqsum_aux`) relate a
`Sum` tag-by-tag, `inl` by `IRel` and `inr` by `ORel`. Neither ever relates an
`inl` to an `inr`, so the *tag* stays public even when the payload underneath is
not; an `inr` is never secret. They differ only in the `inl` case:

```text
eqsum      nothing is secret
eqsum_L    an inl is secret exactly when its payload is
```

`eqsum_L` is the one the state cell uses (section 7a), where it makes `f_EP` a
condition on the input summand alone.

**`eqmaybe VRel` and variants (`eqmaybe_private` / `eqmaybe_hidden` / `eqmaybe_swi`,
via `eqmaybe_aux`)** relate `Option` values. On `Some`/`Some` they defer to
`VRel`; they differ only in a level-predicate `P l` = "the observer at `l` can
see `None`", `None` being secret exactly when `¬P l`:

```text
eqmaybe          P l = True        None is public: everyone can see it.
eqmaybe_private  P l = (l ≠ ⊥)     everyone but ⊥ can see None; None is secret
                                   only at the attacker level ⊥ -- the same
                                   condition as private_equiv.
eqmaybe_hidden   P l = False       nobody can see None; None is secret at every
                                   level (a value whose very presence is hidden).
eqmaybe_swi      P l = aware BRel  those who are "aware" per an equivalence BRel
                                   can see None; used to gate a switch branch.
```

The mixed case follows from the characterisation (section 1): `Some v ~ None` at
`l` iff both are secret there, i.e. iff `¬P l` and `dis VRel l v`. `None` can stand
in for `Some v` only when `v` is itself a secret the observer may not see.


## 4. The model's equivalences: `in_equiv`, `out_equiv`, `out_equiv_userview`

**`in_equiv : cEquiv [T_in]`** is built from `ir_dis` rather than taken as
`private_equiv TInterrupt`:

```coq
ir_dis l ir        := ir = DiskInterrupt /\ l = \bot
in_equiv.dis       := ir_dis
in_equiv.rel l     := fun ir ir' => ir = ir' \/ (ir_dis l ir /\ ir_dis l ir')
```

The disk interrupt alone is unobservable, and only at `⊥`; every other interrupt
must be matched even there. `private_equiv TInterrupt` would hide the timer as well,
and non-interference would then forbid the schedule from depending on it, which is
the whole basis of `model_sliced`.

**`out_equiv Opub Opriv : cEquiv [T_out Opub Opriv]`** relates two pool outputs
componentwise. A pool output is a six-tuple, one `Option` per slot:

```text
( pub , sys , sch , dfl , dsk , tmr )
```

and `out_equiv` is the corresponding nest of `eqpair`s, with these components:

| slot | component equivalence | value at `⊥` | did the slot run? |
|---|---|---|---|
| `pub` public user process | `eqmaybe public_equiv` | visible | visible |
| `sys` private user process | `eqmaybe private_equiv` | hidden | visible |
| `sch` scheduler | `eqmaybe public_equiv` | visible | visible |
| `dfl` default/NOP handler | `eqmaybe_private private_equiv` | hidden | hidden |
| `dsk` disk handler | `eqmaybe_private private_equiv` | hidden | hidden |
| `tmr` timer handler | `eqmaybe public_equiv` | visible | visible |

The timer slot is public, since it reacts only to public scheduled events. The disk
slot is private because the disk interrupt is, and the default/NOP slot has to be
private as well: a slice step is filled by one or the other, so the two must look
alike.

**The last two columns come apart only for the handlers, and that is where
scheduling secrecy lives.** The `private_equiv` payload hides the *value* in a slot.
Whether the slot ran is decided by the `eqmaybe` variant wrapped around it, since
that is what fixes who can see `None`. Under plain `eqmaybe`, `None` is public, so a
`⊥`-observer sees a `Some` where the other run has a `None`. That is why `sys` hides
`Syscall` from `NOP` but not the fact that `p_priv_concrete` produced something.
Under `eqmaybe_private`, `None` is unobservable at `⊥` and may be related to
`Some o`, so a disk handler run and a step where nothing happened are the same
observation.

For `p_priv_concrete` hiding the value is enough, since when it runs is public
anyway. For the two secret handlers the fact of running must go too, which is the
formal content of "the leak is in the scheduling". Section 6a discharges the
obligation `eqmaybe_private` creates.

**`out_equiv_userview Opub Opriv : cEquiv [T_out_userview Opub Opriv]`**
(user-visible output, for `model_sliced_userview`)

```text
eqmaybe_hidden (eqsum public_equiv private_equiv)
```

Only the user-visible channel survives `parse_output`: a public user output on the
left (exact) or the secret syscall on the right (secret at `⊥`).


## 5. `model_immediate` is not non-interfering

`model_immediate_not_NI : ~ NI in_equiv out_equivC model_immediate_concrete`.

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
  NI (public_equiv Empty) (public_equiv Opub) p_pub ->
  NI (private_equiv THandlerOutput) (private_equiv Opriv) p_priv ->
  NI (public_equiv Empty) (public_equiv Nat) p_sched ->
     NI in_equiv (out_equiv Opub Opriv)
          (model_sliced runtime runs p_pub p_priv p_sched)
  /\ NI in_equiv (out_equiv_userview Opub Opriv)
          (model_sliced_userview runtime runs p_pub p_priv p_sched)
```

(the two conjuncts are `model_sliced_NI` and `model_sliced_userview_NI`).

`model_sliced_userview = map id parse_output model_sliced`, and the second conjunct
follows from the first by output weakening: `parse_output` maps `out_equiv`-related
outputs to `out_equiv_userview`-related ones.

**Why the result is parametric.** Everything the process pool is built around
stays fixed; everything it carries is left open:

| parameter | ranges over | side condition |
|---|---|---|
| `p_pub` | any process in the public user slot | must be `NI` at `public_equiv`/`public_equiv` |
| `p_priv` | any process in the private user slot | must be `NI` at `private_equiv`/`private_equiv` |
| `p_sched` | any scheduler | must be `NI` at `public_equiv`/`public_equiv` |
| `Opub`, `Opriv` | the two user output alphabets | none |
| `runtime` | how many steps a handler runs for | none |
| `runs` | how many handler runs a slice holds | none |

Two features of the design buy this:

- **The pool's own transition never reads a user slot's output value.**
  `is_sched_out` matches `(None,(None,(Some n,_)))`, inspecting the user slots only
  for `None`-ness, so no user behaviour reaches the schedule.
- **`fv_NI` (section 7) never mentions the slot processes**, so the one hard
  obligation is unaffected by what fills them.

Instantiating them with `p_pub_concrete_NI`, `p_priv_concrete_NI` and
`scheduler_NI` recovers the concrete system (`model_sliced_concrete_NI`,
`model_sliced_userview_concrete_NI`).

`model_sliced_NI` is assembled from the generic composition theorems, one per
constructor of the calculus, so the proof follows the structure of the term itself
from the outside in:

| layer of `model_sliced` | theorem | what it gives |
|---|---|---|
| the outer `map inl (inr_or_def def)` and every rewiring of an input or output | `map_NI` | `NI IRel' ORel p → NI IRel ORel' (map f g p)`, given `f_NI`/`f_PU` for `f` and `f_NI` for `g` |
| `loop` (the feedback tying output back to input) | `loop_NI` | `NI IRel IRel p → NI IRel IRel (loop p)`; note input and output equivalences must coincide |
| `sta` (the global state cell) | `sta_NI` | `NI (eqpair_R VRel IRel) ORel p → NI IRel (eqpair VRel ORel) (sta f g v p)`, given `fv_NI` for both state updates; **this is where section 7 is discharged** |
| `maybe` (a slot or the pool idling) | `maybe_NI` | `NI IRel ORel p → NI (eqmaybe_hidden IRel) ORel (maybe p)` |
| `par` (laying the pool slots side by side) | `par_NI` | `NI IRel ORel1 p1 → NI IRel ORel2 p2 → NI IRel (eqpair ORel1 ORel2) (par p1 p2)` |
| `swi` (gating each slot on/off) | `swi_NI` | `NI IRel (eqpair_LR BRel ORel) p → NI (eqpair_LR BRel IRel) (eqmaybe_swi ORel BRel) (swi b p)`, given awareness-or-obliviousness at every level; the gate `BRel` is [`false_equiv`](#6a-gating-a-slot-why-false_equiv-and-where-obliviousness-is-needed) for every public slot |
| the leaves | `out_NI`, or a hypothesis | the handler and padding leaves are constant processes, so `out_NI`; the scheduler and user slots are where the three parametricity hypotheses are consumed |
| `parse_output` on top of `model_sliced` | `map_NI` again | output weakening, giving `model_sliced_userview_NI` |

Each theorem *derives* the composite's equivalences from those of its parts rather
than taking them as given, which accounts for the shape of the equivalences in
section 4: `par_NI` imposes `out_equiv`'s nest of `eqpair`s on a pool output, and
`swi_NI` imposes its `eqmaybe`s on a gated slot.

Two of these layers carry substantial side conditions. `sta_NI`'s are section 7,
and `swi_NI`'s occupy the rest of this one.

### 6a. Gating a slot: why `false_equiv`, and where obliviousness is needed

`par_NI` peels the pool apart into one goal per slot, so it is enough to look at a
single slot. Each is built the same way ([`models.md` §3](models.md)): a `swi`
holding the slot's process, with a `map` in front that computes the gate bit from
the current pid.

```coq
map (fun i => (slot_pid i.1 == k, f_proj i.2 k)) id (swi ... (f_proc k))
```

Two obligations are left for slot `k`, both parameterised by an equivalence `BRel`
on Bool we get to choose. `map_NI` asks that the gate map be sound at `BRel`, and its
second half is the one that bites:

```coq
f_PU (eqsum private_equiv public_equiv) BRel (fun pid => slot_pid pid == k)
  (* an unobservable pid must produce an unobservable bit *)
```

and `swi_NI` asks, at every level,

```coq
aware BRel true l  \/  oblivious (eqpair_R BRel ORel) (f_proc k) l
```

Under `aware BRel true l` a value related to `true` must *be* `true` and must not
be unobservable, so the observer can trust the gate. Under `oblivious` every output
the gated process can produce is unobservable at `l`, so the observer learns
nothing from it either way.

`cur_pid` is `Sum Bool Nat` classified `eqsum private_equiv public_equiv` (section 7b),
so at `⊥` every `inl b` is unobservable while `inr n` is not. What `f_PU` demands
of `BRel` therefore depends on where `slot_pid` sends those two `inl` values, which
is `1` for `inl true` and `2` for `inl false` ([models.v:222](../theories/models.v)).

**`p_pub_concrete` at slot 5, and the same for slots 4, 3 and 0.** Both
unobservable pids miss this slot, so the gate map sends them to `false`. `f_PU`
therefore needs a `BRel` in which `false` is unobservable. `false` becomes a sink
for exactly those pids the observer may not see, none of which select this slot.
`aware BRel true l` then needs `true` to be observable and rigid at every level.
`false_equiv`
([definitions.v:252](../theories/definitions.v)) is exactly that:

```text
false_equiv   dis l b = (b = false ∧ l = ⊥)      rel l b b' = (b = b')
```

It is a well-formed `cEquiv` because `false` is its only unobservable value, so at
`⊥` the unobservable class is the singleton `{false}`, and above `⊥` it is empty
(section 1). With it, `f_PU` holds, and
`false_equiv_aware : forall l, aware false_equiv true l`
([noninterference.v:230](../theories/noninterference.v)) discharges `swi_NI` by the
left disjunct at every level, no case split needed.

**The disk handler at slot 1, and the same for the default handler at slot 2.**
Here `inl true` maps to `true` and `inl false` maps to `false`, and both pids are
unobservable at `⊥`. `f_PU` now demands that *both* booleans be unobservable there,
which rules `false_equiv` out and leaves `private_equiv Bool`. But if `true` is
unobservable at `⊥` then `aware BRel true ⊥` fails by definition, so the left
disjunct is gone and the proof must split on the level:

- above `⊥`, `private_equiv` collapses to equality, nothing is unobservable, and
  `aware` applies as before;
- at `⊥`, the right disjunct is used. The proof builds an `ObliviousTrace`, every
  output step of which must satisfy `dis ORel ⊥ o`.

That last obligation is affordable only because the slot's output was classified
`eqmaybe_private private_equiv` in section 4, which makes both `Some o` and `None`
unobservable at `⊥`. Under `eqmaybe private_equiv` the `None` would be public,
obliviousness would fail, and nothing would hide that the handler ran. Losing
awareness at `⊥` costs nothing, since the slot's output is private there anyway.

| slot | process | `BRel` | `swi_NI` discharged by |
|---|---|---|---|
| 5 | `p_pub_concrete`, public | `false_equiv` | `aware`, every level |
| 4 | `p_priv_concrete`, private | `false_equiv` | `aware`, every level |
| 3 | scheduler | `false_equiv` | `aware`, every level |
| 0 | timer handler | `false_equiv` | `aware`, every level |
| 2 | default/NOP handler | `private_equiv` | `oblivious` at `⊥`, `aware` above |
| 1 | disk handler | `private_equiv` | `oblivious` at `⊥`, `aware` above |

The line falls between the two secret handlers and everything else.
`p_priv_concrete` sits on the public side of it: its secrecy travels in the
`private_equiv` payload inside `eqmaybe_swi`, never in its gate.

> The generic theorems in [`theories/theorems.v`](../theories/theorems.v)
> mechanise results from separate prior work; the mechanisation replaces the
> original coinductive definitions with inductive ones (`oblivious` above is one
> such), which avoids constructing streams throughout the proofs.


## 7. The state equivalence and `fv_NI`: the hard part

### 7a. What constrains the classification

The state transition is driven by an event, which is an interrupt arriving on the
left or a pool output on the right:

```coq
event : Sum T_in (T_out Opub Opriv)      inl i = an interrupt arrived
                                          inr o = the pool produced an output
```

`step_sum f g`, written `f ⊕ g` below, is the state update that handles an input
with `f` and an output with `g`, and the transition is one of these
([`models.md` §6](models.md)):

```text
(f ⊕ g) (inl i) = f i
(f ⊕ g) (inr o) = g o

state_step h b = set_pending ⊕ (initiate_next b ∘ h ∘ check_scheduler)
```

An arriving interrupt does nothing but record itself. Everything it eventually
causes sits in the right summand, on a later output step where the input is no
longer the thing being varied.

Composition is componentwise, `(f ⊕ g) ∘ (f' ⊕ g') = (f ∘ f') ⊕ (g ∘ g')`, so the two
summands can be reasoned about separately, which is what section 7c does.

`sta_NI` needs two side conditions on this transition, and they push in opposite
directions:

```coq
fv_NI IRel VRel VRel f  :=  rel IRel l i i' -> rel VRel l v v' ->
                            rel VRel l (f i v) (f i' v')
f_EP  IRel VRel f       :=  dis IRel l i -> rel VRel l (f i v) v
```

`fv_NI` says the transition maps related states to related states. `f_EP`, for
*equivalence preserving*, asks for more: an input the observer may not see must not
visibly move the state. Events are related by `eqsum_L in_equiv out_equiv`
([noninterference.v:514](../theories/noninterference.v)), whose `dis` holds only on
the `inl` side, so `f_EP` constrains the left summand and nothing else. It is a
condition on `set_pending` alone.

- **`f_EP` forces fields written by a secret input to be private.** A disk
  interrupt is unobservable at `⊥`, and `set_pending` responds by setting the disk
  pending bit. For `f_EP` to hold the result must still be `⊥`-related to the
  original, so that bit cannot be public. Likewise the default handler's.
- **`fv_NI` forces fields that decide control flow to be public.** `initiate_next`
  branches on the mask bits, and two `⊥`-related states disagreeing there would
  take different branches and produce unrelated states.

Both must hold at once, so the interrupt controller is classified *per bit*:
`private_pending_equiv` pairs a private pending bit with a public mask bit, the only
assignment that satisfies both.

`f_EP` also explains why `set_pending` writes one bit and stops. No decision can be
taken on an input step, since starting a handler, reassigning `cur_pid`, clearing a
mask or moving the slice counter would all disturb fields compared by equality at
`⊥`. Everything the interrupt causes is deferred to the right summand, where the
input is no longer the thing being varied.

### 7b. `state_type_equiv`: the resulting classification

The state is nested pairs ([`models.md` §5](models.md)), and `state_type_equiv` is the
matching nest of `eqpair`s:

```text
state = ( ( cur_pid , prev_pid ) , ( re_sched , ( ir_count , ic ) ) )
ic    = ( dfl , ( dsk , tmr ) )        the interrupt controller
dfl   = ( pending , mask )             and likewise dsk and tmr
```

Field by field:

| field | type | equivalence | at `⊥` |
|---|---|---|---|
| `cur_pid` | Sum Bool Nat | `eqsum private_equiv public_equiv` | see below |
| `prev_pid` | Nat | `public_equiv` | visible |
| `re_sched` | Bool | `public_equiv` | visible |
| `ir_count`, the slice counter | Option Nat | `public_equiv` | visible |
| `dfl` | (pending, mask) | `private_pending_equiv` | pending hidden, mask visible |
| `dsk` | (pending, mask) | `private_pending_equiv` | pending hidden, mask visible |
| `tmr` | (pending, mask) | `public_bits_equiv` | both visible |

Every mask bit is public, which is the formal content of "all masks are public".

`cur_pid` is the one field whose parts are classified differently, and it is where
the design is doing its work. `inl b` means a handler is running, with `b`
selecting which; `inr n` is a user or scheduler pid. Since `eqsum` never relates an
`inl` to an `inr` (section 3), *that* a handler is running stays visible, and so
does the pid in `inr n`. What `private_equiv` hides is the `Bool` inside `inl`: at
`⊥`, `inl true` and `inl false` are related, so the disk handler and the
default/NOP one look alike.

Across two `⊥`-related states, that bit and the `dfl` and `dsk` pending bits are
the only things allowed to differ.

### 7c. `fv_NI` and the composition-breakdown technique

The core obligation for `model_sliced` is that `state_type_equiv` is closed under the
whole transition:

```text
fv_NI  (eqsum_L in_equiv out_equiv)  state_type_equiv  state_type_equiv
       (state_step sliced_preroutine restore_invariant)
```

`eqsum_L` relates two inputs by `in_equiv` and two outputs by `out_equiv`, and never
relates an input to an output. So `fv_NI_step_sum` splits the goal along the `⊕`:
on the left both events are inputs and only `set_pending` runs, on the right both
are outputs and only the pipeline runs. `fv_NI_comp` then breaks that pipeline into
its three stages, leaving one goal apiece:

| stage | summand | what has to be shown |
|---|---|---|
| `set_pending` | input | an arriving interrupt sets a pending bit, and related inputs give related states |
| `check_scheduler` | output | the scheduler pid is public, so the `cur_pid` update agrees |
| `handler_preroutine` | output | the slice bookkeeping reads only the public `ir_count` and masks, so it agrees |
| `initiate_next` | output | related states must pick the same branch of "what runs next"; the hard one, see 7d |

`f_EP` needs no such breakdown. Since `eqsum_L` makes only an `inl` unobservable,
`f_EP_step_sum` reduces it to a condition on `set_pending`, and the output summand
never comes up.

Each goal is self-contained, which is the point of splitting. The cost is that a
stage is proved over *all* pairs of related states. It cannot assume its input came
from the stage before it, so it must hold even for states no real run produces.
Section 7d recovers what that loses.

### 7d. `restore_invariant`: putting the forgotten invariant back

Two facts hold of every state `model_sliced` can reach. First, while the time slice
is live, the NOP (default) handler's pending bit is true, the disk and NOP masks are
false and the timer mask is true. Second, the disk and NOP masks are always toggled
together. Because `fv_NI_comp` forgets both, `restore_invariant` writes them back
into the interrupt controller just before `initiate_next` runs:

- it sets the controller's flags from `timeslice_live`, restoring "slice live ⇒ NOP
  pending, disk/NOP unmasked, timer masked". The flags are ORed in, so a state that
  already has them set is untouched. Since `timeslice_live` reads only the public
  `ir_count`, the same flags are set in two related states;
- it forces the default (NOP) mask to equal the disk mask. On any state that
  already satisfies the invariant this is a no-op, but stated unconditionally it
  lets the `sta` non-interference argument assume the two masks are in sync without
  having to recover that fact from an earlier stage.

The hard `initiate_next` stage can then assume related states take the same branch,
because `restore_invariant` has already run and made the deciding mask bits agree.


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
otherwise leak through the public mask toggles. `fv_NI` would then have to be proved
across diverging branches. Avoiding that is why the model fixes handler length.

**(c) Further modelling choices**, built into the construction rather than argued
for:

- **One output step per selection.** In `process_pool` each slot's output is tagged
  with the constant `true`, closing its switch after a single output. Every process
  is cooperative and advances one step per selection; preemption within a step goes
  unmodelled ([`models.md` §3](models.md)).
- **No interrupt nesting.** All masks are set while a handler runs, so a handler can
  never itself be interrupted.
- **Fixed pool size and layout.** Six slots, the last of them padding. The
  scheduler and user slot *processes* are parameters, but their number and position
  are fixed by the output projections `is_sched_out`, `tI_out`, `dI_out` and
  `default_ir_out`. Those are tuple patterns, and they hardwire two user slots ahead
  of the scheduler slot. Varying the count changes the state transition and lands
  inside `fv_NI`.
