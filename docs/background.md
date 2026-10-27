# NonInterference: background

*Prose companion to [`theories/definitions.v`](../theories/definitions.v) and
[`theories/theorems.v`](../theories/theorems.v).*

Everything in this development is built from a small process calculus and a
definition of non-interference over it. Both are due to Rafnsson et al.,
*Timing-Sensitive Noninterference through Composition*
([POST 2017](https://users.ece.cmu.edu/~lbauer/papers/2017/post2017-compose-time.pdf));
mechanising them is part of the contribution of this development. This document
sets them out once, so that [`models.md`](models.md) and
[`noninterference.md`](noninterference.md) can build on them. The mechanisation
departs from the paper in four places, each proved harmless; they are set out in
[`departures.md`](departures.md), and none of them is needed to follow what is
here.

Names are those of the source, and every process is given with the `@` and `Ty`
annotations erased (section 1 says why the source needs them).

## Contents

1. [The process calculus](#1-the-process-calculus)
2. [Characterised equivalences and `NI`](#2-characterised-equivalences-and-ni)
3. [Public and private](#3-public-and-private)
4. [Composite equivalences](#4-composite-equivalences)
5. [Compositional theorems](#5-compositional-theorems)


## 1. The process calculus

A process has type `Proc I O`, where `I` and `O` are its input and output types.

A process moves in one of two ways:

```text
   p ──i──▶ p'     p receives the input i
   p ──o──▶ p'     p emits the output o
```

in any order; nothing forces them to alternate. A **trace** is the sequence of
values along one such run, each marked as received or emitted, and it is all
non-interference looks at.

Throughout, *emit* means an output step and *receive* an input step.

**Time is counted in output steps.** Every output step is one tick of a clock the
observer shares, and on every tick a process emits a value; there is no tick on
which it stays silent. Where nothing happens, the value says so (in the models
below, a slot that did not run emits `None`), and that absence is itself something
an observer can see. Input steps take no time. This is what makes the definitions
timing-sensitive: delaying an output by one step changes the trace, exactly as
changing its value would.

Both kinds of step are **total** and **deterministic**. Whatever state a process is
in, it can receive any input of its type and it can emit, and in each case there is
exactly one way to do so: the successor is determined, and on an output step so is
the value emitted. The two relations are therefore functions, and
[`adequacy.v`](../theories/adequacy.v) gives them as the functions `stepI` and
`stepO` and proves the relations agree with them. Nothing in the models relies on
this, and the reader can take the arrows above at face value. It matters once
traces are compared with the paper's streams, where totality is what lets a finite
run be continued and determinism is what makes the finite runs of one stream fit
together into a single infinite one ([`departures.md` §3](departures.md)).

There are seven constructors, described here by what each does on an input step and
on an output step:

- **`out o`** is the constant process. It receives any value and is unchanged; it
  emits the fixed `o` and is unchanged.
- **`map f g p`** rewires `p` on both sides. Receiving `i`, it hands `p` the
  value `f i`. Emitting, it lets `p` emit some `o` and emits `g o` in its place.
  (`Proc I' O → Proc I O'`)
- **`sta f g v p`** gives `p` a state cell holding `v`, and *exposes* that cell in
  what it emits. Receiving `i`, the cell becomes `f i v` and `p` receives the pair
  `(f i v, i)`. Emitting, `p` emits some `o`, the cell becomes `g o v`, and the whole
  process emits the pair `(g o v, o)`, the new state alongside `p`'s value.
- **`swi b p`** is a one-bit "switch" in phase `b`, wrapping a `p` that emits values
  tagged with a Bool. Receiving `(b', i)`, the phase flips to `xor b b'` and `p`
  receives `i`. Emitting in phase `false`, it emits `None` and `p` does not step at
  all; emitting in phase `true`, `p` emits a tagged `(c, o)`, the switch emits
  `Some o` and the phase becomes `xor true c`. `swi` is how a pool slot is gated on /
  off ([`models.md` §3](models.md)).
- **`par p1 p2`**: receiving `i`, both `p1` and `p2` receive it. Emitting, both emit,
  and `par` emits the pair of their two values.
- **`loop p`** is feedback. Receiving `i`, `p` receives it. Emitting is two steps of
  `p`: `p` emits some `o`, that same `o` is immediately fed back to `p` as an input
  step, and `loop p` emits `o`. (`Proc I I → Proc I I`)
- **`maybe p`** makes the input optional. Receiving `None`, `p` does not step;
  receiving `Some i`, `p` receives `i`. Emitting passes straight through: `p` emits
  `o` and so does `maybe p`. (`Proc I O → Proc (Option I) O`)

> **Why `I` and `O` are drawn from `Ty`.** In the mechanisation they range over an
> inductive `Ty` (`Nat`, `Bool`, `Unit`, `Times`, `Option`, `Sum`, ...) rather than
> over Coq's `Set`, with `[t]` interpreting a `t : Ty` as the `Set` it encodes.
> Going through `Ty` rather than through `Set` directly is what makes reductions
> invertible. The negative result needs that, since refuting non-interference means
> showing a trace is *not* accepted. The cost is the explicit annotations in the
> source, which these documents strip away.


## 2. Characterised equivalences and `NI`

**Two levels.** The definitions are stated over an arbitrary security lattice, but
everything in this development can be read with two levels: the attacker `⊥`, and
`⊤`, an observer who sees everything. These documents use that reading throughout;
[`noninterference.md` §5](noninterference.md) says what the general lattice adds.

One `cEquiv` ([`definitions.v`](../theories/definitions.v)) is fixed for the input
type and one for the output type. Each carries two level-indexed fields, which
together say what an observer at a given level can tell about values of that type:

```text
rel l x y   x and y are indistinguishable to an observer at level l
dis l x     x is unobservable at level l, so non-interference is allowed
            to vary it freely
```

The remaining fields give the record its name. `rel l` is an **equivalence**, so at
each level it partitions the type into classes; and `dis l` is **characterised** as
one of them:

```text
dis l a0  ->  forall a1, dis l a1 <-> rel l a0 a1
```

Take any unobservable value. The values related to it are the other unobservable
ones and nothing else. So at each level a `cEquiv` cuts the type into classes an
observer there cannot tell apart, and one of them is the **distinguished class**,
the one the observer does not see at all. That class is empty whenever the level
hides nothing, as under `public_equiv` below, and the characterisation holds
vacuously there.

The two fields are not used symmetrically. `NI` licenses inserting and deleting
inputs only, so `dis IRel` is what its insertion and deletion clauses turn on, while
outputs are compared through `rel ORel` alone. An output type is given a `cEquiv`
because that is the one record the theorems consume, and its distinguished class
then serves only to say which outputs are indistinguishable.

### What `NI` says

```coq
NI IRel ORel p := forall l, NI_l IRel ORel l p
```

and `NI_l` ([definitions.v:226](../theories/definitions.v)) is three clauses, all
quantified over traces `t` and positions `n`, with `insert n (inl i) t` placing an
input `i` at position `n`:

| clause | statement | reading |
|---|---|---|
| substitution | `rel IRel l i i'` → `Trace (insert n i t)` → `Trace (insert n i' t)` | swapping an input for an indistinguishable one keeps it a trace |
| insertion | `dis IRel l i` → `Trace t` → `Trace (insert n i t)` | an unobservable input may be added anywhere |
| deletion | `dis IRel l i` → `Trace (insert n i t)` → `Trace t` | and removed again |

Traces are compared through `ORel` at `l`, so outputs are determined only up to
`rel ORel l`. Together the clauses say that the set of traces visible at `l` is
unchanged by anything the observer at `l` may not see. All the content is at `⊥`:
at `⊤` nothing is unobservable and indistinguishable means equal, so the clauses
hold of every process. The counterexample of
[`noninterference.md` §2](noninterference.md) refutes the *insertion* clause at `⊥`.

The paper states the same property differently, as a coinductive simulation over
streams, with L-equivalences in place of `cEquiv`. Both versions are mechanised and
shown to accept the same processes ([`departures.md` §1–3](departures.md)).


## 3. Public and private

**public** and **private** name a whole `cEquiv`, the one a type is given, whereas
**unobservable** is the per-level property `dis l x`. ("Secret" is used informally
for unobservable at `⊥`.)

```text
                  at ⊥                              at ⊤
public_equiv A    nothing unobservable;             nothing unobservable;
                  related iff equal                 related iff equal
private_equiv A   everything unobservable;          nothing unobservable;
                  any two values related            related iff equal
```

These are the two extremes of the class picture of section 2. Under `public_equiv`
every class is a singleton and the distinguished class is empty. A public value can
therefore be neither inserted, removed, nor varied without an observer noticing.
Under `private_equiv` the whole type collapses at `⊥` to a single class, and that
class is the distinguished one. Non-interference may therefore insert, remove or
replace such a value freely. At `⊤` the two coincide.


## 4. Composite equivalences

Each family is one construction that takes *which values are secret* as a parameter.
The variants below are that one construction at different values of the parameter.
The rest follows from the characterisation of section 2: values of the same shape
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

`eqsum_L` is the one the state cell uses
([`noninterference.md` §4a](noninterference.md)), where it makes `f_EP` a condition
on the input summand alone.

**`eqmaybe P VRel`** relates `Option` values. On `Some`/`Some` it defers to
`VRel`; the level predicate `P` says who can see `None`, and `None` is secret
exactly for those who cannot. Four instances are used, named after who sees
`None`:

```text
                 who sees None             can the attacker (⊥)?   can ⊤?
eqmaybe_all   every level               yes                     yes
eqmaybe_nonbot  every level above ⊥       no                      yes
eqmaybe_nobody   no level                  no                      no
eqmaybe_aware      levels aware of the gate  iff aware under BRel    iff aware there
```

To the attacker, `eqmaybe_nonbot` and `eqmaybe_nobody` are the same; they differ
only at `⊤`.

The mixed case follows from the characterisation (section 2): `Some v ~ None` at
`l` iff both are secret there, i.e. iff `None` is hidden at `l` and `dis VRel l v`.
`None` can stand in for `Some v` only when `v` is itself a secret the observer may
not see.


## 5. Compositional theorems

[`theorems.v`](../theories/theorems.v) proves one theorem per constructor: if the
parts are non-interfering at suitable equivalences, so is the composite. Each
theorem *derives* the composite's equivalences from those of its parts, which is
what gives the model's equivalences their shape.

| constructor | theorem | from | to |
|---|---|---|---|
| `out o` | `out_NI` | nothing | `NI IRel ORel (out o)` |
| `map f g p` | `map_NI` | `NI IRel' ORel p`, side conditions on `f` and `g` | `NI IRel ORel' (map f g p)` |
| `sta f g v p` | `sta_NI` | `NI (eqpair_R VRel IRel) ORel p`, `fv_NI` and `f_EP` for the updates | `NI IRel (eqpair VRel ORel) (sta f g v p)` |
| `swi b p` | `swi_NI` | `NI IRel (eqpair_LR BRel ORel) p`, awareness or obliviousness at every level | `NI (eqpair_LR BRel IRel) (eqmaybe_aware ORel BRel) (swi b p)` |
| `par p1 p2` | `par_NI` | `NI IRel ORel1 p1`, `NI IRel ORel2 p2` | `NI IRel (eqpair ORel1 ORel2) (par p1 p2)` |
| `loop p` | `loop_NI` | `NI IRel IRel p` | `NI IRel IRel (loop p)` |
| `maybe p` | `maybe_NI` | `NI IRel ORel p` | `NI (eqmaybe_nobody IRel) ORel (maybe p)` |

Two of these carry substantial side conditions, and they are where the work of
[`noninterference.md`](noninterference.md) lies: `sta_NI` asks that the state update
map related states to related states (`fv_NI`) and that an unobservable input not
visibly move the state (`f_EP`); `swi_NI` asks, at each level, that the observer
either can trust the gate (`aware`) or learns nothing from the gated process
(`oblivious`).
