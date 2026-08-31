# Departures from the paper

*Companion to [`theories/adequacy.v`](../theories/adequacy.v).*

The calculus and the generic non-interference theorems are Rafnsson et al.'s,
*Timing-Sensitive Noninterference through Composition*, [POST
2017](https://users.ece.cmu.edu/~lbauer/papers/2017/post2017-compose-time.pdf).
Mechanising them changed four definitions.

**Every one of the four is proved adequate in
[`adequacy.v`](../theories/adequacy.v).** For each, the paper's version is written
out and shown to hold of exactly the same processes as the version used here. That
file depends only on [`definitions.v`](../theories/definitions.v), nothing depends
on it, and its results rest on no axioms beyond the two lattice parameters. None of
it is needed to follow the models or the proof; it is here so that the departures
can be checked rather than taken on trust.

## Overview

| # | Departure | The paper | Here | Adequacy |
|---|---|---|---|---|
| 1 | the equivalences | an equivalence on `V` extended with a distinguished element `*` | a record with separate `rel` and `dis` fields, tied by a law | `NI_lEquiv` |
| 2 | the shape of `NI` | a coinductive simulation, four clauses at the head | three closure clauses, at an arbitrary position `n` | `PNI_of_SNI`, `SNI_of_PNI` |
| 3 | traces | infinite streams of labels | finite lists of labels | `NI_SNI` |
| 4 | obliviousness | every reachable output is unobservable | every output falls in one indistinguishability class | `oblivious_of_ObliviousDis` |

Departures 2 and 3 compose: `NI_paper` says the paper's Definition 4 and this
development's `NI` hold of the same processes.

## 1. Characterised equivalences, not L-equivalences

**The paper.** A value set `V` is extended with a distinguished element `*`. An
L-equivalence is a level-indexed equivalence on `V + {*}`, weakening downwards, and
`v` is unobservable at `l` when `v` is `l`-equivalent to `*`.

**Here.** `cEquiv` ([`definitions.v`](../theories/definitions.v)) carries
indistinguishability and unobservability as two fields, `rel` and `dis`, kept in
step by the characterisation law `dis l a0 -> forall a1, dis l a1 <-> rel l a0 a1`.

**Why.** Unobservability is used on its own throughout: the insertion and deletion
clauses of `NI` turn on `dis` alone. Having it as a field of the record avoids
threading an option type through every equivalence, every model and every proof.

**Adequacy.** `lEquiv` is the paper's presentation, with `None` for `*`.
`cEquiv_of_lEquiv` and `lEquiv_of_cEquiv` translate in both directions,
`cEquiv_of_lEquivK` and `lEquiv_of_cEquivK` say the translations are inverse, and
`NI_lEquiv` carries non-interference across.

**Rests on.** Nothing. Both translations are constructive, and no choice principle
is needed, because `*` is adjoined to `V` rather than chosen from it. Transitivity
through `*` is exactly what the characterisation law supplies, which is why the two
records hold the same information.

## 2. Closure at a position, not a coinductive simulation

**The paper.** Definition 3 is a coinductive simulation with four clauses, applied
at the head of a stream and reapplied to the residual: delete an unobservable
input, insert one, substitute an indistinguishable one, and match an output with an
indistinguishable output. Definition 4 asks that a process simulate every stream it
performs.

**Here.** `Trace` collects what a process can do, and `NI_l`
([`definitions.v`](../theories/definitions.v)) states three closure properties of
it, each at an arbitrary position `n`. The fourth clause is built into `Trace`,
whose output constructor already compares outputs through `rel ORel`.

**Why.** The generic theorems in [`theorems.v`](../theories/theorems.v) are proved
against this shape. Quantifying over positions replaces coinduction with ordinary
induction, which is what makes those proofs go through by induction on traces.

**Adequacy.** `Performs`, `Clause1` to `Clause4`, `SimulationF` and `PNI` are the
paper's definitions, clause for clause. `PNI_of_SNI` and `SNI_of_PNI` prove the two
shapes agree.

**Rests on.** Reading position `n` as the head of the residual after `n` steps.
Forwards, the coinduction carries a run `t` and the state `runT t p` it reaches, and
closure at the head there is closure at position `size t` in the original process.
Backwards, `n` labels are peeled off the simulation by induction and the trace
rebuilt. Two bridges connect the paper's exact streams to traces that fix outputs
only up to `rel`: `runS` gives the exact run along a stream's labels, and
`simulation_SRel` transports a simulation across streams differing only by
indistinguishable outputs.

## 3. Finite traces, not streams

**The paper.** Traces are infinite streams of labels, and definitions over them,
such as obliviousness, are coinductive.

**Here.** A trace is a finite list, the labels of zero or more reductions
([`definitions.v:208`](../theories/definitions.v)). Definitions quantify over the
traces a process admits.

**Why.** No proof ever has to construct a stream. `Trace` is an ordinary inductive
predicate, so the development proceeds by induction on traces, and prefix-closure
is one of its constructors rather than a lemma.

**Adequacy.** `STrace` and `SNI` are `Trace` and `NI` read over streams, clause for
clause, and `NI_SNI` proves the two readings hold of the same processes.

**Rests on.** Two properties. First, finite and stream behaviour determine each
other. `Trace` speaks only about finite lists, so all one has about a process
running along a stream is one derivation per prefix length, and `sprefix_STrace`
assembles that family into a single infinite derivation. This is where reduction
has to be **deterministic**: derivations for different lengths need not pass
through the same intermediate processes, and the construction has to commit at each
step to one successor that serves every length at once. The converse lemma,
`Trace_STrace`, continues a finite trace into a stream, and for that reduction has
to be **total**. Both hold because reduction is a function, given as `stepI` and
`stepO` and proved to agree with the two relations. Second, insertion commutes with
prefixing: a prefix shorter than the insertion point does not see the inserted
input, and a longer one sees it in the same place.

## 4. Obliviousness by class, not by unobservability

**The paper.** Definition 10, coinductive over reductions: a level is oblivious to
a process when every output the process can reach is unobservable at that level.

**Here.** `oblivious` asks that all outputs fall in one class: there is a reference
output `o0` such that every output the process can produce is indistinguishable
from it.

**Why.** Only inputs are ever inserted or deleted, so non-interference constrains
outputs through indistinguishability alone
([`noninterference.md` §1](noninterference.md)). Requiring the distinguished class
was therefore stronger than needed, and it forced output types to carry a non-empty
`dis`. Under the weaker condition, neither `swi_NI` nor `oblivious_swi` mentions
`dis` at all.

**Adequacy.** In two parts, because two things changed at once. Shape:
`ObliviousAt` is the paper's, quantified over reachable states, and
`ObliviousAt_iff` says it agrees with the trace-based `oblivious_at`. Condition:
`ObliviousDis` is the paper's, and `oblivious_of_ObliviousDis` says it implies the
one used here. The converse fails, so the weakening is strict: under `public_equiv`
a constant process stays in one class (`oblivious_out_public`) while nothing there
is unobservable at all (`not_ObliviousDis_public`).

**Rests on.** The shape result needs nothing; unlike departure 3, neither direction
uses reduction being a function. The implication needs every process to emit, so
that a reference output is available.

## Scope

These four results are about definitions. They say that the paper's definitions and
this development's hold of the same processes, not that the paper's proofs were
replayed: the generic theorems in [`theorems.v`](../theories/theorems.v) are proved
for the definitions used here.
