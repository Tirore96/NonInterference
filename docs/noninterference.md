# NonInterference: proof and security-equivalence documentation

*Prose companion to [`theories/noninterference.v`](../theories/noninterference.v).*

[`models.md`](models.md) describes the three models; this document gives the
security argument. It builds on [`background.md`](background.md), which sets out the
characterised equivalences, `NI`, the generic equivalences such as `eqpair` and
`eqmaybe`, and the composition theorems. Definitions are as given in
[`definitions.v`](../theories/definitions.v) and
[`noninterference.v`](../theories/noninterference.v).

> **Logical foundations.** Classical logic is imported at
> [`theories/theorems.v:737`](../theories/theorems.v) and used in one place, the
> case split on `aware` inside `swi_NI`, because `aware` is not constructively
> decidable (a decision procedure would do instead). Everything else is
> constructive.

## Contents

1. [The model's equivalences: `in_equiv`, `out_equiv`, `out_equiv_userview`](#1-the-models-equivalences-in_equiv-out_equiv-out_equiv_userview)
2. [`model_immediate` is not non-interfering](#2-model_immediate-is-not-non-interfering)
3. [`model_sliced` and `model_sliced_userview` are non-interfering](#3-model_sliced-and-model_sliced_userview-are-non-interfering)
4. [The state equivalence and `fv_NI`: the hard part](#4-the-state-equivalence-and-fv_ni-the-hard-part)
5. [How general the result is](#5-how-general-the-result-is)
6. [Model limitations](#6-model-limitations)


## 1. The model's equivalences: `in_equiv`, `out_equiv`, `out_equiv_userview`

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
( pub , sys , sch , nop , dsk , tmr )
```

and `out_equiv` is the corresponding nest of `eqpair`s, with these components:

| slot | component equivalence | value at `⊥` | did the slot run? |
|---|---|---|---|
| `pub` public user process | `eqmaybe_all public_equiv` | visible | visible |
| `sys` private user process | `eqmaybe_all private_equiv` | hidden | visible |
| `sch` scheduler | `eqmaybe_all public_equiv` | visible | visible |
| `nop` NOP handler | `eqmaybe_nonbot private_equiv` | hidden | hidden |
| `dsk` disk handler | `eqmaybe_nonbot private_equiv` | hidden | hidden |
| `tmr` timer handler | `eqmaybe_all public_equiv` | visible | visible |

The timer slot is public, since it reacts only to public scheduled events. The disk
slot is private because the disk interrupt is, and the NOP slot has to be
private as well: a slice step is filled by one or the other, so the two must look
alike.

**The last two columns come apart only for the handlers, and that is where
scheduling secrecy lives.** The `private_equiv` payload hides the *value* in a slot.
Whether the slot ran is decided by the `eqmaybe` variant wrapped around it, since
that is what fixes who can see `None`. Under `eqmaybe_all`, `None` is public, so a
`⊥`-observer sees a `Some` where the other run has a `None`. That is why `sys` hides
`Syscall` from `Idle` but not the fact that `p_priv_concrete` produced something.
Under `eqmaybe_nonbot`, `None` is unobservable at `⊥` and may be related to
`Some o`, so a disk handler run and a step where nothing happened are the same
observation.

For `p_priv_concrete` hiding the value is enough, since when it runs is public
anyway. For the two secret handlers the fact of running must go too, which is the
formal content of "the leak is in the scheduling". Section 3a discharges the
obligation `eqmaybe_nonbot` creates.

**`out_equiv_userview Opub Opriv : cEquiv [T_out_userview Opub Opriv]`**
(user-visible output, for `model_sliced_userview`)

```text
eqmaybe_nobody (eqsum public_equiv private_equiv)
```

Only the user-visible channel survives `parse_output`: a public user output on the
left (exact) or the secret syscall on the right (secret at `⊥`).


## 2. `model_immediate` is not non-interfering

`model_immediate_not_NI : ~ NI in_equiv out_equivC model_immediate_concrete`.

A counterexample should exhibit a single system, so the refutation is stated at
`model_immediate_concrete`, the instance at the concrete user processes, scheduler
and alphabets ([`models.md` §10](models.md)).

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


## 3. `model_sliced` and `model_sliced_userview` are non-interfering

```coq
model_sliced_NI          : NI in_equiv (out_equiv Opub Opriv) model_sliced
model_sliced_userview_NI : NI in_equiv (out_equiv_userview Opub Opriv)
                              model_sliced_userview
```

The arguments of the two models are elided above; section 5 gives one of the
statements in full. Both hold whenever the three slot processes are themselves
non-interfering at the classification their slot declares: `p_pub` and the scheduler at
`public_equiv`/`public_equiv`, `p_priv` at `private_equiv`/`private_equiv`.

`model_sliced_userview = map id parse_output model_sliced`, and the second result
follows from the first by output weakening: `parse_output` maps `out_equiv`-related
outputs to `out_equiv_userview`-related ones.

Read the two statements here at one system: a scheduler, two user processes, a
handler length and a slice size. None of those is fixed by the theorem, and
[section 5](#5-how-general-the-result-is) says precisely what is left open, once the
proof below has made clear what the argument rests on.

`model_sliced_NI` is assembled from the generic composition theorems, one per
constructor of the calculus, so the proof follows the structure of the term itself
from the outside in:

| layer of `model_sliced` | theorem | what it gives |
|---|---|---|
| the outer `map inl (inr_or_def no_output)` and every rewiring of an input or output | `map_NI` | `NI IRel' ORel p → NI IRel ORel' (map f g p)`, given `f_NI`/`f_PU` for `f` and `f_NI` for `g` |
| `loop` (the feedback tying output back to input) | `loop_NI` | `NI IRel IRel p → NI IRel IRel (loop p)`; note input and output equivalences must coincide |
| `sta` (the global state cell) | `sta_NI` | `NI (eqpair_R VRel IRel) ORel p → NI IRel (eqpair VRel ORel) (sta f g v p)`, given `fv_NI` for both state updates; **this is where section 4 is discharged** |
| `maybe` (a slot or the pool idling) | `maybe_NI` | `NI IRel ORel p → NI (eqmaybe_nobody IRel) ORel (maybe p)` |
| `par` (laying the pool slots side by side) | `par_NI` | `NI IRel ORel1 p1 → NI IRel ORel2 p2 → NI IRel (eqpair ORel1 ORel2) (par p1 p2)` |
| `swi` (gating each slot on/off) | `swi_NI` | `NI IRel (eqpair_LR BRel ORel) p → NI (eqpair_LR BRel IRel) (eqmaybe_aware ORel BRel) (swi b p)`, given awareness-or-obliviousness at every level; the gate `BRel` is [`false_equiv`](#3a-gating-a-slot-why-false_equiv-and-where-obliviousness-is-needed) for every public slot |
| the leaves | `out_NI`, or a hypothesis | the handler and padding leaves are constant processes, so `out_NI`; the scheduler and user slots are where the three parametricity hypotheses are consumed |
| `parse_output` on top of `model_sliced` | `map_NI` again | output weakening, giving `model_sliced_userview_NI` |

Each theorem *derives* the composite's equivalences from those of its parts rather
than taking them as given, which accounts for the shape of the equivalences in
section 1: `par_NI` imposes `out_equiv`'s nest of `eqpair`s on a pool output, and
`swi_NI` imposes its `eqmaybe`s on a gated slot.

Two of these layers carry substantial side conditions. `sta_NI`'s are section 4,
and `swi_NI`'s occupy the rest of this one.

### 3a. Gating a slot: why `false_equiv`, and where obliviousness is needed

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
aware BRel true l  \/  oblivious (eqmaybe_aware ORel BRel) (swi b (f_proc k)) l
```

Under `aware BRel true l` a value related to `true` must *be* `true` and must not
be unobservable, so the observer can trust the gate. Under `oblivious` the gated
slot never leaves one indistinguishability class at `l`:

```coq
oblivious ORel p l  :=  exists o0, forall s, Trace ORel l s p ->
                                   ObliviousTrace ORel l o0 s
```

where `ObliviousTrace ORel l o0 s` asks that every output in `s` satisfy
`rel ORel l o0 o`, for the one reference output `o0`. The observer sees the same
class whatever the input does, so it learns nothing from the slot either way. Only
`rel` is involved, which is what non-interference constrains on the output side
([`background.md` §2](background.md)).

`cur_pid` is `Sum Bool Nat` classified `eqsum private_equiv public_equiv` (section 4b),
so at `⊥` every `inl b` is unobservable while `inr n` is not. What `f_PU` demands
of `BRel` therefore depends on where `slot_pid` sends those two `inl` values, which
is `1` for `inl true` and `2` for `inl false` ([models.v:222](../theories/models.v)).

**`p_pub_concrete` at slot 5, and the same for slots 4, 3 and 0.** Both
unobservable pids miss this slot, so the gate map sends them to `false`. `f_PU`
therefore needs a `BRel` in which `false` is unobservable. `false` becomes a sink
for exactly those pids the observer may not see, none of which select this slot.
`aware BRel true l` then needs `true` to be observable and rigid at every level.
`false_equiv`
([definitions.v:235](../theories/definitions.v)) is exactly that:

```text
false_equiv   dis l b = (b = false ∧ l = ⊥)      rel l b b' = (b = b')
```

It is a well-formed `cEquiv` because `false` is its only unobservable value, so at
`⊥` the distinguished class is the singleton `{false}`, and at `⊤` it is empty
([`background.md` §2](background.md)). With it, `f_PU` holds, and
`false_equiv_aware : forall l, aware false_equiv true l`
([noninterference.v:238](../theories/noninterference.v)) discharges `swi_NI` by the
left disjunct at every level, no case split needed.

**The disk handler at slot 1, and the same for the NOP handler at slot 2.**
Here `inl true` maps to `true` and `inl false` maps to `false`, and both pids are
unobservable at `⊥`. `f_PU` now demands that *both* booleans be unobservable there,
which rules `false_equiv` out and leaves `private_equiv Bool`. But if `true` is
unobservable at `⊥` then `aware BRel true ⊥` fails by definition, so the left
disjunct is gone and the proof must split on the level:

- at `⊤`, `private_equiv` is equality, nothing is unobservable, and `aware` applies
  as before;
- at `⊥`, the right disjunct is used, with `None` as the reference output. A step
  where the slot is gated off emits `None` itself, and a step where it runs emits
  `Some o`, so the obligation is `rel (eqmaybe_aware ORel BRel) ⊥ None (Some o)`.

`oblivious_swi` ([theorems.v](../theories/theorems.v)) discharges that from two
facts, both of them relations:

```coq
rel (eqmaybe_aware ORel BRel) l None (Some o0)      (* None sits in the class *)
oblivious_at (eqpair_R BRel ORel) (b0,o0) p l     (* and the slot stays in it *)
```

Every `Some o` the slot emits is then related to `None` by transitivity through
`Some o0`. Where the slot's own relation holds by two outputs being unobservable,
the characterisation ([`background.md` §2](background.md)) turns that straight back
into relatedness, so no step of the argument mentions `dis`.

What the model has to prove is the first line, at `⊥`, with `o0` any handler
output. `eqmaybe_aware` relates `None` to a `Some` exactly when the observer cannot
see the gate and the payload is unobservable, so this is where the classification of
section 1 comes back in: the slot's `private_equiv` payload is what makes a disk
handler run and a step where nothing happened the same observation. Under a public
`None` the two would come apart and obliviousness would fail. Losing awareness at
`⊥` costs nothing, since the slot's output is private there anyway.

So the distinguished class enters only through how `eqmaybe_aware` *defines*
relatedness, and never through obliviousness or through `swi_NI`, neither of which
mentions it. The paper asks for more, that every output be unobservable; the
weakening and its adequacy are in [`departures.md` §4](departures.md).

| slot | process | `BRel` | `swi_NI` discharged by |
|---|---|---|---|
| 5 | `p_pub_concrete`, public | `false_equiv` | `aware`, every level |
| 4 | `p_priv_concrete`, private | `false_equiv` | `aware`, every level |
| 3 | scheduler | `false_equiv` | `aware`, every level |
| 0 | timer handler | `false_equiv` | `aware`, every level |
| 2 | NOP handler | `private_equiv` | `oblivious` at `⊥`, `aware` at `⊤` |
| 1 | disk handler | `private_equiv` | `oblivious` at `⊥`, `aware` at `⊤` |

The line falls between the two secret handlers and everything else.
`p_priv_concrete` sits on the public side of it: its secrecy travels in the
`private_equiv` payload inside `eqmaybe_aware`, never in its gate.

## 4. The state equivalence and `fv_NI`: the hard part

### 4a. What constrains the classification

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
summands can be reasoned about separately, which is what section 4c does.

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
([noninterference.v:560](../theories/noninterference.v)), whose `dis` holds only on
the `inl` side, so `f_EP` constrains the left summand and nothing else. It is a
condition on `set_pending` alone.

- **`f_EP` forces fields written by a secret input to be private.** A disk
  interrupt is unobservable at `⊥`, and `set_pending` responds by setting the disk
  pending bit. For `f_EP` to hold the result must still be `⊥`-related to the
  original, so that bit cannot be public. Likewise the NOP handler's.
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

### 4b. `state_type_equiv`: the resulting classification

The state is nested pairs ([`models.md` §5](models.md)), and `state_type_equiv` is the
matching nest of `eqpair`s:

```text
state = ( ( cur_pid , prev_pid ) , ( re_sched , ( ir_count , ic ) ) )
ic    = ( nop , ( dsk , tmr ) )        the interrupt controller
nop   = ( pending , mask )             and likewise dsk and tmr
```

Field by field:

| field | type | equivalence | at `⊥` |
|---|---|---|---|
| `cur_pid` | Sum Bool Nat | `eqsum private_equiv public_equiv` | see below |
| `prev_pid` | Nat | `public_equiv` | visible |
| `re_sched` | Bool | `public_equiv` | visible |
| `ir_count`, the slice counter | Option Nat | `public_equiv` | visible |
| `nop` | (pending, mask) | `private_pending_equiv` | pending hidden, mask visible |
| `dsk` | (pending, mask) | `private_pending_equiv` | pending hidden, mask visible |
| `tmr` | (pending, mask) | `public_bits_equiv` | both visible |

Every mask bit is public, which is the formal content of "all masks are public".

`cur_pid` is the one field whose parts are classified differently, and it is where
the policy is doing its work. `inl b` means a handler is running, with `b`
selecting which; `inr n` is a user or scheduler pid. Since `eqsum` never relates an
`inl` to an `inr` ([`background.md` §4](background.md)), *that* a handler is
running stays visible, and so does the pid in `inr n`. What `private_equiv` hides is the `Bool` inside `inl`: at
`⊥`, `inl true` and `inl false` are related, so the disk handler and the
NOP one look alike.

Across two `⊥`-related states, that bit and the `nop` and `dsk` pending bits are
the only things allowed to differ.

### 4c. `fv_NI` and the composition-breakdown technique

The core obligation for `model_sliced` is that `state_type_equiv` is closed under the
whole transition:

```text
fv_NI  (eqsum_L in_equiv out_equiv)  state_type_equiv  state_type_equiv
       (state_step sliced_service restore_invariant)
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
| `service_policy` | output | the slice bookkeeping reads only the public `ir_count` and masks, and writes the same values into both states (the masks, the private NOP pending bit, the public `re_sched`), so it agrees |
| `initiate_next` | output | related states must pick the same branch of "what runs next"; the hard one, see 7d |

`f_EP` needs no such breakdown. Since `eqsum_L` makes only an `inl` unobservable,
`f_EP_step_sum` reduces it to a condition on `set_pending`, and the output summand
never comes up.

Each goal is self-contained, which is the point of splitting. The cost is that a
stage is proved over *all* pairs of related states. It cannot assume its input came
from the stage before it, so it must hold even for states no real run produces.
Section 4d recovers what that loses.

### 4d. `restore_invariant`: putting the forgotten invariant back

Two facts hold of every state `model_sliced` can reach. First, while the time slice
is live and no handler is running, the NOP handler is pending, the disk and
NOP masks are clear and the timer mask is set; once the slice is over, the disk and
NOP masks are set. Second, the disk and NOP masks are always toggled together. The
policy maintains both: each handler boundary reopens the masks and queues a NOP run,
and every mask update touches the disk and NOP masks alike
([`models.md` §8b](models.md)).

`fv_NI_comp` forgets both facts, because each stage is proved over all related
states. `restore_invariant` writes them back into the interrupt controller just
before `initiate_next` runs:

- it sets the controller's flags from `timeslice_live`, ORing them in. Since
  `timeslice_live` reads only the public `ir_count`, the same flags are set in two
  related states;
- it forces the NOP mask to equal the disk mask, so the `initiate_next`
  argument can assume the two are in sync.

The hard `initiate_next` stage can then assume related states take the same branch,
because `restore_invariant` has already run and made the deciding mask bits agree.

None of this changes the model's behaviour. `restore_invariant_noop`
([`models.v`](../theories/models.v)) proves that wherever `initiate_next` applies
`restore_invariant`, after any sequence of events from the initial state, it returns
the state unchanged. The proof is about the state machine alone: it states the
invariant, shows every event preserves it, and shows `restore_invariant` is the
identity on the states where it holds. It assumes `runtime ≠ 1`, for the reason
given in [`models.md` §8b](models.md). So `restore_invariant` is a device for the
proof that provably does nothing at run time, rather than a part of the policy.


## 5. How general the result is

Everything up to here has been read at one system. It is worth being precise about
how much of that system the theorem actually fixes, because the answer is: very
little. Discharging the section variables of
[`noninterference.v`](../theories/noninterference.v), `model_sliced_userview_NI`
reads in full:

```coq
forall (Opub Opriv : Ty) (runtime runs : nat)
       (p_pub : Proc Empty Opub)
       (p_priv : Proc THandlerOutput Opriv)
       (p_sched : Proc Empty Nat),
  NI (public_equiv Empty) (public_equiv Opub) p_pub ->
  NI (private_equiv THandlerOutput) (private_equiv Opriv) p_priv ->
  NI (public_equiv Empty) (public_equiv Nat) p_sched ->
  NI in_equiv (out_equiv_userview Opub Opriv)
     (model_sliced_userview runtime runs p_pub p_priv p_sched)
```

`model_sliced_NI` is the same statement at `out_equiv`, on the full pool output.
The claim is therefore about the interrupt-and-scheduling mechanism rather than
about one operating system: everything the pool is built around stays fixed, and
everything it carries is left open.

**What is left open.**

| parameter | ranges over | side condition |
|---|---|---|
| `p_pub` | any process in the public user slot | must be `NI` at `public_equiv`/`public_equiv` |
| `p_priv` | any process in the private user slot | must be `NI` at `private_equiv`/`private_equiv` |
| `p_sched` | any scheduler | must be `NI` at `public_equiv`/`public_equiv` |
| `Opub`, `Opriv` | the two user output alphabets | none |
| `runtime` | how many steps a handler runs for | none |
| `runs` | how many handler runs a slice holds | none |

The three side conditions are the expected ones: the mechanism cannot make a
leaking user process secure, so each slot is assumed non-interfering at its own
classification and the theorem adds that composing them through this mechanism
leaks nothing further. The last three carry no side condition at all.
`time_slice runtime runs = runs * runtime` makes the slice end on a handler
boundary by construction, so no arithmetic relation between the two numbers has to
be assumed.

**Why they can be left open.** Two features of the model buy it:

- **The pool's own transition never reads a user slot's output value.**
  `is_sched_out` matches `(None,(None,(Some n,_)))`, inspecting the user slots only
  for `None`-ness, so no user behaviour reaches the schedule.
- **`fv_NI` (section 4) never mentions the slot processes**, so the one hard
  obligation is unaffected by what fills them.

**Levels.** These documents read levels as two, the attacker `⊥` and an observer
`⊤` who sees everything. The mechanisation works over an arbitrary bounded lattice
(the parameters `d` and `L` of [`definitions.v`](../theories/definitions.v)). There
a `cEquiv` must also be monotone downwards: whatever a level relates stays related
below it, and whatever is unobservable at a level stays unobservable below it. `NI`
quantifies over every level. Nothing in the proofs depends on the lattice having two
points, because every equivalence in the models distinguishes `⊥` from all other
levels and nothing more. The level case splits in the proof (section 3a) are
`l = ⊥` against `l ≠ ⊥`, and the second case covers every other level of any
lattice at once.

**What stays fixed.** The three interrupt handlers, which are the mechanism under
study, and the shape of the pool around them: six slots, the last of them padding.
The scheduler and user slot *processes* are open, but their number and position are
not. The output projections `is_sched_out`, `tI_out`, `dI_out` and `nop_ir_out`
are tuple patterns, and they hardwire two user slots ahead of the scheduler slot.
Varying the count changes the state transition and lands inside `fv_NI`.

**Recovering one system.** Instantiating with `p_pub_concrete_NI`,
`p_priv_concrete_NI` and `scheduler_NI` gives the concrete system back, as
`model_sliced_concrete_NI` and `model_sliced_userview_concrete_NI`. The refutation
goes the other way: `model_immediate` is open in exactly the same parameters, but a
counterexample need exhibit only one system, so `model_immediate_not_NI` is stated
at `model_immediate_concrete` (section 2).


## 6. Model limitations

Two simplifications keep the proof tractable. Both are limitations of the model
rather than of the technique, and either could be lifted at the cost of a harder
`fv_NI` (section 4).

**(a) Only one secret interrupt.** The NOP handler exists purely for privacy, as
the disk handler's indistinguishable partner, and the sliced policy schedules it itself,
at every handler boundary. It has an entry in the interrupt controller (`nop_irq`)
but no external interrupt: the input type has only the timer and disk interrupts.
Several secret interrupts would need a correspondingly richer indistinguishability
argument.

**(b) Same-length handler execution.** Every handler runs for the same fixed number
of output steps, which is what lets all masks be public (4b). Handlers finish on
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
- **One-step handlers are degenerate.** At `runtime = 1` a slice loses its last
  handler run: the boundary that should start it ticks the counter to `Some 0` in
  the same step, so the slice already reads as over. Non-interference still holds,
  since it says nothing about how many runs a slice contains, but
  `restore_invariant_noop` excludes this case ([`models.md` §8b](models.md)).
