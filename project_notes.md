
# Overview 

## Project Goals

- Understand presence of timing leaks (timing-sensitive non-interference TSNI) in operating systems (OS)
- Propose methods for achieving TSNI in OS
- Evaluate methods for achieving TSNI in OS

## Observations

- "Optimization is the enemy of security" (folklore)
- Modern OS us interrupts to optimize process availability
  + e.g. disc reads schedule reading process when data is ready
- Interrupt optimization cause timing side-channel
  + Consider processes `p1 := loop (echo "foo")` and `p2 := loop disc_read`
  + `p1` outputs (low sensitivity) signals
  + `p2` eventually trigger a (high sensitivity) disc interrupt
  + An attacker can observe the timing stagger of `p1` outputs, caused by `p2` disc read
- We can eliminate leak by instead scheduling processes round robin

## Problems

1. How can we guarantee leak is eliminated?
 1a. How can we model the OS and detect the leak?
 2b. How can we model the proposed solution, and prove that it works?
2. How can we know that the proposed solution is feasible ?
 2a. How readily can it be adopted in modern OS?
 2b. How performant is the OS with the change?
 
## Solutions

1. Use approach proposed by Rafnsson et al. [POST'17] to model OS, solution, and verify TSNI
2. Investigate existing (simple) operating systems, implement solution, and evaluate performance

# Overview of solution 1

Rafnsson et al. [POST'17] propose a high-level combinator language for modeling I/O processes and verifying their TSNI by composition: https://www.willardthor.com/pub/2017post/2017post-rafnsson-jia-bauer.pdf

## Combinator Language Example

Processes are modelled in terms of their inputs and outputs: `Proc I O`.
The process `p1 := loop (echo "foo")` can be modelled as `Proc _ {"foo"}`.

Combinators can be used to built complex processes, such as

`maybe p` lets processes handle "no input", throwing away `None`, and forwarding `Some i`:
`maybe p1 : Proc (_?) {"foo"}`

`par p1 p2` parallelizes processes:
`par (maybe p1) p2`

Combinators respect TSNI under certain conditions, which lets us verify TSNI of complex composites relatively easily.

## Our Approach

We give a simple model of an operating system as a process pool and interrupt mitigator.

The process pool (limited to 2 processes) has exactly one process enabled at all times, and can receive inputs to change the enabled process.

The interrupt mitigator intercept interrupts and instead schedule the thread pool round robin.

We prove TSNI of the process pool, which depends on the elimination of flows from outputs to scheduling input.

We prove that the mitigator eliminates the flow by intercepting interrupts and fixing scheduling input round robin.

## Model of process pool and interrupt mitigator

Process pool:
```
par_swiI (b:bool) (p1 : Proc I1 O1) (p2 : Proc I2 O2) : Proc (bool * (I1 * I2)) (O1 + O2) :=
  mapO (if b then inl ∘ option_elim ∘ fst else inr ∘ option_elim ∘ snd) $
    par
    (swiI b $ mapI fst p1)
    (swiI (negb b) $ mapI snd p2).
```

Interrupt mitigator:
```
naive_mitigator (p : Proc (bool * I) O) : Proc I O :=
  mapI (λ i, (true,i)) $ p.
```

Note that the mitigator is naive, and flips the active process every clock tick.

A more realistic mitigator that flips every `n` tick is given as:
```
mitigator {I O} n (p : Proc (bool * I) O) : Proc I O :=
  mapO snd $
  staI (λ _ v, (v.1+1, Nat.eqb (v.1 `mod` n) 0)) (0,inhabitant) $
  mapI (λ (nbi : ((nat * bool) * I)), (nbi.1.2,nbi.2)) $
  p.
```

We believe that `mitigator` is TSNI iff `naive_mitigator` is TSNI.

## Thoughts on Non-Interference

`par_swiI b p1 p2 : Proc (B*I1*I2) (O1+O2)` is non-interfering whenever
- Flip inputs B are low (i.e. presence of scheduling is low)
  + Handled externally
- High I1 inputs (resp. I2) does not interfere with Low O1 outputs (resp. O2) (no explicit internal flows)
  + Handled internally
- High outputs of one process does not interfere with low inputs on another (no explicit external flows)
  + Handled externally

`mitigator p` is non-interfering whenever
- High I1 inputs (resp. I2) does not interfere with Low O1 outputs (resp. O2) (no explicit internal flows)
  + Handled internally
- High outputs of one process does not interfere with low inputs on another (no explicit external flows)
  + Handled externally

## Formally defined TSNI specifications

`par_swiI b p1 p2` is in NI(=^{B*I1*I2},=^{O1+O2}) whenever
- (=^{I1*I2}) = eqpair(=^{I1},=^{I2})
- (=^{B*I1*I2}) = eqpair•LR(=^{B},=^{I1*I2})
- (=^{O1+O2}) = eqsum(L1, L2, (=^{O1+O2}))
- L1 = A(True,  (=^{B}))
- L2 = A(False, (=^{B}))
- ∀ l. l ∈ L1 ∪ O(p1, =^{O1})
- ∀ l. l ∈ L2 ∪ O(p2, =^{O2})
- `p1` is in NI(=^{I1},=^{O1})
- `p2` is in NI(=^{I2},=^{O2})

`mitigator p` is NI(=^{I},=^{O}) whenever
- `p` is in NI(=^{I},=^{O})


Note that proofs are TBD.
As such, specifications may not be entirely correct.


## Overview of solution 2

TBD

# Future Work

TBD
