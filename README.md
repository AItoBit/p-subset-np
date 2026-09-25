# P ⊆ NP

A Lean 4 proof of `ComplexityTheory.P ⊆ ComplexityTheory.NP` for the definitions in
[`FormalConjecturesForMathlib/Computability/Complexity.lean`](https://github.com/google-deepmind/formal-conjectures/blob/2424bb480c590237ffbb2cc831ae4cb8977e045a/FormalConjecturesForMathlib/Computability/Complexity.lean)
of [formal-conjectures](https://github.com/google-deepmind/formal-conjectures).

The main theorem is `ComplexityTheory.P_subset_NP'` in [`PSubsetNP.lean`](PSubsetNP.lean).
It depends only on the standard axioms:

```
'ComplexityTheory.P_subset_NP'' depends on axioms: [propext, Classical.choice, Quot.sound]
```

## Proof idea

Given a polynomial-time decider for `L`, the verifier `fun (x, w) => L x` ignores the witness.
Mathlib does not yet prove that polynomial-time Turing machines compose, so
`IsPolyTime.comp_fst` builds the verifier machine explicitly. It parses the self-delimiting
block that encodes `x`, erases the encoding of `w`, copies `x` to the input stack of the
decider, and then simulates the decider step by step. The running time is
`2 n + 2 + T(n)`, where `T` bounds the decider.

## Build

```bash
lake build
```
