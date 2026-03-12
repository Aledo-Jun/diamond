# IsDensityState

## Source location

- Original Lean file: `Diamond/Setups.lean`
- Declaration name: `IsDensityState`
- Declaration kind: `def`

## Why this declaration exists

This predicate expresses the usual quantum-information notion of a density matrix: positive semidefinite with trace one.

 In the file `Setups.lean`, it contributes to foundational objects and notational definitions for operators, channels, norms, and the maps studied in the paper. Later declarations use this name instead of repeatedly expanding the underlying matrix formula.

## Original code

```lean
def IsDensityState
    {d : Type u} [Fintype d] [DecidableEq d] (ρ : Matrix d d ℂ) : Prop :=
  Matrix.PosSemidef ρ ∧ Matrix.trace ρ = 1
```

## Line-by-line explanation

The explanation below follows the declaration one physical line at a time. For long proofs, some lines are tiny bookkeeping steps; those are still explained, but briefly.

1. Code:
```lean
def IsDensityState
```
This line starts the `IsDensityState` declaration. Because it begins with `def`, Lean now knows what kind of named object is being introduced.

2. Code:
```lean
    {d : Type u} [Fintype d] [DecidableEq d] (ρ : Matrix d d ℂ) : Prop :=
```
This line is one local step in the declaration. It either refines the formula being defined or advances the proof by a small algebraic or logical move.  `Matrix d d ℂ` means a square matrix with complex entries; the index type `d` tells Lean which rows and columns exist.  A bracket such as `[Fintype d]` tells Lean that the index set `d` is finite, so sums over all indices make sense.  A bracket such as `[DecidableEq d]` tells Lean that it can decide whether two indices are equal.

3. Code:
```lean
  Matrix.PosSemidef ρ ∧ Matrix.trace ρ = 1
```
This line is one local step in the declaration. It either refines the formula being defined or advances the proof by a small algebraic or logical move.  `PosSemidef` is Lean’s name for “positive semidefinite”.

## Mathematical summary

In ordinary mathematical language, `IsDensityState` is the project's formal Lean name for the object introduced in this declaration.

## Dependencies and downstream use

### Earlier declarations this depends on
- This declaration does not explicitly cite an earlier named declaration from the documented tree; it mostly uses Lean primitives or local algebraic steps.

### Later declarations that use this one
- [`DensityState`](DensityState.md) in `Setups.lean`
- [`tensorWithIdentity_hermitian`](../StandardFacts/tensorWithIdentity_hermitian.md) in `StandardFacts.lean`
- [`traceNormOp_density_eq_one`](../Theorem/Lemma1/traceNormOp_density_eq_one.md) in `Theorem/Lemma1.lean`
- [`traceNormOp_sub_density_le_two`](../Theorem/Lemma1/traceNormOp_sub_density_le_two.md) in `Theorem/Lemma1.lean`
- [`phiState_isDensityState`](../EndMatter/Eq7/phiState_isDensityState.md) in `EndMatter/Eq7.lean`

## Backlinks

- [Back to `INDEX.md`](../INDEX.md)
- [Back to the `Setups.lean` section in the index](../INDEX.md#diamond-setups-lean)
- [Previous declaration in this file](hsNormOp.md)
- [Next declaration in this file](DensityState.md)