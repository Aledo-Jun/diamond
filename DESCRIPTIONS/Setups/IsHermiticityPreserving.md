# IsHermiticityPreserving

## Source location

- Original Lean file: `Diamond/Setups.lean`
- Declaration name: `IsHermiticityPreserving`
- Declaration kind: `def`

## Why this declaration exists

This definition captures the property that a linear map sends Hermitian matrices to Hermitian matrices.

 In the file `Setups.lean`, it contributes to foundational objects and notational definitions for operators, channels, norms, and the maps studied in the paper. Later declarations use this name instead of repeatedly expanding the underlying matrix formula.

## Original code

```lean
def IsHermiticityPreserving
    {d : Type u} [Fintype d] [DecidableEq d] (Φ : Channel d) : Prop :=
  ∀ X, Φ Xᴴ = (Φ X)ᴴ
```

## Line-by-line explanation

The explanation below follows the declaration one physical line at a time. For long proofs, some lines are tiny bookkeeping steps; those are still explained, but briefly.

1. Code:
```lean
def IsHermiticityPreserving
```
This line starts the `IsHermiticityPreserving` declaration. Because it begins with `def`, Lean now knows what kind of named object is being introduced.

2. Code:
```lean
    {d : Type u} [Fintype d] [DecidableEq d] (Φ : Channel d) : Prop :=
```
This line is one local step in the declaration. It either refines the formula being defined or advances the proof by a small algebraic or logical move.  `Channel d` is an abbreviation for a complex-linear map from operators on `d` to operators on `d`.  A bracket such as `[Fintype d]` tells Lean that the index set `d` is finite, so sums over all indices make sense.  A bracket such as `[DecidableEq d]` tells Lean that it can decide whether two indices are equal.

3. Code:
```lean
  ∀ X, Φ Xᴴ = (Φ X)ᴴ
```
This line is one local step in the declaration. It either refines the formula being defined or advances the proof by a small algebraic or logical move.  The superscript `ᴴ` means conjugate transpose (also called the adjoint).

## Mathematical summary

In ordinary mathematical language, `IsHermiticityPreserving` is the project's formal Lean name for the object introduced in this declaration.

## Dependencies and downstream use

### Earlier declarations this depends on
- [`Channel`](Channel.md) from `Setups.lean`

### Later declarations that use this one
- [`IsQuantumChannel`](IsQuantumChannel.md) in `Setups.lean`
- [`idMinus_isHermiticityPreserving`](../StandardFacts/idMinus_isHermiticityPreserving.md) in `StandardFacts.lean`
- [`tensorWithIdentity_hermitian`](../StandardFacts/tensorWithIdentity_hermitian.md) in `StandardFacts.lean`
- [`remark1`](../Theorem/Remark1/remark1.md) in `Theorem/Remark1.lean`

## Backlinks

- [Back to `INDEX.md`](../INDEX.md)
- [Back to the `Setups.lean` section in the index](../INDEX.md#diamond-setups-lean)
- [Previous declaration in this file](DensityState.md)
- [Next declaration in this file](IsQuantumChannel.md)