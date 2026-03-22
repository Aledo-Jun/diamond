# diamondNormAt

## Source location

- Original Lean file: `Diamond/Setups.lean`
- Declaration name: `diamondNormAt`
- Declaration kind: `def`

## Why this declaration exists

This is a fixed-ancilla version of the diamond norm, used to implement the standard finite-dimensional reduction $k=d$.

 In the file `Setups.lean`, it contributes to foundational objects and notational definitions for operators, channels, norms, and the maps studied in the paper. Later declarations use this name instead of repeatedly expanding the underlying matrix formula.

## Original code

```lean
/-- Fixed-ancilla stabilization of `Φ`, used for the standard `k = d` reduction. -/
def diamondNormAt
    {d k : Type u} [Fintype d] [DecidableEq d] [Fintype k] [DecidableEq k]
    (Φ : Channel d) : ℝ :=
  sSup {r : ℝ | ∃ ρ : DensityState (d × k),
    r = traceNormOp (tensorWithIdentity d k Φ ρ.1)}
```

## Block-by-block explanation

The explanation below follows the declaration block by block. Each block groups a coherent piece of the definition or proof, so the mathematical structure is easier to see than in a strictly line-oriented reading.

1. Code:
```lean
/-- Fixed-ancilla stabilization of `Φ`, used for the standard `k = d` reduction. -/
```
This is a Lean docstring. It is a human-written comment that tells readers what the declaration is meant to express before the formal code begins.

2. Code:
```lean
def diamondNormAt
```
This line starts the `diamondNormAt` declaration. Because it begins with `def`, Lean now knows what kind of named object is being introduced.

3. Code:
```lean
    {d k : Type u} [Fintype d] [DecidableEq d] [Fintype k] [DecidableEq k]
```
This line is one local step in the declaration. It either refines the formula being defined or advances the proof by a small algebraic or logical move.  A bracket such as `[Fintype d]` tells Lean that the index set `d` is finite, so sums over all indices make sense.  A bracket such as `[DecidableEq d]` tells Lean that it can decide whether two indices are equal.

4. Code:
```lean
    (Φ : Channel d) : ℝ :=
```
This line is one local step in the declaration. It either refines the formula being defined or advances the proof by a small algebraic or logical move.  `Channel d` is an abbreviation for a complex-linear map from operators on `d` to operators on `d`.

5. Code:
```lean
  sSup {r : ℝ | ∃ ρ : DensityState (d × k),
```
This line is one local step in the declaration. It either refines the formula being defined or advances the proof by a small algebraic or logical move.  `sSup` is Lean’s notation for the supremum, the least upper bound of a set of real numbers.

6. Code:
```lean
    r = traceNormOp (tensorWithIdentity d k Φ ρ.1)}
```
This line is one local step in the declaration. It either refines the formula being defined or advances the proof by a small algebraic or logical move.

## Mathematical summary

In ordinary mathematical language, `diamondNormAt` is the project's formal Lean name for the object introduced in this declaration.

## Dependencies and downstream use

### Earlier declarations this depends on
- [`Channel`](Channel.md) from `Setups.lean`
- [`traceNormOp`](traceNormOp.md) from `Setups.lean`
- [`DensityState`](DensityState.md) from `Setups.lean`
- [`tensorWithIdentity`](tensorWithIdentity.md) from `Setups.lean`

### Later declarations that use this one
- [`diamondOp`](diamondOp.md) in `Setups.lean`
- [`diamond_le_of_pointwise`](../StandardFacts/diamond_le_of_pointwise.md) in `StandardFacts.lean`
- [`traceNorm_apply_le_diamond`](../StandardFacts/traceNorm_apply_le_diamond.md) in `StandardFacts.lean`
- [`theorem1`](../Theorem/Theorem1/theorem1.md) in `Theorem/Theorem1.lean`
- [`remark1`](../Theorem/Remark1/remark1.md) in `Theorem/Remark1.lean`

## Backlinks

- [Back to `INDEX.md`](../INDEX.md)
- [Back to the `Setups.lean` section in the index](../INDEX.md#diamond-setups-lean)
- [Previous declaration in this file](diamondNorm.md)
- [Next declaration in this file](diamondOp.md)