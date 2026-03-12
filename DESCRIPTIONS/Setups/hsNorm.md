# hsNorm

## Source location

- Original Lean file: `Diamond/Setups.lean`
- Declaration name: `hsNorm`
- Declaration kind: `def`

## Why this declaration exists

This definition gives the Hilbert--Schmidt norm, implemented using Lean's Frobenius norm on matrices.

 In the file `Setups.lean`, it contributes to foundational objects and notational definitions for operators, channels, norms, and the maps studied in the paper. Later declarations use this name instead of repeatedly expanding the underlying matrix formula.

## Original code

```lean
/-- Hilbert--Schmidt norm, realized by the Frobenius norm. -/
def hsNorm
    {m n : Type u} [Fintype m] [DecidableEq m] [Fintype n] [DecidableEq n]
    (X : Matrix m n ℂ) : ℝ :=
  ‖X‖
```

## Line-by-line explanation

The explanation below follows the declaration one physical line at a time. For long proofs, some lines are tiny bookkeeping steps; those are still explained, but briefly.

1. Code:
```lean
/-- Hilbert--Schmidt norm, realized by the Frobenius norm. -/
```
This is a Lean docstring. It is a human-written comment that tells readers what the declaration is meant to express before the formal code begins.

2. Code:
```lean
def hsNorm
```
This line starts the `hsNorm` declaration. Because it begins with `def`, Lean now knows what kind of named object is being introduced.

3. Code:
```lean
    {m n : Type u} [Fintype m] [DecidableEq m] [Fintype n] [DecidableEq n]
```
This line is one local step in the declaration. It either refines the formula being defined or advances the proof by a small algebraic or logical move.  A bracket such as `[Fintype d]` tells Lean that the index set `d` is finite, so sums over all indices make sense.  A bracket such as `[DecidableEq d]` tells Lean that it can decide whether two indices are equal.

4. Code:
```lean
    (X : Matrix m n ℂ) : ℝ :=
```
This line is one local step in the declaration. It either refines the formula being defined or advances the proof by a small algebraic or logical move.  `Matrix d d ℂ` means a square matrix with complex entries; the index type `d` tells Lean which rows and columns exist.

5. Code:
```lean
  ‖X‖
```
This line is one local step in the declaration. It either refines the formula being defined or advances the proof by a small algebraic or logical move.

## Mathematical summary

In ordinary mathematical language, `hsNorm` is the project's formal Lean name for the object introduced in this declaration.

## Dependencies and downstream use

### Earlier declarations this depends on
- This declaration does not explicitly cite an earlier named declaration from the documented tree; it mostly uses Lean primitives or local algebraic steps.

### Later declarations that use this one
- [`hsNormOp`](hsNormOp.md) in `Setups.lean`
- [`hsNorm_nonneg`](../StandardFacts/hsNorm_nonneg.md) in `StandardFacts.lean`
- [`hsNormOp_eq_zero_iff`](../StandardFacts/hsNormOp_eq_zero_iff.md) in `StandardFacts.lean`

## Backlinks

- [Back to `INDEX.md`](../INDEX.md)
- [Back to the `Setups.lean` section in the index](../INDEX.md#diamond-setups-lean)
- [Previous declaration in this file](Channel.md)
- [Next declaration in this file](traceNorm.md)