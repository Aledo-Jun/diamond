# traceNorm

## Source location

- Original Lean file: `Diamond/Setups.lean`
- Declaration name: `traceNorm`
- Declaration kind: `def`

## Why this declaration exists

This definition gives the trace norm as the sum of singular values, written in Lean via eigenvalues of $X^\dagger X$.

 In the file `Setups.lean`, it contributes to foundational objects and notational definitions for operators, channels, norms, and the maps studied in the paper. Later declarations use this name instead of repeatedly expanding the underlying matrix formula.

## Original code

```lean
/-- Trace norm, realized as the sum of the singular values. -/
def traceNorm
    {d : Type u} [Fintype d] [DecidableEq d] (X : Matrix d d ℂ) : ℝ :=
  ∑ i, Real.sqrt ((Matrix.isHermitian_conjTranspose_mul_self X).eigenvalues i)
```

## Line-by-line explanation

The explanation below follows the declaration one physical line at a time. For long proofs, some lines are tiny bookkeeping steps; those are still explained, but briefly.

1. Code:
```lean
/-- Trace norm, realized as the sum of the singular values. -/
```
This is a Lean docstring. It is a human-written comment that tells readers what the declaration is meant to express before the formal code begins.

2. Code:
```lean
def traceNorm
```
This line starts the `traceNorm` declaration. Because it begins with `def`, Lean now knows what kind of named object is being introduced.

3. Code:
```lean
    {d : Type u} [Fintype d] [DecidableEq d] (X : Matrix d d ℂ) : ℝ :=
```
This line is one local step in the declaration. It either refines the formula being defined or advances the proof by a small algebraic or logical move.  `Matrix d d ℂ` means a square matrix with complex entries; the index type `d` tells Lean which rows and columns exist.  A bracket such as `[Fintype d]` tells Lean that the index set `d` is finite, so sums over all indices make sense.  A bracket such as `[DecidableEq d]` tells Lean that it can decide whether two indices are equal.

4. Code:
```lean
  ∑ i, Real.sqrt ((Matrix.isHermitian_conjTranspose_mul_self X).eigenvalues i)
```
This line is one local step in the declaration. It either refines the formula being defined or advances the proof by a small algebraic or logical move.

## Mathematical summary

In ordinary mathematical language, `traceNorm` is the project's formal Lean name for the object introduced in this declaration.

## Dependencies and downstream use

### Earlier declarations this depends on
- This declaration does not explicitly cite an earlier named declaration from the documented tree; it mostly uses Lean primitives or local algebraic steps.

### Later declarations that use this one
- [`traceNormOp`](traceNormOp.md) in `Setups.lean`
- [`traceNormOp_mul_left_isometry`](../Theorem/Lemma1/traceNormOp_mul_left_isometry.md) in `Theorem/Lemma1.lean`
- [`traceNormOp_diagonal`](../Theorem/Lemma1/traceNormOp_diagonal.md) in `Theorem/Lemma1.lean`
- [`traceNormOp_conjTranspose`](../Theorem/Lemma1/traceNormOp_conjTranspose.md) in `Theorem/Lemma1.lean`
- [`traceNormOp_eq_of_conjTranspose_mul_self_eq`](../Theorem/Lemma1/traceNormOp_eq_of_conjTranspose_mul_self_eq.md) in `Theorem/Lemma1.lean`

## Backlinks

- [Back to `INDEX.md`](../INDEX.md)
- [Back to the `Setups.lean` section in the index](../INDEX.md#diamond-setups-lean)
- [Previous declaration in this file](hsNorm.md)
- [Next declaration in this file](traceNormOp.md)