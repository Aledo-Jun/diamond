# hsNormOp

## Source location

- Original Lean file: `Diamond/Setups.lean`
- Declaration name: `hsNormOp`
- Declaration kind: `abbrev`

## Why this declaration exists

This abbrev introduces the object named `hsNormOp`. Its name suggests the mathematical role: hs Norm Op.

 In the file `Setups.lean`, it contributes to foundational objects and notational definitions for operators, channels, norms, and the maps studied in the paper. Later declarations use this name instead of repeatedly expanding the underlying matrix formula.

## Original code

```lean
abbrev hsNormOp
    {m n : Type u} [Fintype m] [DecidableEq m] [Fintype n] [DecidableEq n]
    (X : Matrix m n ℂ) : ℝ :=
  hsNorm X
```

## Block-by-block explanation

The explanation below follows the declaration block by block. Each block groups a coherent piece of the definition or proof, so the mathematical structure is easier to see than in a strictly line-oriented reading.

1. Code:
```lean
abbrev hsNormOp
```
This line starts the `hsNormOp` declaration. Because it begins with `abbrev`, Lean now knows what kind of named object is being introduced.

2. Code:
```lean
    {m n : Type u} [Fintype m] [DecidableEq m] [Fintype n] [DecidableEq n]
```
This line is one local step in the declaration. It either refines the formula being defined or advances the proof by a small algebraic or logical move.  A bracket such as `[Fintype d]` tells Lean that the index set `d` is finite, so sums over all indices make sense.  A bracket such as `[DecidableEq d]` tells Lean that it can decide whether two indices are equal.

3. Code:
```lean
    (X : Matrix m n ℂ) : ℝ :=
```
This line is one local step in the declaration. It either refines the formula being defined or advances the proof by a small algebraic or logical move.  `Matrix d d ℂ` means a square matrix with complex entries; the index type `d` tells Lean which rows and columns exist.

4. Code:
```lean
  hsNorm X
```
This line is one local step in the declaration. It either refines the formula being defined or advances the proof by a small algebraic or logical move.

## Mathematical summary

In ordinary mathematical language, `hsNormOp` is the project's formal Lean name for the object introduced in this declaration.

## Dependencies and downstream use

### Earlier declarations this depends on
- [`hsNorm`](hsNorm.md) from `Setups.lean`

### Later declarations that use this one
- [`hsNorm_nonneg`](../StandardFacts/hsNorm_nonneg.md) in `StandardFacts.lean`
- [`hsNormOp_eq_zero_iff`](../StandardFacts/hsNormOp_eq_zero_iff.md) in `StandardFacts.lean`
- [`hsNorm_sq_eq_re_trace_conjTranspose_mul_self`](../Theorem/Lemma1/hsNorm_sq_eq_re_trace_conjTranspose_mul_self.md) in `Theorem/Lemma1.lean`
- [`lemma1`](../Theorem/Lemma1/lemma1.md) in `Theorem/Lemma1.lean`
- [`hsNorm_sq_eq_re_trace_conjTranspose_mul_self`](../Theorem/Lemma2/hsNorm_sq_eq_re_trace_conjTranspose_mul_self.md) in `Theorem/Lemma2.lean`
- [`lemma2`](../Theorem/Lemma2/lemma2.md) in `Theorem/Lemma2.lean`
- [`lemma3`](../Theorem/Lemma3/lemma3.md) in `Theorem/Lemma3.lean`
- [`theorem1`](../Theorem/Theorem1/theorem1.md) in `Theorem/Theorem1.lean`
- [`remark1`](../Theorem/Remark1/remark1.md) in `Theorem/Remark1.lean`
- [`lemma1_eq_imp_rank_two`](../PositiveGap/NotTight/lemma1_eq_imp_rank_two.md) in `PositiveGap/NotTight.lean`
- [`lemma2_eq_imp_full_rank`](../PositiveGap/NotTight/lemma2_eq_imp_full_rank.md) in `PositiveGap/NotTight.lean`
- [`partialTranspose_ne_zero_of_ne_zero`](../PositiveGap/NotTight/partialTranspose_ne_zero_of_ne_zero.md) in `PositiveGap/NotTight.lean`
- [`theorem_not_tight`](../PositiveGap/NotTight/theorem_not_tight.md) in `PositiveGap/NotTight.lean`

## Backlinks

- [Back to `INDEX.md`](../INDEX.md)
- [Back to the `Setups.lean` section in the index](../INDEX.md#diamond-setups-lean)
- [Previous declaration in this file](traceNormOp.md)
- [Next declaration in this file](IsDensityState.md)