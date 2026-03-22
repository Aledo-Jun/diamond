# traceNormOp

## Source location

- Original Lean file: `Diamond/Setups.lean`
- Declaration name: `traceNormOp`
- Declaration kind: `abbrev`

## Why this declaration exists

This abbrev introduces the object named `traceNormOp`. Its name suggests the mathematical role: trace Norm Op.

 In the file `Setups.lean`, it contributes to foundational objects and notational definitions for operators, channels, norms, and the maps studied in the paper. Later declarations use this name instead of repeatedly expanding the underlying matrix formula.

## Original code

```lean
abbrev traceNormOp
    {d : Type u} [Fintype d] [DecidableEq d] (X : Matrix d d ℂ) : ℝ :=
  traceNorm X
```

## Block-by-block explanation

The explanation below follows the declaration block by block. Each block groups a coherent piece of the definition or proof, so the mathematical structure is easier to see than in a strictly line-oriented reading.

1. Code:
```lean
abbrev traceNormOp
```
This line starts the `traceNormOp` declaration. Because it begins with `abbrev`, Lean now knows what kind of named object is being introduced.

2. Code:
```lean
    {d : Type u} [Fintype d] [DecidableEq d] (X : Matrix d d ℂ) : ℝ :=
```
This line is one local step in the declaration. It either refines the formula being defined or advances the proof by a small algebraic or logical move.  `Matrix d d ℂ` means a square matrix with complex entries; the index type `d` tells Lean which rows and columns exist.  A bracket such as `[Fintype d]` tells Lean that the index set `d` is finite, so sums over all indices make sense.  A bracket such as `[DecidableEq d]` tells Lean that it can decide whether two indices are equal.

3. Code:
```lean
  traceNorm X
```
This line is one local step in the declaration. It either refines the formula being defined or advances the proof by a small algebraic or logical move.

## Mathematical summary

In ordinary mathematical language, `traceNormOp` is the project's formal Lean name for the object introduced in this declaration.

## Dependencies and downstream use

### Earlier declarations this depends on
- [`traceNorm`](traceNorm.md) from `Setups.lean`

### Later declarations that use this one
- [`diamondNorm`](diamondNorm.md) in `Setups.lean`
- [`diamondNormAt`](diamondNormAt.md) in `Setups.lean`
- [`trNorm_nonneg`](../StandardFacts/trNorm_nonneg.md) in `StandardFacts.lean`
- [`diamond_le_of_pointwise`](../StandardFacts/diamond_le_of_pointwise.md) in `StandardFacts.lean`
- [`traceNorm_apply_le_diamond`](../StandardFacts/traceNorm_apply_le_diamond.md) in `StandardFacts.lean`
- [`exists_maximizing_state`](../StandardFacts/exists_maximizing_state.md) in `StandardFacts.lean`
- [`traceNormOp_mul_left_isometry`](../Theorem/Lemma1/traceNormOp_mul_left_isometry.md) in `Theorem/Lemma1.lean`
- [`traceNormOp_diagonal`](../Theorem/Lemma1/traceNormOp_diagonal.md) in `Theorem/Lemma1.lean`
- [`traceNormOp_conjTranspose`](../Theorem/Lemma1/traceNormOp_conjTranspose.md) in `Theorem/Lemma1.lean`
- [`traceNormOp_mul_right_isometry`](../Theorem/Lemma1/traceNormOp_mul_right_isometry.md) in `Theorem/Lemma1.lean`
- [`traceNormOp_hermitian_eq_sum_abs_eigenvalues`](../Theorem/Lemma1/traceNormOp_hermitian_eq_sum_abs_eigenvalues.md) in `Theorem/Lemma1.lean`
- [`lemma1`](../Theorem/Lemma1/lemma1.md) in `Theorem/Lemma1.lean`
- [`traceNormOp_posSemidef_eq_trace`](../Theorem/Lemma1/traceNormOp_posSemidef_eq_trace.md) in `Theorem/Lemma1.lean`
- [`traceNormOp_density_eq_one`](../Theorem/Lemma1/traceNormOp_density_eq_one.md) in `Theorem/Lemma1.lean`
- [`traceNormOp_sub_density_le_two`](../Theorem/Lemma1/traceNormOp_sub_density_le_two.md) in `Theorem/Lemma1.lean`
- [`traceNormOp_eq_of_conjTranspose_mul_self_eq`](../Theorem/Lemma1/traceNormOp_eq_of_conjTranspose_mul_self_eq.md) in `Theorem/Lemma1.lean`
- [`lemma2`](../Theorem/Lemma2/lemma2.md) in `Theorem/Lemma2.lean`
- [`theorem1`](../Theorem/Theorem1/theorem1.md) in `Theorem/Theorem1.lean`
- [`remark1`](../Theorem/Remark1/remark1.md) in `Theorem/Remark1.lean`
- [`lemma1_eq_imp_rank_two`](../PositiveGap/NotTight/lemma1_eq_imp_rank_two.md) in `PositiveGap/NotTight.lean`
- [`lemma2_eq_imp_full_rank`](../PositiveGap/NotTight/lemma2_eq_imp_full_rank.md) in `PositiveGap/NotTight.lean`
- [`theorem_not_tight`](../PositiveGap/NotTight/theorem_not_tight.md) in `PositiveGap/NotTight.lean`
- [`theorem_eq7_witness_bound`](../EndMatter/Eq7/theorem_eq7_witness_bound.md) in `EndMatter/Eq7.lean`
- [`theorem_eq7_witness_bound_explicit`](../EndMatter/Eq7/theorem_eq7_witness_bound_explicit.md) in `EndMatter/Eq7.lean`
- [`explicit_witness_traceNorm_eq_sum`](../EndMatter/Eq7/explicit_witness_traceNorm_eq_sum.md) in `EndMatter/Eq7.lean`
- [`explicit_witness_traceNorm_eq`](../EndMatter/Eq7/explicit_witness_traceNorm_eq.md) in `EndMatter/Eq7.lean`
- [`theorem_eq7`](../EndMatter/Eq7/theorem_eq7.md) in `EndMatter/Eq7.lean`

## Backlinks

- [Back to `INDEX.md`](../INDEX.md)
- [Back to the `Setups.lean` section in the index](../INDEX.md#diamond-setups-lean)
- [Previous declaration in this file](traceNorm.md)
- [Next declaration in this file](hsNormOp.md)