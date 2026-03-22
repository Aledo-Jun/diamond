# swapMatrix

## Source location

- Original Lean file: `Diamond/PositiveGap/Lemma6.lean`
- Declaration name: `swapMatrix`
- Declaration kind: `def`

## Why this declaration exists

This definition introduces the swap operator $F$, which exchanges the two tensor factors.

 In the file `PositiveGap/Lemma6.lean`, it contributes to the swap operator and its algebraic interaction with tensor products. Later declarations use this name instead of repeatedly expanding the underlying matrix formula.

## Original code

```lean
/-- Paper Definition 2: the swap operator `F`. -/
def swapMatrix (d : ℕ) : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ :=
  fun i j => if i.1 = j.2 ∧ i.2 = j.1 then 1 else 0
```

## Block-by-block explanation

The explanation below follows the declaration block by block. Each block groups a coherent piece of the definition or proof, so the mathematical structure is easier to see than in a strictly line-oriented reading.

1. Code:
```lean
/-- Paper Definition 2: the swap operator `F`. -/
```
This is a Lean docstring. It is a human-written comment that tells readers what the declaration is meant to express before the formal code begins.

2. Code:
```lean
def swapMatrix (d : ℕ) : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ :=
```
This line starts the `swapMatrix` declaration. Because it begins with `def`, Lean now knows what kind of named object is being introduced. The type information on this line explains what sort of mathematical object the declaration talks about.  `Matrix d d ℂ` means a square matrix with complex entries; the index type `d` tells Lean which rows and columns exist.

3. Code:
```lean
  fun i j => if i.1 = j.2 ∧ i.2 = j.1 then 1 else 0
```
This line is one local step in the declaration. It either refines the formula being defined or advances the proof by a small algebraic or logical move.

## Mathematical summary

In ordinary mathematical language, `swapMatrix` is the project's formal Lean name for the object introduced in this declaration.

## Dependencies and downstream use

### Earlier declarations this depends on
- This declaration does not explicitly cite an earlier named declaration from the documented tree; it mostly uses Lean primitives or local algebraic steps.

### Later declarations that use this one
- [`swapMatrix_mul_self`](swapMatrix_mul_self.md) in `PositiveGap/Lemma6.lean`
- [`swapMatrix_conjTranspose`](swapMatrix_conjTranspose.md) in `PositiveGap/Lemma6.lean`
- [`swapMatrix_conjTranspose_mul_self`](swapMatrix_conjTranspose_mul_self.md) in `PositiveGap/Lemma6.lean`
- [`lemma6`](lemma6.md) in `PositiveGap/Lemma6.lean`
- [`oneKronecker_mul_swap_apply`](../Lemma7/oneKronecker_mul_swap_apply.md) in `PositiveGap/Lemma7.lean`
- [`lemma7`](../Lemma7/lemma7.md) in `PositiveGap/Lemma7.lean`
- [`transpose_phiState_eq_swap`](../../EndMatter/Eq7/transpose_phiState_eq_swap.md) in `EndMatter/Eq7.lean`
- [`swapMatrix_mul_phase_apply`](../../EndMatter/Eq7/swapMatrix_mul_phase_apply.md) in `EndMatter/Eq7.lean`
- [`transpose_ad_phiState_eq_swap_mul_phase`](../../EndMatter/Eq7/transpose_ad_phiState_eq_swap_mul_phase.md) in `EndMatter/Eq7.lean`
- [`lambda_phiState_eq`](../../EndMatter/Eq7/lambda_phiState_eq.md) in `EndMatter/Eq7.lean`
- [`theorem_eq7_witness_bound_explicit`](../../EndMatter/Eq7/theorem_eq7_witness_bound_explicit.md) in `EndMatter/Eq7.lean`
- [`swapMatrix_mul_diagonal_apply`](../../EndMatter/Eq7/swapMatrix_mul_diagonal_apply.md) in `EndMatter/Eq7.lean`
- [`explicit_witness_eq_swap_diagonal`](../../EndMatter/Eq7/explicit_witness_eq_swap_diagonal.md) in `EndMatter/Eq7.lean`
- [`explicit_witness_traceNorm_eq_sum`](../../EndMatter/Eq7/explicit_witness_traceNorm_eq_sum.md) in `EndMatter/Eq7.lean`
- [`explicit_witness_traceNorm_eq`](../../EndMatter/Eq7/explicit_witness_traceNorm_eq.md) in `EndMatter/Eq7.lean`
- [`theorem_eq7`](../../EndMatter/Eq7/theorem_eq7.md) in `EndMatter/Eq7.lean`

## Backlinks

- [Back to `INDEX.md`](../../INDEX.md)
- [Back to the `PositiveGap/Lemma6.lean` section in the index](../../INDEX.md#diamond-positivegap-lemma6-lean)
- [Next declaration in this file](swapMatrix_mul_self.md)