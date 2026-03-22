# Ud

## Source location

- Original Lean file: `Diamond/Setups.lean`
- Declaration name: `Ud`
- Declaration kind: `def`

## Why this declaration exists

This is the special diagonal phase unitary used in the end-matter lower-bound construction.

 In the file `Setups.lean`, it contributes to foundational objects and notational definitions for operators, channels, norms, and the maps studied in the paper. Later declarations use this name instead of repeatedly expanding the underlying matrix formula.

## Original code

```lean
/-- The phase unitary used in the lower-bound example. -/
def Ud (d : ℕ) [Fact (1 < d)] : Matrix (Fin d) (Fin d) ℂ :=
  Matrix.diagonal fun i =>
    Complex.exp ((2 * Real.pi * Complex.I * (i : ℂ)) / (d : ℂ))
```

## Block-by-block explanation

The explanation below follows the declaration block by block. Each block groups a coherent piece of the definition or proof, so the mathematical structure is easier to see than in a strictly line-oriented reading.

1. Code:
```lean
/-- The phase unitary used in the lower-bound example. -/
```
This is a Lean docstring. It is a human-written comment that tells readers what the declaration is meant to express before the formal code begins.

2. Code:
```lean
def Ud (d : ℕ) [Fact (1 < d)] : Matrix (Fin d) (Fin d) ℂ :=
```
This line starts the `Ud` declaration. Because it begins with `def`, Lean now knows what kind of named object is being introduced. The type information on this line explains what sort of mathematical object the declaration talks about.  `Matrix d d ℂ` means a square matrix with complex entries; the index type `d` tells Lean which rows and columns exist.

3. Code:
```lean
  Matrix.diagonal fun i =>
```
This line is one local step in the declaration. It either refines the formula being defined or advances the proof by a small algebraic or logical move.

4. Code:
```lean
    Complex.exp ((2 * Real.pi * Complex.I * (i : ℂ)) / (d : ℂ))
```
This line is one local step in the declaration. It either refines the formula being defined or advances the proof by a small algebraic or logical move.

## Mathematical summary

In ordinary mathematical language, `Ud` is the project's formal Lean name for the object introduced in this declaration.

## Dependencies and downstream use

### Earlier declarations this depends on
- This declaration does not explicitly cite an earlier named declaration from the documented tree; it mostly uses Lean primitives or local algebraic steps.

### Later declarations that use this one
- [`Lambda`](Lambda.md) in `Setups.lean`
- [`trace_Ud_eq_zero`](../StandardFacts/trace_Ud_eq_zero.md) in `StandardFacts.lean`
- [`swapMatrix_mul_phase_apply`](../EndMatter/Eq7/swapMatrix_mul_phase_apply.md) in `EndMatter/Eq7.lean`
- [`transpose_ad_phiState_eq_swap_mul_phase`](../EndMatter/Eq7/transpose_ad_phiState_eq_swap_mul_phase.md) in `EndMatter/Eq7.lean`
- [`lambda_phiState_eq`](../EndMatter/Eq7/lambda_phiState_eq.md) in `EndMatter/Eq7.lean`
- [`theorem_eq7_witness_bound_explicit`](../EndMatter/Eq7/theorem_eq7_witness_bound_explicit.md) in `EndMatter/Eq7.lean`
- [`ud_add_eq_mul`](../EndMatter/Eq7/ud_add_eq_mul.md) in `EndMatter/Eq7.lean`
- [`ud_mul_star_self`](../EndMatter/Eq7/ud_mul_star_self.md) in `EndMatter/Eq7.lean`
- [`ud_conjTranspose_mul_self`](../EndMatter/Eq7/ud_conjTranspose_mul_self.md) in `EndMatter/Eq7.lean`
- [`ud_add_mul_star_eq`](../EndMatter/Eq7/ud_add_mul_star_eq.md) in `EndMatter/Eq7.lean`
- [`explicit_witness_eq_swap_diagonal`](../EndMatter/Eq7/explicit_witness_eq_swap_diagonal.md) in `EndMatter/Eq7.lean`
- [`explicit_witness_traceNorm_eq_sum`](../EndMatter/Eq7/explicit_witness_traceNorm_eq_sum.md) in `EndMatter/Eq7.lean`
- [`norm_one_sub_ud_eq_sin`](../EndMatter/Eq7/norm_one_sub_ud_eq_sin.md) in `EndMatter/Eq7.lean`
- [`norm_one_sub_ud_sum_eq_cot`](../EndMatter/Eq7/norm_one_sub_ud_sum_eq_cot.md) in `EndMatter/Eq7.lean`
- [`explicit_witness_traceNorm_eq`](../EndMatter/Eq7/explicit_witness_traceNorm_eq.md) in `EndMatter/Eq7.lean`
- [`theorem_eq7`](../EndMatter/Eq7/theorem_eq7.md) in `EndMatter/Eq7.lean`
- [`theorem_eq8`](../EndMatter/Eq8/theorem_eq8.md) in `EndMatter/Eq8.lean`
- [`alpha_lower_bound`](../EndMatter/Eq8/alpha_lower_bound.md) in `EndMatter/Eq8.lean`

## Backlinks

- [Back to `INDEX.md`](../INDEX.md)
- [Back to the `Setups.lean` section in the index](../INDEX.md#diamond-setups-lean)
- [Previous declaration in this file](adMap.md)
- [Next declaration in this file](Lambda.md)