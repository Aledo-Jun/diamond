# phiState

## Source location

- Original Lean file: `Diamond/EndMatter/Eq7.lean`
- Declaration name: `phiState`
- Declaration kind: `def`

## Why this declaration exists

This definition forms the rank-one projector $|\Omega_d
angle\langle\Omega_d|$ from the maximally entangled vector.

 In the file `EndMatter/Eq7.lean`, it contributes to the explicit witness construction used to prove the lower bound labelled Eq. (7). Later declarations use this name instead of repeatedly expanding the underlying matrix formula.

## Original code

```lean
/-- The corresponding rank-one density operator `|Ω_d⟩⟨Ω_d|`. -/
def phiState (d : ℕ) : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ :=
  Matrix.vecMulVec (omegaVec d) (star (omegaVec d))
```

## Block-by-block explanation

The explanation below follows the declaration block by block. Each block groups a coherent piece of the definition or proof, so the mathematical structure is easier to see than in a strictly line-oriented reading.

1. Code:
```lean
/-- The corresponding rank-one density operator `|Ω_d⟩⟨Ω_d|`. -/
```
This is a Lean docstring. It is a human-written comment that tells readers what the declaration is meant to express before the formal code begins.

2. Code:
```lean
def phiState (d : ℕ) : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ :=
```
This line starts the `phiState` declaration. Because it begins with `def`, Lean now knows what kind of named object is being introduced. The type information on this line explains what sort of mathematical object the declaration talks about.  `Matrix d d ℂ` means a square matrix with complex entries; the index type `d` tells Lean which rows and columns exist.

3. Code:
```lean
  Matrix.vecMulVec (omegaVec d) (star (omegaVec d))
```
This line is one local step in the declaration. It either refines the formula being defined or advances the proof by a small algebraic or logical move.

## Mathematical summary

In ordinary mathematical language, `phiState` is the project's formal Lean name for the object introduced in this declaration.

## Dependencies and downstream use

### Earlier declarations this depends on
- [`omegaVec`](omegaVec.md) from `EndMatter/Eq7.lean`

### Later declarations that use this one
- [`phiState_trace`](phiState_trace.md) in `EndMatter/Eq7.lean`
- [`phiState_isDensityState`](phiState_isDensityState.md) in `EndMatter/Eq7.lean`
- [`phiState_apply`](phiState_apply.md) in `EndMatter/Eq7.lean`
- [`transpose_phiState_eq_swap`](transpose_phiState_eq_swap.md) in `EndMatter/Eq7.lean`
- [`transpose_ad_phiState_eq_swap_mul_phase`](transpose_ad_phiState_eq_swap_mul_phase.md) in `EndMatter/Eq7.lean`
- [`lambda_phiState_eq`](lambda_phiState_eq.md) in `EndMatter/Eq7.lean`
- [`theorem_eq7_witness_bound`](theorem_eq7_witness_bound.md) in `EndMatter/Eq7.lean`

## Backlinks

- [Back to `INDEX.md`](../../INDEX.md)
- [Back to the `EndMatter/Eq7.lean` section in the index](../../INDEX.md#diamond-endmatter-eq7-lean)
- [Previous declaration in this file](omegaVec.md)
- [Next declaration in this file](inv_sqrt_mul_inv_sqrt.md)