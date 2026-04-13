---
layout: default
---

# diamond_le_of_pointwise_nonempty

## Source location

- Original Lean file: `Diamond/StandardFacts.lean`
- Declaration name: `diamond_le_of_pointwise_nonempty`
- Declaration kind: `theorem`

## Why this declaration exists

This theorem packages the exact supremum step used in `Theorem1.lean` and `Remark1.lean`.
It is the formal version of the paper’s final move: once the pointwise estimate is proved for every
ancilla-`d` density state, take the supremum and conclude the diamond-norm bound.

## Current code

```lean
theorem diamond_le_of_pointwise_nonempty
    {d : Type u} [Fintype d] [DecidableEq d] [Nonempty d]
    (Φ : Channel d) (b : ℝ)
    (hbound : ∀ ρ : DensityState (d × d),
      traceNormOp (tensorWithIdentity d d Φ ρ.1) ≤ b) :
    diamondOp Φ ≤ b := by
  unfold diamondOp diamondNormAt
  let i0 : d × d := (Classical.choice ‹Nonempty d›, Classical.choice ‹Nonempty d›)
  let ψ : d × d → ℂ := Pi.single i0 1
  let ρ0 : Matrix (d × d) (d × d) ℂ := Matrix.vecMulVec ψ (star ψ)
  have hρ0 : IsDensityState ρ0 := by
    refine ⟨?_, ?_⟩
    · simpa [ρ0, ψ] using Matrix.posSemidef_vecMulVec_self_star ψ
    · simp [ρ0, ψ, Matrix.trace_vecMulVec]
  apply csSup_le
  · exact ⟨traceNormOp (tensorWithIdentity d d Φ ρ0), ⟨⟨ρ0, hρ0⟩, rfl⟩⟩
  · intro r hr
    rcases hr with ⟨ρ, rfl⟩
    exact hbound ρ
```

## Mathematical summary

The proof is elementary:

1. Unfold `diamondOp` into the `sSup` defining `diamondNormAt`.
2. Build one explicit density state `ρ0`, so the witness set is nonempty.
3. Apply `csSup_le`: every element of the witness set is bounded by `b` by the hypothesis `hbound`.

The only place where `Nonempty d` matters is step 2, where it supplies a basis vector from which a
rank-one density state is built.

## Dependencies and downstream use

### Earlier declarations this depends on
- [`Channel`](../Setups/Channel/) from `Setups.lean`
- [`DensityState`](../Setups/DensityState/) from `Setups.lean`
- [`traceNormOp`](../Setups/traceNormOp/) from `Setups.lean`
- [`tensorWithIdentity`](../Setups/tensorWithIdentity/) from `Setups.lean`
- [`diamondNormAt`](../Setups/diamondNormAt/) from `Setups.lean`
- [`diamondOp`](../Setups/diamondOp/) from `Setups.lean`

### Later declarations that use this one
- [`theorem1`](../Theorem/Theorem1/theorem1/) in `Theorem/Theorem1.lean`
- [`remark1`](../Theorem/Remark1/remark1/) in `Theorem/Remark1.lean`

## Backlinks

- [Back to `INDEX.md`](../INDEX/)
- [Back to the `StandardFacts.lean` section in the index](../INDEX/#diamond-standardfacts-lean)
- [Previous declaration in this file](diamond_le_of_pointwise/)
- [Next declaration in this file](traceNorm_apply_le_diamond/)
