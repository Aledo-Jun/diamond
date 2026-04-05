---
layout: default
---

# transpose_ad_phiState_eq_swap_mul_phase

## Source location

- Original Lean file: `Diamond/EndMatter/Eq7.lean`
- Declaration name: `transpose_ad_phiState_eq_swap_mul_phase`
- Declaration kind: `theorem`

## Why this declaration exists

Explicit formula for `((Θ ∘ Ad_U) ⊗ id) (Φ_d)`.

 In the file `EndMatter/Eq7.lean`, it contributes to the explicit witness construction used to prove the lower bound labelled Eq. (7). Later proofs call this result by name, so documenting it makes the larger argument readable as a mathematical chain rather than as opaque proof script.

## Original code

```lean
/-- Explicit formula for `((Θ ∘ Ad_U) ⊗ id) (Φ_d)`. -/
theorem transpose_ad_phiState_eq_swap_mul_phase (d : ℕ) [Fact (1 < d)] :
    tensorWithIdentity
        (Fin d)
        (Fin d)
        ((transposeMap (Fin d)).comp (adMap (Fin d) (Ud d)))
        (phiState d) =
      (d : ℂ)⁻¹ • (swapMatrix d * ((Ud d)ᵀ ⊗ₖ star (Ud d))) := by
  ext i j
  rcases i with ⟨a, b⟩
  rcases j with ⟨c, e⟩
  have hEntry :
      tensorWithIdentity
          (Fin d)
          (Fin d)
          ((transposeMap (Fin d)).comp (adMap (Fin d) (Ud d)))
          (phiState d)
          (a, b)
          (c, e) =
        if b = c ∧ a = e then
          (d : ℂ)⁻¹ * Ud d b b * star (Ud d e e)
        else 0 := by
      by_cases h : b = c ∧ a = e
      · rcases h with ⟨hbc, hae⟩
        simp [tensorWithIdentity, transposeMap, adMap, LinearMap.comp_apply, Matrix.mul_apply,
          phiState_apply, Ud, Matrix.diagonal_apply, hbc, hae, mul_comm, mul_left_comm,
          mul_assoc]
      · have hcases : ¬ c = b ∨ ¬ a = e := by
          by_cases hcb : c = b
          · right
            intro hae
            apply h
            exact ⟨hcb.symm, hae⟩
          · left
            exact hcb
        rcases hcases with hcb | hae
        · have hbc : ¬ b = c := by
            simpa [eq_comm] using hcb
          simp [tensorWithIdentity, transposeMap, adMap, LinearMap.comp_apply,
            Matrix.mul_apply, phiState_apply, Ud, Matrix.diagonal_apply, hcb, hbc]
        · have hea : ¬ e = a := by
            simpa [eq_comm] using hae
          simp [tensorWithIdentity, transposeMap, adMap, LinearMap.comp_apply,
            Matrix.mul_apply, phiState_apply, Ud, Matrix.diagonal_apply, hae]
  calc
    tensorWithIdentity
        (Fin d)
        (Fin d)
        ((transposeMap (Fin d)).comp (adMap (Fin d) (Ud d)))
        (phiState d)
        (a, b)
        (c, e)
      = if b = c ∧ a = e then
          (d : ℂ)⁻¹ * Ud d b b * star (Ud d e e)
        else 0 := hEntry
    _ = ((d : ℂ)⁻¹ • (swapMatrix d * ((Ud d)ᵀ ⊗ₖ star (Ud d)))) (a, b) (c, e) := by
      simp [swapMatrix_mul_phase_apply, and_comm, mul_assoc]
```

## How To Read This Declaration

This page now uses a concise reading guide instead of a line-by-line Lean walkthrough.
The best way to read the declaration is:

1. read the **Why this declaration exists** section for the mathematical role,
2. read the **Original code** block as the exact formal statement or construction,
3. treat the proof as a small number of conceptual moves rather than a commentary on each Lean line.

## Proof / Construction Shape

Most declarations in this repository follow the same pattern:

- **setup**: introduce the ambient spaces, matrices, channels, or witnesses,
- **reduction**: rewrite the goal into a standard matrix, trace, or diamond-norm form,
- **core step**: apply previously proved lemmas from the same module or an earlier one,
- **finish**: simplify the remaining algebra with `rw`, `simp`, `calc`, or `ext`.

## Lean Cues

- `let` names an intermediate mathematical object.
- `have` records a useful subclaim.
- `calc` is a displayed derivation written as a chain of equalities or inequalities.
- `rw` rewrites using an identity.
- `simp` performs controlled simplification.
- `ext` means the proof is reduced to entrywise or pointwise equality.

For the math-first reading path, start from `DESCRIPTIONS/INDEX.md` and use the module overviews and flagship theorem pages before coming back to individual declaration pages.
