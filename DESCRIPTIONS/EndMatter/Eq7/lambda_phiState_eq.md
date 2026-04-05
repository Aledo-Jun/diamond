# lambda_phiState_eq

## Source location

- Original Lean file: `Diamond/EndMatter/Eq7.lean`
- Declaration name: `lambda_phiState_eq`
- Declaration kind: `theorem`

## Why this declaration exists

Explicit formula for `((Λ_d ⊗ id) (Φ_d))` in matrix form.

 In the file `EndMatter/Eq7.lean`, it contributes to the explicit witness construction used to prove the lower bound labelled Eq. (7). Later proofs call this result by name, so documenting it makes the larger argument readable as a mathematical chain rather than as opaque proof script.

## Original code

```lean
/-- Explicit formula for `((Λ_d ⊗ id) (Φ_d))` in matrix form. -/
theorem lambda_phiState_eq (d : ℕ) [Fact (1 < d)] :
    tensorWithIdentity (Fin d) (Fin d) (Lambda d) (phiState d) =
      (d : ℂ)⁻¹ •
        (swapMatrix d - swapMatrix d * ((Ud d)ᵀ ⊗ₖ star (Ud d))) := by
  calc
    tensorWithIdentity (Fin d) (Fin d) (Lambda d) (phiState d)
      =
        tensorWithIdentity (Fin d) (Fin d) (transposeMap (Fin d)) (phiState d) -
          tensorWithIdentity
            (Fin d)
            (Fin d)
            ((transposeMap (Fin d)).comp (adMap (Fin d) (Ud d)))
            (phiState d) := by
              ext i j
              simp [Lambda, idMinus, tensorWithIdentity, transposeMap, adMap,
                LinearMap.comp_apply]
    _ =
        (d : ℂ)⁻¹ • swapMatrix d -
          (d : ℂ)⁻¹ • (swapMatrix d * ((Ud d)ᵀ ⊗ₖ star (Ud d))) := by
            rw [transpose_phiState_eq_swap, transpose_ad_phiState_eq_swap_mul_phase]
    _ =
        (d : ℂ)⁻¹ •
          (swapMatrix d - swapMatrix d * ((Ud d)ᵀ ⊗ₖ star (Ud d))) := by
            simp [smul_sub]
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
