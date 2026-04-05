---
layout: default
---

# explicit_witness_eq_swap_diagonal

## Source location

- Original Lean file: `Diamond/EndMatter/Eq7.lean`
- Declaration name: `explicit_witness_eq_swap_diagonal`
- Declaration kind: `theorem`

## Why this declaration exists

The explicit witness is a swap times a diagonal matrix.

 In the file `EndMatter/Eq7.lean`, it contributes to the explicit witness construction used to prove the lower bound labelled Eq. (7). Later proofs call this result by name, so documenting it makes the larger argument readable as a mathematical chain rather than as opaque proof script.

## Original code

```lean
/-- The explicit witness is a swap times a diagonal matrix. -/
theorem explicit_witness_eq_swap_diagonal (d : ℕ) [Fact (1 < d)] :
    ((d : ℂ)⁻¹ •
      (swapMatrix d - swapMatrix d * ((Ud d)ᵀ ⊗ₖ star (Ud d)))) =
    swapMatrix d * Matrix.diagonal (fun ab =>
      (d : ℂ)⁻¹ * (1 - Ud d ab.1 ab.1 * star (Ud d ab.2 ab.2))) := by
  ext i j
  rcases i with ⟨a, b⟩
  rcases j with ⟨c, e⟩
  by_cases h : b = c ∧ a = e
  · rcases h with ⟨hbc, hae⟩
    subst hbc
    subst hae
    have hswap : swapMatrix d (a, b) (b, a) = 1 := by
      simp [swapMatrix]
    have hphase :
        (swapMatrix d * ((Ud d)ᵀ ⊗ₖ star (Ud d))) (a, b) (b, a) =
          Ud d b b * star (Ud d a a) := by
      simpa using swapMatrix_mul_phase_apply d a b b a
    have hdiag :
        (swapMatrix d *
            Matrix.diagonal (fun ab : Fin d × Fin d =>
              (d : ℂ)⁻¹ * (1 - Ud d ab.1 ab.1 * star (Ud d ab.2 ab.2))))
            (a, b) (b, a) =
          (d : ℂ)⁻¹ * (1 - Ud d b b * star (Ud d a a)) := by
      simpa using
        swapMatrix_mul_diagonal_apply d
          (fun ab : Fin d × Fin d =>
            (d : ℂ)⁻¹ * (1 - Ud d ab.1 ab.1 * star (Ud d ab.2 ab.2)))
          a b b a
    rw [hdiag]
    simp [hswap, hphase, sub_eq_add_neg]
  · have hcases : ¬ b = c ∨ ¬ a = e := by
      by_cases hbc : b = c
      · right
        intro hae
        apply h
        exact ⟨hbc, hae⟩
      · left
        exact hbc
    rcases hcases with hbc | hae
    · have hcb : ¬ c = b := by
        simpa [eq_comm] using hbc
      have hswap : swapMatrix d (a, b) (c, e) = 0 := by
        simp [swapMatrix, hbc]
      have hphase :
          (swapMatrix d * ((Ud d)ᵀ ⊗ₖ star (Ud d))) (a, b) (c, e) = 0 := by
        simpa [hbc] using swapMatrix_mul_phase_apply d a b c e
      have hdiag :
          (swapMatrix d *
              Matrix.diagonal (fun ab : Fin d × Fin d =>
                (d : ℂ)⁻¹ * (1 - Ud d ab.1 ab.1 * star (Ud d ab.2 ab.2))))
              (a, b) (c, e) = 0 := by
        simpa [hbc] using
          swapMatrix_mul_diagonal_apply d
            (fun ab : Fin d × Fin d =>
              (d : ℂ)⁻¹ * (1 - Ud d ab.1 ab.1 * star (Ud d ab.2 ab.2)))
            a b c e
      rw [hdiag]
      simp [Matrix.sub_apply, hswap, hphase]
    · have hea : ¬ e = a := by
        simpa [eq_comm] using hae
      have hswap : swapMatrix d (a, b) (c, e) = 0 := by
        simp [swapMatrix, hae]
      have hphase :
          (swapMatrix d * ((Ud d)ᵀ ⊗ₖ star (Ud d))) (a, b) (c, e) = 0 := by
        simpa [hae] using swapMatrix_mul_phase_apply d a b c e
      have hdiag :
          (swapMatrix d *
              Matrix.diagonal (fun ab : Fin d × Fin d =>
                (d : ℂ)⁻¹ * (1 - Ud d ab.1 ab.1 * star (Ud d ab.2 ab.2))))
              (a, b) (c, e) = 0 := by
        simpa [hae] using
          swapMatrix_mul_diagonal_apply d
            (fun ab : Fin d × Fin d =>
              (d : ℂ)⁻¹ * (1 - Ud d ab.1 ab.1 * star (Ud d ab.2 ab.2)))
            a b c e
      rw [hdiag]
      simp [Matrix.sub_apply, hswap, hphase]
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
