# explicit_witness_traceNorm_eq_sum

## Source location

- Original Lean file: `Diamond/EndMatter/Eq7.lean`
- Declaration name: `explicit_witness_traceNorm_eq_sum`
- Declaration kind: `theorem`

## Why this declaration exists

The witness trace norm collapses to the one-dimensional phase sum.

 In the file `EndMatter/Eq7.lean`, it contributes to the explicit witness construction used to prove the lower bound labelled Eq. (7). Later proofs call this result by name, so documenting it makes the larger argument readable as a mathematical chain rather than as opaque proof script.

## Original code

```lean
/-- The witness trace norm collapses to the one-dimensional phase sum. -/
theorem explicit_witness_traceNorm_eq_sum (d : ℕ) [Fact (1 < d)] :
    traceNormOp
      ((d : ℂ)⁻¹ •
        (swapMatrix d - swapMatrix d * ((Ud d)ᵀ ⊗ₖ star (Ud d)))) =
      ∑ k : Fin d, ‖1 - Ud d k k‖ := by
  let f : Fin d × Fin d → ℂ := fun ab =>
    (d : ℂ)⁻¹ * (1 - Ud d ab.1 ab.1 * star (Ud d ab.2 ab.2))
  rw [explicit_witness_eq_swap_diagonal]
  rw [traceNormOp_mul_left_isometry (U := swapMatrix d) (X := Matrix.diagonal f)
    (hU := swapMatrix_conjTranspose_mul_self d)]
  rw [traceNormOp_diagonal]
  have hd_pos : 0 < d := lt_trans Nat.zero_lt_one ‹Fact (1 < d)›.out
  have hd_neR : (d : ℝ) ≠ 0 := by
    exact_mod_cast hd_pos.ne'
  have hscalar : ‖((d : ℂ)⁻¹)‖ = (d : ℝ)⁻¹ := by
    rw [norm_inv, Complex.norm_natCast]
  calc
    ∑ i, ‖f i‖
      = ∑ i : Fin d × Fin d, ‖((d : ℂ)⁻¹) * (1 - Ud d i.1 i.1 * star (Ud d i.2 i.2))‖ := by
          rfl
    _ = ∑ i : Fin d × Fin d, ‖((d : ℂ)⁻¹)‖ * ‖1 - Ud d i.1 i.1 * star (Ud d i.2 i.2)‖ := by
          refine Finset.sum_congr rfl ?_
          intro i hi
          rw [norm_mul]
    _ = ‖((d : ℂ)⁻¹)‖ * ∑ i : Fin d × Fin d, ‖1 - Ud d i.1 i.1 * star (Ud d i.2 i.2)‖ := by
          rw [← Finset.mul_sum]
    _ = (d : ℝ)⁻¹ * ∑ i : Fin d × Fin d, ‖1 - Ud d i.1 i.1 * star (Ud d i.2 i.2)‖ := by
          rw [hscalar]
    _ = (d : ℝ)⁻¹ * ((d : ℝ) * ∑ k : Fin d, ‖1 - Ud d k k‖) := by
          congr 1
          calc
            ∑ i : Fin d × Fin d, ‖1 - Ud d i.1 i.1 * star (Ud d i.2 i.2)‖
              = ∑ a : Fin d, ∑ b : Fin d, ‖1 - Ud d a a * star (Ud d b b)‖ := by
                  simp [Fintype.sum_prod_type]
            _ = ∑ b : Fin d, ∑ a : Fin d, ‖1 - Ud d a a * star (Ud d b b)‖ := by
                  simpa using
                    (Finset.sum_comm
                      (s := (Finset.univ : Finset (Fin d)))
                      (t := (Finset.univ : Finset (Fin d)))
                      (f := fun a b => ‖1 - Ud d a a * star (Ud d b b)‖))
            _ = ∑ b : Fin d, ∑ a : Fin d, ‖1 - Ud d a a‖ := by
                  refine Finset.sum_congr rfl ?_
                  intro b hb
                  have hinner :
                      ∑ k : Fin d, ‖1 - Ud d k k * star (Ud d b b)‖ =
                        ∑ a : Fin d, ‖1 - Ud d a a‖ := by
                    exact (Fintype.sum_bijective (fun a => a + b)
                      (AddGroup.addRight_bijective b)
                      (fun a => ‖1 - Ud d a a‖)
                      (fun k => ‖1 - Ud d k k * star (Ud d b b)‖)
                      (fun a => by
                        change ‖1 - Ud d a a‖ =
                          ‖1 - Ud d (a + b) (a + b) * star (Ud d b b)‖
                        rw [ud_add_mul_star_eq])).symm
                  exact hinner
            _ = (d : ℝ) * ∑ a : Fin d, ‖1 - Ud d a a‖ := by
                  rw [Fin.sum_const, nsmul_eq_mul]
    _ = ∑ k : Fin d, ‖1 - Ud d k k‖ := by
          rw [← mul_assoc, inv_mul_cancel₀ hd_neR, one_mul]
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
