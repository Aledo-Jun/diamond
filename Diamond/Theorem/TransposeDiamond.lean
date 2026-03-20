import Diamond.Setups
import Diamond.StandardFacts
import Diamond.Theorem.Lemma1
import Diamond.Theorem.Lemma2
import Diamond.Theorem.Lemma3

open scoped BigOperators
open scoped ComplexOrder
open scoped Kronecker
open scoped MatrixOrder
open scoped Matrix.Norms.Frobenius
open Matrix

namespace Diamond

universe u

noncomputable section

private theorem densityState_hsNorm_le_one
    {n : Type u} [Fintype n] [DecidableEq n]
    (ρ : DensityState n) : hsNormOp ρ.1 ≤ 1 := by
  rcases (Matrix.posSemidef_iff_eq_conjTranspose_mul_self).mp ρ.2.1 with ⟨B, hB⟩
  have hsum : ∑ i, ∑ j, ‖B i j‖ ^ (2 : ℝ) = 1 := by
    have htrace : Matrix.trace (Bᴴ * B) = 1 := by
      simpa [hB] using ρ.2.2
    have hre := congrArg Complex.re htrace
    have haux : Complex.re (Matrix.trace (Bᴴ * B)) = ∑ i, ∑ j, ‖B i j‖ ^ (2 : ℝ) := by
      calc
        Complex.re (Matrix.trace (Bᴴ * B)) = ∑ i, Complex.re ((Bᴴ * B) i i) := by
          simp [Matrix.trace]
        _ = ∑ i, ∑ j, ‖B j i‖ ^ (2 : ℝ) := by
          simp [Matrix.mul_apply, Matrix.conjTranspose_apply, RCLike.norm_sq_eq_def]
        _ = ∑ i, ∑ j, ‖B i j‖ ^ (2 : ℝ) := by
          rw [Finset.sum_comm]
    simpa [haux] using hre
  have hBnorm : hsNormOp B = 1 := by
    change ‖B‖ = 1
    rw [Matrix.frobenius_norm_def, hsum]
    norm_num
  have hBstar : hsNormOp Bᴴ = hsNormOp B := by
    change ‖Bᴴ‖ = ‖B‖
    simpa using Matrix.frobenius_norm_conjTranspose B
  calc
    hsNormOp ρ.1 = hsNormOp (Bᴴ * B) := by
      simpa [hB]
    _ ≤ hsNormOp Bᴴ * hsNormOp B := by
      change ‖Bᴴ * B‖ ≤ ‖Bᴴ‖ * ‖B‖
      exact Matrix.frobenius_norm_mul _ _
    _ = hsNormOp B * hsNormOp B := by
      rw [hBstar]
    _ = 1 := by
      rw [hBnorm]
      ring

private def omegaVecGen (d : Type u) [Fintype d] [DecidableEq d] : d × d → ℂ :=
  fun ij => if ij.1 = ij.2 then ((Real.sqrt (Fintype.card d : ℝ) : ℂ)⁻¹) else 0

private def phiStateGen (d : Type u) [Fintype d] [DecidableEq d] :
    Matrix (d × d) (d × d) ℂ :=
  Matrix.vecMulVec (omegaVecGen d) (star (omegaVecGen d))

private theorem inv_sqrt_mul_inv_sqrt_card
    (d : Type u) [Fintype d] [DecidableEq d] [Nonempty d] :
    ((Real.sqrt (Fintype.card d : ℝ) : ℂ)⁻¹) * ((Real.sqrt (Fintype.card d : ℝ) : ℂ)⁻¹) =
      ((Fintype.card d : ℂ)⁻¹) := by
  have hd_pos_nat : 0 < Fintype.card d := Fintype.card_pos_iff.mpr ‹Nonempty d›
  have hd_pos : (0 : ℝ) < Fintype.card d := by
    exact_mod_cast hd_pos_nat
  have hsqrt_neR : (Real.sqrt (Fintype.card d : ℝ)) ≠ 0 := (Real.sqrt_ne_zero').2 hd_pos
  have hsqrt_ne : ((Real.sqrt (Fintype.card d : ℝ) : ℂ)) ≠ 0 := by
    exact_mod_cast hsqrt_neR
  calc
    ((Real.sqrt (Fintype.card d : ℝ) : ℂ)⁻¹) * ((Real.sqrt (Fintype.card d : ℝ) : ℂ)⁻¹)
      = ((Real.sqrt (Fintype.card d : ℝ) : ℂ) ^ 2)⁻¹ := by
          field_simp [hsqrt_ne]
    _ = ((Fintype.card d : ℂ)⁻¹) := by
          congr 1
          exact_mod_cast Real.sq_sqrt (show 0 ≤ (Fintype.card d : ℝ) by positivity)

private theorem phiStateGen_trace
    (d : Type u) [Fintype d] [DecidableEq d] [Nonempty d] :
    Matrix.trace (phiStateGen d) = 1 := by
  rw [phiStateGen, Matrix.trace_vecMulVec, dotProduct, Fintype.sum_prod_type]
  simp [omegaVecGen, inv_sqrt_mul_inv_sqrt_card]

private theorem phiStateGen_isDensityState
    (d : Type u) [Fintype d] [DecidableEq d] [Nonempty d] :
    IsDensityState (phiStateGen d) := by
  refine ⟨?_, phiStateGen_trace d⟩
  simpa [phiStateGen] using Matrix.posSemidef_vecMulVec_self_star (omegaVecGen d)

private theorem phiStateGen_apply
    (d : Type u) [Fintype d] [DecidableEq d] [Nonempty d] (a b c e : d) :
    phiStateGen d (c, b) (a, e) =
      if c = b ∧ a = e then ((Fintype.card d : ℂ)⁻¹) else 0 := by
  rw [phiStateGen, Matrix.vecMulVec_apply]
  by_cases hcb : c = b
  · by_cases hae : a = e
    · simp only [omegaVecGen, hcb, hae, if_true, Pi.star_apply]
      simpa using inv_sqrt_mul_inv_sqrt_card d
    · simp [omegaVecGen, hcb, hae]
  · by_cases hae : a = e
    · simp [omegaVecGen, hcb, hae]
    · simp [omegaVecGen, hcb, hae]

private def swapMatrixGen
    (d : Type u) [Fintype d] [DecidableEq d] : Matrix (d × d) (d × d) ℂ :=
  fun i j => if i.1 = j.2 ∧ i.2 = j.1 then 1 else 0

private theorem swapMatrixGen_mul_self
    (d : Type u) [Fintype d] [DecidableEq d] :
    swapMatrixGen d * swapMatrixGen d = 1 := by
  ext i j
  rw [Matrix.mul_apply]
  rw [Finset.sum_eq_single (i.2, i.1)]
  · by_cases hij : i = j
    · subst hij
      simp [swapMatrixGen]
    · have hneq : ¬ (i.2 = j.2 ∧ i.1 = j.1) := by
        intro h
        apply hij
        cases i with
        | mk a b =>
          cases j with
          | mk c e =>
            simp only [Prod.mk.injEq] at h ⊢
            exact ⟨h.2, h.1⟩
      simp [swapMatrixGen, hneq, hij]
  · intro x _ hx
    have hzero : ¬ (i.1 = x.2 ∧ i.2 = x.1) := by
      intro h
      apply hx
      ext <;> simp [h.1, h.2]
    simp [swapMatrixGen, hzero]
  · intro hi
    simp at hi

private theorem swapMatrixGen_conjTranspose
    (d : Type u) [Fintype d] [DecidableEq d] :
    (swapMatrixGen d)ᴴ = swapMatrixGen d := by
  ext i j
  by_cases h : i.1 = j.2 ∧ i.2 = j.1
  · rcases h with ⟨h1, h2⟩
    have h' : j.1 = i.2 ∧ j.2 = i.1 := ⟨h2.symm, h1.symm⟩
    change star (if j.1 = i.2 ∧ j.2 = i.1 then (1 : ℂ) else 0) =
      if i.1 = j.2 ∧ i.2 = j.1 then (1 : ℂ) else 0
    simp only [if_pos h', if_pos (And.intro h1 h2), star_one]
  · have h' : ¬ (j.1 = i.2 ∧ j.2 = i.1) := by
      intro hji
      apply h
      exact ⟨hji.2.symm, hji.1.symm⟩
    change star (if j.1 = i.2 ∧ j.2 = i.1 then (1 : ℂ) else 0) =
      if i.1 = j.2 ∧ i.2 = j.1 then (1 : ℂ) else 0
    simp only [if_neg h', if_neg h, star_zero]

private theorem transpose_phiStateGen_eq_swap
    (d : Type u) [Fintype d] [DecidableEq d] [Nonempty d] :
    tensorWithIdentity d d (transposeMap d) (phiStateGen d) =
      ((Fintype.card d : ℂ)⁻¹) • swapMatrixGen d := by
  ext i j
  rcases i with ⟨a, b⟩
  rcases j with ⟨c, e⟩
  simp [tensorWithIdentity, transposeMap, swapMatrixGen, phiStateGen_apply, eq_comm, and_comm]

private theorem scalar_one_eq_diagonal
    {n : Type u} [DecidableEq n] (c : ℂ) :
    (c • (1 : Matrix n n ℂ)) = Matrix.diagonal (fun _ => c) := by
  ext i j
  by_cases h : i = j <;> simp [h]

/-- Exact diamond norm of transposition on the stabilized ancilla-`d` witness space. -/
theorem transpose_diamond_exact
    {d : Type u} [Fintype d] [DecidableEq d] [Nonempty d] :
    diamondOp (transposeMap d) = Real.sqrt (Fintype.card (d × d) : ℝ) := by
  have hsqrt : (Fintype.card d : ℝ) = Real.sqrt (Fintype.card (d × d) : ℝ) := by
    rw [sqrt_card_prod_self (d := d) (k := d)]
    have hcard_nonneg : (0 : ℝ) ≤ Fintype.card d := by positivity
    nlinarith [Real.sq_sqrt hcard_nonneg]
  have hup : diamondOp (transposeMap d) ≤ Real.sqrt (Fintype.card (d × d) : ℝ) := by
    refine diamond_le_of_pointwise_nonempty (d := d) (Φ := transposeMap d) _ ?_
    intro ρ
    have hrewrite : tensorWithIdentity d d (transposeMap d) ρ.1 = partialTransposeMap d d ρ.1 := by
      simpa [LinearMap.comp_apply] using
        congrArg (fun Ψ : Channel (d × d) => Ψ ρ.1)
          (tensorWithIdentity_comp_transpose (d := d) (k := d)
            (Φ := (LinearMap.id : Channel d)))
    have hlemma2 :
        traceNormOp (partialTransposeMap d d ρ.1) ≤
          Real.sqrt (Fintype.card (d × d) : ℝ) * hsNormOp (partialTransposeMap d d ρ.1) := by
      simpa using lemma2 (Y := partialTransposeMap d d ρ.1)
    have hlemma3 : hsNormOp (partialTransposeMap d d ρ.1) = hsNormOp ρ.1 := by
      simpa using lemma3 (d := d) (k := d) ρ.1
    have hρhs : hsNormOp ρ.1 ≤ 1 := densityState_hsNorm_le_one ρ
    rw [hrewrite]
    calc
      traceNormOp (partialTransposeMap d d ρ.1)
        ≤ Real.sqrt (Fintype.card (d × d) : ℝ) * hsNormOp (partialTransposeMap d d ρ.1) := hlemma2
      _ = Real.sqrt (Fintype.card (d × d) : ℝ) * hsNormOp ρ.1 := by rw [hlemma3]
      _ ≤ Real.sqrt (Fintype.card (d × d) : ℝ) * 1 := by
            exact mul_le_mul_of_nonneg_left hρhs (Real.sqrt_nonneg _)
      _ = Real.sqrt (Fintype.card (d × d) : ℝ) := by ring
  have hlow : Real.sqrt (Fintype.card (d × d) : ℝ) ≤ diamondOp (transposeMap d) := by
    let ρ : DensityState (d × d) := ⟨phiStateGen d, phiStateGen_isDensityState d⟩
    have hwit :
        traceNormOp (tensorWithIdentity d d (transposeMap d) ρ.1) ≤ diamondOp (transposeMap d) :=
      traceNorm_apply_le_diamond (d := d) (k := d) (Φ := transposeMap d) ρ
    have hswap :
        tensorWithIdentity d d (transposeMap d) ρ.1 = ((Fintype.card d : ℂ)⁻¹) • swapMatrixGen d := by
      simpa [ρ] using transpose_phiStateGen_eq_swap d
    have hU : swapMatrixGen d * (swapMatrixGen d)ᴴ = 1 := by
      rw [swapMatrixGen_conjTranspose, swapMatrixGen_mul_self]
    have hswapNorm :
        traceNormOp (((Fintype.card d : ℂ)⁻¹) • swapMatrixGen d) = (Fintype.card d : ℝ) := by
      calc
        traceNormOp (((Fintype.card d : ℂ)⁻¹) • swapMatrixGen d)
          = traceNormOp ((((Fintype.card d : ℂ)⁻¹) • (1 : Matrix (d × d) (d × d) ℂ)) *
              swapMatrixGen d) := by
                simpa [one_mul] using
                  (smul_mul_assoc ((Fintype.card d : ℂ)⁻¹)
                    (1 : Matrix (d × d) (d × d) ℂ) (swapMatrixGen d)).symm
        _ = traceNormOp (((Fintype.card d : ℂ)⁻¹) • (1 : Matrix (d × d) (d × d) ℂ)) := by
              exact traceNormOp_mul_right_isometry
                (X := ((Fintype.card d : ℂ)⁻¹) • (1 : Matrix (d × d) (d × d) ℂ))
                (U := swapMatrixGen d) hU
        _ = traceNormOp (Matrix.diagonal (fun _ : d × d => ((Fintype.card d : ℂ)⁻¹))) := by
              rw [scalar_one_eq_diagonal]
        _ = ∑ _ : d × d, ‖((Fintype.card d : ℂ)⁻¹)‖ := by
              rw [traceNormOp_diagonal]
        _ = (Fintype.card (d × d) : ℝ) * ((Fintype.card d : ℝ)⁻¹) := by
              simp
        _ = (Fintype.card d : ℝ) := by
              rw [Fintype.card_prod, Nat.cast_mul]
              field_simp [show (Fintype.card d : ℝ) ≠ 0 by positivity]
    rw [hswap] at hwit
    rw [hswapNorm] at hwit
    exact hsqrt ▸ hwit
  exact le_antisymm hup hlow

end
end Diamond
