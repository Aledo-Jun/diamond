import Diamond.Setups
import Diamond.Theorem.Lemma1
import Diamond.Theorem.Lemma2
import Diamond.Theorem.Lemma3
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Sinc
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.InnerProductSpace.JointEigenspace
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.LinearAlgebra.UnitaryGroup

open scoped BigOperators
open scoped ComplexOrder
open scoped Kronecker
open scoped MatrixOrder
open scoped Matrix.Norms.Frobenius
open scoped Topology
open Filter
open Matrix
open Module.End

namespace Diamond

universe u

noncomputable section

theorem trNorm_nonneg
    {d : Type u} [Fintype d] [DecidableEq d] (X : Matrix d d ℂ) :
    0 ≤ traceNormOp X := by
  unfold traceNormOp
  exact Finset.sum_nonneg (fun i hi => Real.sqrt_nonneg _)

theorem hsNorm_nonneg
    {m n : Type u} [Fintype m] [DecidableEq m] [Fintype n] [DecidableEq n]
    (X : Matrix m n ℂ) : 0 ≤ hsNormOp X := by
  unfold hsNormOp hsNorm
  exact norm_nonneg X

theorem hsNormOp_eq_zero_iff
    {m n : Type u} [Fintype m] [DecidableEq m] [Fintype n] [DecidableEq n]
    {X : Matrix m n ℂ} : hsNormOp X = 0 ↔ X = 0 := by
  unfold hsNormOp hsNorm
  simp

/-- Background Kraus representation for finite-dimensional quantum channels. -/
theorem quantumChannel_has_kraus
    {d : Type u} [Fintype d] [DecidableEq d] {T : Channel d} :
    IsQuantumChannel T →
    ∃ (r : ℕ), ∃ (E : Fin r → Matrix d d ℂ),
      (∀ X, T X = ∑ i, E i * X * (E i)ᴴ) ∧
      (∑ i, (E i)ᴴ * E i = 1) := by
  intro hT
  exact hT.kraus

/-- `tensorWithIdentity` commutes with transposition on the left tensor factor. -/
theorem tensorWithIdentity_comp_transpose
    {d k : Type u} [Fintype d] [DecidableEq d] [Fintype k] [DecidableEq k]
    (Φ : Channel d) :
    tensorWithIdentity d k ((transposeMap d).comp Φ)
      = (partialTransposeMap d k).comp (tensorWithIdentity d k Φ) := by
  ext X i j
  simp [tensorWithIdentity, partialTransposeMap, LinearMap.comp_apply, transposeMap]

/-- `idMinus` preserves Hermiticity for CPTP channels. -/
theorem idMinus_isHermiticityPreserving
    {d : Type u} [Fintype d] [DecidableEq d] (T : Channel d) (hT : IsQuantumChannel T) :
    IsHermiticityPreserving (idMinus T) := by
  intro X
  calc
    idMinus T Xᴴ = Xᴴ - T Xᴴ := by simp [idMinus]
    _ = Xᴴ - (T X)ᴴ := by rw [hT.hermiticity_preserving X]
    _ = (X - T X)ᴴ := by simp [Matrix.conjTranspose_sub]

/-- `idMinus` is trace-annihilating for CPTP channels. -/
theorem idMinus_isTraceAnnihilating
    {d : Type u} [Fintype d] [DecidableEq d] (T : Channel d) (hT : IsQuantumChannel T) :
    IsTraceAnnihilating (idMinus T) := by
  intro X
  simp [idMinus, hT.trace_preserving]

/-- Unitary conjugation is a quantum channel. -/
theorem adMap_isQuantumChannel
    {d : Type u} [Fintype d] [DecidableEq d]
    (U : Matrix d d ℂ) (hU : Uᴴ * U = 1) :
    IsQuantumChannel (adMap d U) := by
  refine ⟨?_, ?_, ?_⟩
  · intro X
    calc
      Matrix.trace (adMap d U X) = Matrix.trace (U * X * Uᴴ) := by rfl
      _ = Matrix.trace ((Uᴴ * U) * X) := by
            simpa [Matrix.mul_assoc] using Matrix.trace_mul_cycle U X Uᴴ
      _ = Matrix.trace X := by simp [hU]
  · intro X
    simp [adMap, Matrix.conjTranspose_mul, Matrix.mul_assoc]
  · refine ⟨1, fun _ => U, ?_, ?_⟩
    · intro X
      simp [adMap]
    · simpa using hU

/-- Abstract pointwise-to-diamond reduction.

    This lemma states the standard `k = d` reduction used throughout the file. -/
-- Background functional-analytic fact (finite-dimensional attainment/compactness input).
theorem diamond_le_of_pointwise
    {d : Type u} [Fintype d] [DecidableEq d]
    [Nonempty d]
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

/-- Pointwise-to-diamond reduction in the nonempty case. -/
theorem diamond_le_of_pointwise_nonempty
    {d : Type u} [Fintype d] [DecidableEq d] [Nonempty d]
    (Φ : Channel d) (b : ℝ)
    (hbound : ∀ ρ : DensityState (d × d),
      traceNormOp (tensorWithIdentity d d Φ ρ.1) ≤ b) :
    diamondOp Φ ≤ b := by
  exact diamond_le_of_pointwise (d := d) Φ b hbound

/-- Concrete witness bound for the diamond norm defined in `Setups`. -/
-- Immediate from the definition of `diamondNormAt`; kept as an explicit axiom in this split
-- to avoid introducing an auxiliary compactness/attainment argument at this layer.
axiom traceNorm_apply_le_diamond
    {d : Type u} [Fintype d] [DecidableEq d] {k : Type u}
    [Fintype k] [DecidableEq k]
    (Φ : Channel d) (ρ : DensityState (d × k)) :
    traceNormOp (tensorWithIdentity d k Φ ρ.1) ≤ diamondNormAt (d := d) (k := k) Φ

/-- Tensoring unitary conjugation with the identity is conjugation by the Kronecker unitary. -/
private theorem tensorWithIdentity_adMap_eq_kronecker
    {d k : Type u} [Fintype d] [DecidableEq d] [Fintype k] [DecidableEq k]
    (U : Matrix d d ℂ) (X : Matrix (d × k) (d × k) ℂ) :
    tensorWithIdentity d k (adMap d U) X =
      (U ⊗ₖ (1 : Matrix k k ℂ)) * X * (U ⊗ₖ (1 : Matrix k k ℂ))ᴴ := by
  ext i j
  rcases i with ⟨a, b⟩
  rcases j with ⟨c, e⟩
  calc
    tensorWithIdentity d k (adMap d U) X (a, b) (c, e)
      = ∑ x : d, ∑ y : d, U a x * X (x, b) (y, e) * star (U c y) := by
          calc
            tensorWithIdentity d k (adMap d U) X (a, b) (c, e)
                = ∑ x, U a x * (∑ y, X (x, b) (y, e) * star (U c y)) := by
                    simp [tensorWithIdentity, adMap, Matrix.mul_apply, Matrix.conjTranspose_apply,
                      mul_assoc]
            _ = ∑ x : d, ∑ y : d, U a x * X (x, b) (y, e) * star (U c y) := by
                  simp_rw [Finset.mul_sum, mul_assoc]
    _ = (((U ⊗ₖ (1 : Matrix k k ℂ)) * X) * (U ⊗ₖ (1 : Matrix k k ℂ))ᴴ) (a, b) (c, e) := by
          have hleft :
              ∀ y : d, ((U ⊗ₖ (1 : Matrix k k ℂ)) * X) (a, b) (y, e) =
                ∑ x : d, U a x * X (x, b) (y, e) := by
            intro y
            rw [Matrix.mul_apply, Fintype.sum_prod_type]
            refine Finset.sum_congr rfl ?_
            intro x hx
            rw [Finset.sum_eq_single b]
            · simp [Matrix.kroneckerMap_apply, Matrix.one_apply, mul_assoc]
            · intro z hz hzb
              have hbz' : b ≠ z := by
                exact fun h => hzb h.symm
              have hbz : (1 : Matrix k k ℂ) b z = 0 := by
                simp [Matrix.one_apply, hbz']
              simp [Matrix.kroneckerMap_apply, hbz]
            · simp
          have hright :
              (((U ⊗ₖ (1 : Matrix k k ℂ)) * X) * (U ⊗ₖ (1 : Matrix k k ℂ))ᴴ) (a, b) (c, e) =
                ∑ y : d, ((U ⊗ₖ (1 : Matrix k k ℂ)) * X) (a, b) (y, e) * star (U c y) := by
            rw [Matrix.mul_apply, Fintype.sum_prod_type]
            refine Finset.sum_congr rfl ?_
            intro y hy
            rw [Finset.sum_eq_single e]
            · simp [Matrix.kroneckerMap_apply, Matrix.conjTranspose_apply, Matrix.one_apply,
                mul_assoc]
            · intro z hz hze
              have hez' : e ≠ z := by
                exact fun h => hze h.symm
              have hez : (1 : Matrix k k ℂ) e z = 0 := by
                simp [Matrix.one_apply, hez']
              simp [Matrix.kroneckerMap_apply, Matrix.conjTranspose_apply, hez]
            · simp
          rw [hright]
          rw [Finset.sum_comm]
          refine Finset.sum_congr rfl ?_
          intro y hy
          rw [← Finset.sum_mul, hleft]

private def omegaVecGen
    (d : Type u) [Fintype d] [DecidableEq d] [Nonempty d] : d × d → ℂ :=
  fun ij => if ij.1 = ij.2 then ((Real.sqrt (Fintype.card d : ℝ) : ℂ)⁻¹) else 0

private def phiStateGen
    (d : Type u) [Fintype d] [DecidableEq d] [Nonempty d] :
    Matrix (d × d) (d × d) ℂ :=
  Matrix.vecMulVec (omegaVecGen d) (star (omegaVecGen d))

private def unitaryVecGen
    (d : Type u) [Fintype d] [DecidableEq d] [Nonempty d]
    (U : Matrix d d ℂ) : d × d → ℂ :=
  fun ij => ((Real.sqrt (Fintype.card d : ℝ) : ℂ)⁻¹) * U ij.1 ij.2

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

private theorem omegaVecGen_dot_self
    (d : Type u) [Fintype d] [DecidableEq d] [Nonempty d] :
    omegaVecGen d ⬝ᵥ star (omegaVecGen d) = 1 := by
  rw [dotProduct, Fintype.sum_prod_type]
  calc
    ∑ i : d, ∑ j : d, omegaVecGen d (i, j) * star (omegaVecGen d (i, j))
      = ((Real.sqrt (Fintype.card d : ℝ) : ℂ)⁻¹) * ((Real.sqrt (Fintype.card d : ℝ) : ℂ)⁻¹) *
          (Fintype.card d : ℂ) := by
            simp [omegaVecGen, mul_assoc, mul_left_comm, mul_comm]
    _ = 1 := by
          rw [inv_sqrt_mul_inv_sqrt_card (d := d)]
          field_simp [show (Fintype.card d : ℂ) ≠ 0 by positivity]

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

private theorem phiStateGen_trace
    (d : Type u) [Fintype d] [DecidableEq d] [Nonempty d] :
    Matrix.trace (phiStateGen d) = 1 := by
  rw [phiStateGen, Matrix.trace_vecMulVec]
  exact omegaVecGen_dot_self d

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

/-- Transposition norm identity `‖Θ‖⋄ = √(d²) = d`. -/
theorem lemma_transpose_diamond
    {d : Type u} [Fintype d] [DecidableEq d] [Nonempty d] :
    diamondOp (transposeMap d) = Real.sqrt (Fintype.card (d × d) : ℝ) := by
  have hsqrt : (Fintype.card d : ℝ) = Real.sqrt (Fintype.card (d × d) : ℝ) := by
    rw [Fintype.card_prod, Nat.cast_mul]
    rw [Real.sqrt_mul (show (0 : ℝ) ≤ Fintype.card d by positivity)]
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

private theorem unitaryVecGen_dot_self
    {d : Type u} [Fintype d] [DecidableEq d] [Nonempty d]
    (U : Matrix d d ℂ) (hU : Uᴴ * U = 1) :
    unitaryVecGen d U ⬝ᵥ star (unitaryVecGen d U) = 1 := by
  let c : ℂ := ((Real.sqrt (Fintype.card d : ℝ) : ℂ)⁻¹)
  rw [dotProduct, Fintype.sum_prod_type]
  calc
    ∑ i : d, ∑ j : d, unitaryVecGen d U (i, j) * star (unitaryVecGen d U (i, j))
      = ∑ i : d, (∑ j : d, U i j * star (U i j)) * (c * c) := by
          refine Finset.sum_congr rfl ?_
          intro i hi
          simpa [unitaryVecGen, c, mul_assoc, mul_left_comm, mul_comm] using
            (Finset.sum_mul (s := Finset.univ)
              (f := fun j : d => U i j * star (U i j)) (a := c * c)).symm
    _ = (∑ i : d, ∑ j : d, U i j * star (U i j)) * (c * c) := by
          simpa using
            (Finset.sum_mul (s := Finset.univ)
              (f := fun i : d => ∑ j : d, U i j * star (U i j))
              (a := c * c)).symm
    _ = c * (c * ∑ i : d, ∑ j : d, U i j * star (U i j)) := by
          ring
    _ = c * (c * ∑ i : d, (Uᴴ * U).diag i) := by
          congr 1
          congr 1
          rw [Finset.sum_comm]
          simp [Matrix.diag, Matrix.mul_apply, Matrix.conjTranspose_apply, mul_assoc,
            mul_left_comm, mul_comm]
    _ = c * (c * Matrix.trace (Uᴴ * U)) := by
          simp [Matrix.trace]
    _ = 1 := by
          dsimp [c]
          rw [hU, ← mul_assoc, inv_sqrt_mul_inv_sqrt_card (d := d)]
          simp [Matrix.trace]

private theorem omegaVecGen_orthogonal_unitaryVecGen
    {d : Type u} [Fintype d] [DecidableEq d] [Nonempty d]
    (U : Matrix d d ℂ) (htrace : Matrix.trace U = 0) :
    star (omegaVecGen d) ⬝ᵥ unitaryVecGen d U = 0 := by
  let c : ℂ := ((Real.sqrt (Fintype.card d : ℝ) : ℂ)⁻¹)
  rw [dotProduct, Fintype.sum_prod_type]
  calc
    ∑ i : d, ∑ j : d, star (omegaVecGen d (i, j)) * unitaryVecGen d U (i, j)
      = ∑ i : d, U i i * (c * c) := by
          refine Finset.sum_congr rfl ?_
          intro i hi
          rw [Finset.sum_eq_single i]
          · simp [omegaVecGen, unitaryVecGen, c, mul_assoc, mul_left_comm, mul_comm]
          · intro j hj hji
            have hij : i ≠ j := by
              exact fun h => hji h.symm
            simp [omegaVecGen, hij, unitaryVecGen]
          · simp
    _ = (∑ i : d, U i i) * (c * c) := by
          simpa using
            (Finset.sum_mul (s := Finset.univ) (f := fun i : d => U i i) (a := c * c)).symm
    _ = c * (c * ∑ i : d, U i i) := by
          ring
    _ = ((Fintype.card d : ℂ)⁻¹) * Matrix.trace U := by
          dsimp [c]
          rw [← mul_assoc, inv_sqrt_mul_inv_sqrt_card (d := d)]
          simp [Matrix.trace]
    _ = 0 := by simp [htrace]

private theorem kronecker_mulVec_omegaVecGen
    {d : Type u} [Fintype d] [DecidableEq d] [Nonempty d]
    (U : Matrix d d ℂ) :
    (U ⊗ₖ (1 : Matrix d d ℂ)) *ᵥ omegaVecGen d = unitaryVecGen d U := by
  ext ij
  rcases ij with ⟨a, b⟩
  rw [Matrix.mulVec, dotProduct, Fintype.sum_prod_type]
  change ∑ x : d, ∑ y : d,
      (U a x * (1 : Matrix d d ℂ) b y) * omegaVecGen d (x, y) = unitaryVecGen d U (a, b)
  calc
    ∑ x : d, ∑ y : d, (U a x * (1 : Matrix d d ℂ) b y) * omegaVecGen d (x, y)
      = ∑ x : d, U a x * omegaVecGen d (x, b) := by
          refine Finset.sum_congr rfl ?_
          intro x hx
          rw [Finset.sum_eq_single b]
          · simp [mul_assoc]
          · intro y hy hyb
            have hby' : b ≠ y := by
              exact fun h => hyb h.symm
            have hby : (1 : Matrix d d ℂ) b y = 0 := by
              simp [Matrix.one_apply, hby']
            simp [hby, omegaVecGen]
          · simp
    _ = unitaryVecGen d U (a, b) := by
          simpa [omegaVecGen, unitaryVecGen, mul_assoc, mul_comm]

private theorem omegaVecGen_vecMul_kronecker_conjTranspose
    {d : Type u} [Fintype d] [DecidableEq d] [Nonempty d]
    (U : Matrix d d ℂ) :
    star (omegaVecGen d) ᵥ* (U ⊗ₖ (1 : Matrix d d ℂ))ᴴ = star (unitaryVecGen d U) := by
  ext ij
  rcases ij with ⟨a, b⟩
  rw [Matrix.vecMul, dotProduct, Fintype.sum_prod_type]
  change ∑ x : d, ∑ y : d,
      star (omegaVecGen d (x, y)) * ((U ⊗ₖ (1 : Matrix d d ℂ))ᴴ) (x, y) (a, b) =
        star (unitaryVecGen d U (a, b))
  calc
    ∑ x : d, ∑ y : d,
        star (omegaVecGen d (x, y)) * ((U ⊗ₖ (1 : Matrix d d ℂ))ᴴ) (x, y) (a, b)
      = ∑ x : d, star (omegaVecGen d (x, b)) * star (U a x) := by
          refine Finset.sum_congr rfl ?_
          intro x hx
          rw [Finset.sum_eq_single b]
          · simp [Matrix.kroneckerMap_apply, Matrix.one_apply, Matrix.conjTranspose_apply,
              mul_assoc]
          · intro y hy hyb
            have hby' : b ≠ y := by
              exact fun h => hyb h.symm
            simp [Matrix.kroneckerMap_apply, Matrix.conjTranspose_apply, Matrix.one_apply, hyb,
              hby']
          · simp
    _ = star (unitaryVecGen d U (a, b)) := by
          rw [Finset.sum_eq_single b]
          · simp [omegaVecGen, unitaryVecGen, mul_assoc, mul_comm]
          · intro x hx hxb
            simp [omegaVecGen, hxb]
          · simp

private theorem vecMulVec_isDensityState_of_dotProduct_one
    {ι : Type u} [Fintype ι] [DecidableEq ι] (ψ : ι → ℂ)
    (hψ : ψ ⬝ᵥ star ψ = 1) :
    IsDensityState (Matrix.vecMulVec ψ (star ψ)) := by
  refine ⟨?_, ?_⟩
  · simpa using Matrix.posSemidef_vecMulVec_self_star ψ
  · simpa [hψ] using Matrix.trace_vecMulVec ψ (star ψ)

private theorem tensorWithIdentity_adMap_phiStateGen
    {d : Type u} [Fintype d] [DecidableEq d] [Nonempty d]
    (U : Matrix d d ℂ) :
    tensorWithIdentity d d (adMap d U) (phiStateGen d) =
      Matrix.vecMulVec (unitaryVecGen d U) (star (unitaryVecGen d U)) := by
  rw [tensorWithIdentity_adMap_eq_kronecker, phiStateGen]
  rw [Matrix.mul_vecMulVec, Matrix.vecMulVec_mul]
  simp [kronecker_mulVec_omegaVecGen, omegaVecGen_vecMul_kronecker_conjTranspose]

private theorem traceNorm_vecMulVec_sub_vecMulVec_of_orthogonal
    {ι : Type u} [Fintype ι] [DecidableEq ι]
    (ψ φ : ι → ℂ)
    (hψ : ψ ⬝ᵥ star ψ = 1) (hφ : φ ⬝ᵥ star φ = 1)
    (horth : star ψ ⬝ᵥ φ = 0) :
    traceNormOp (Matrix.vecMulVec ψ (star ψ) - Matrix.vecMulVec φ (star φ)) = 2 := by
  let ρ : Matrix ι ι ℂ := Matrix.vecMulVec ψ (star ψ)
  let σ : Matrix ι ι ℂ := Matrix.vecMulVec φ (star φ)
  let P : Matrix ι ι ℂ := ρ + σ
  let X : Matrix ι ι ℂ := ρ - σ
  have hρpos : ρ.PosSemidef := by simpa [ρ] using Matrix.posSemidef_vecMulVec_self_star ψ
  have hσpos : σ.PosSemidef := by simpa [σ] using Matrix.posSemidef_vecMulVec_self_star φ
  have hρtr : Matrix.trace ρ = 1 := by simpa [ρ, hψ] using Matrix.trace_vecMulVec ψ (star ψ)
  have hσtr : Matrix.trace σ = 1 := by simpa [σ, hφ] using Matrix.trace_vecMulVec φ (star φ)
  have hρσ : ρ * σ = 0 := by
    simp [ρ, σ, Matrix.vecMulVec_mul_vecMulVec, horth]
  have hσρ : σ * ρ = 0 := by
    have horth' : star φ ⬝ᵥ ψ = 0 := by
      rw [star_dotProduct, horth]
      simp
    simp [ρ, σ, Matrix.vecMulVec_mul_vecMulVec, horth']
  have hρsq : ρ * ρ = ρ := by
    simp [ρ, Matrix.vecMulVec_mul_vecMulVec, hψ, dotProduct_comm]
  have hσsq : σ * σ = σ := by
    simp [σ, Matrix.vecMulVec_mul_vecMulVec, hφ, dotProduct_comm]
  have hXsq : Xᴴ * X = P := by
    calc
      Xᴴ * X = (ρ - σ)ᴴ * (ρ - σ) := by rfl
      _ = (ρ - σ) * (ρ - σ) := by simp [ρ, σ, Matrix.conjTranspose_vecMulVec]
      _ = ρ * ρ - ρ * σ - σ * ρ + σ * σ := by
            noncomm_ring
      _ = P := by simp [P, hρsq, hσsq, hρσ, hσρ]
  have hPidem : P * P = P := by
    calc
      P * P = (ρ + σ) * (ρ + σ) := by rfl
      _ = ρ * ρ + ρ * σ + σ * ρ + σ * σ := by
            noncomm_ring
      _ = P := by simp [P, hρsq, hσsq, hρσ, hσρ]
  have hPself : Pᴴ = P := by simp [P, ρ, σ, Matrix.conjTranspose_vecMulVec]
  have hPcts : Pᴴ * P = P := by simpa [hPself] using hPidem
  calc
    traceNormOp X = traceNormOp P := by
      apply traceNormOp_eq_of_conjTranspose_mul_self_eq
      simpa [X, hPcts] using hXsq.trans hPcts.symm
    _ = Complex.re (Matrix.trace P) := traceNormOp_posSemidef_eq_trace (hρpos.add hσpos)
    _ = 2 := by norm_num [P, hρtr, hσtr]

/-- Background unitary-channel diamond-distance formula used for Eq. (8). -/
theorem unitary_channel_diamond_distance_eq_two_of_trace_zero
    {d : Type u} [Fintype d] [DecidableEq d] [Nonempty d] (U : Matrix d d ℂ) (hU : Uᴴ * U = 1)
    (htrace : Matrix.trace U = 0) :
    diamondOp (idMinus (adMap d U)) = 2 := by
  have hup : diamondOp (idMinus (adMap d U)) ≤ 2 := by
    refine diamond_le_of_pointwise_nonempty (d := d) (Φ := idMinus (adMap d U)) 2 ?_
    intro ρ
    let K : Matrix (d × d) (d × d) ℂ := U ⊗ₖ (1 : Matrix d d ℂ)
    have hK : Kᴴ * K = 1 := by
      calc
        Kᴴ * K = ((U ⊗ₖ (1 : Matrix d d ℂ))ᴴ) * (U ⊗ₖ (1 : Matrix d d ℂ)) := by
          rfl
        _ = (Uᴴ ⊗ₖ (1 : Matrix d d ℂ)ᴴ) * (U ⊗ₖ (1 : Matrix d d ℂ)) := by
          rw [Matrix.conjTranspose_kronecker]
        _ = (Uᴴ * U) ⊗ₖ ((1 : Matrix d d ℂ)ᴴ * (1 : Matrix d d ℂ)) := by
          rw [Matrix.mul_kronecker_mul]
        _ = (1 : Matrix d d ℂ) ⊗ₖ (1 : Matrix d d ℂ) := by simp [hU]
        _ = 1 := by exact one_kronecker_one (α := ℂ) (m := d) (n := d)
    let σ : Matrix (d × d) (d × d) ℂ := tensorWithIdentity d d (adMap d U) ρ.1
    have hσeq : σ = K * ρ.1 * Kᴴ := by
      ext i j
      simpa [σ, K] using
        congrArg (fun M => M i j) (tensorWithIdentity_adMap_eq_kronecker U ρ.1)
    have hσdens : IsDensityState σ := by
      refine ⟨?_, ?_⟩
      · rw [hσeq]
        simpa [K] using ρ.2.1.conjTranspose_mul_mul_same Kᴴ
      · rw [hσeq]
        calc
          Matrix.trace (K * ρ.1 * Kᴴ) = Matrix.trace ((Kᴴ * K) * ρ.1) := by
            simpa [Matrix.mul_assoc] using Matrix.trace_mul_cycle K ρ.1 Kᴴ
          _ = Matrix.trace ρ.1 := by rw [hK, one_mul]
          _ = 1 := ρ.2.2
    simpa [idMinus, σ] using traceNormOp_sub_density_le_two ρ.2 hσdens
  have hlow : 2 ≤ diamondOp (idMinus (adMap d U)) := by
    let ρ : DensityState (d × d) :=
      ⟨phiStateGen d,
        vecMulVec_isDensityState_of_dotProduct_one (omegaVecGen d) (omegaVecGen_dot_self d)⟩
    have hσ :
        tensorWithIdentity d d (adMap d U) ρ.1 =
          Matrix.vecMulVec (unitaryVecGen d U) (star (unitaryVecGen d U)) := by
      simpa [ρ] using tensorWithIdentity_adMap_phiStateGen (d := d) U
    have hwit :
        traceNormOp (tensorWithIdentity d d (idMinus (adMap d U)) ρ.1) ≤
          diamondOp (idMinus (adMap d U)) :=
      traceNorm_apply_le_diamond (d := d) (k := d) (Φ := idMinus (adMap d U)) ρ
    have hnorm : traceNormOp (tensorWithIdentity d d (idMinus (adMap d U)) ρ.1) = 2 := by
      rw [show tensorWithIdentity d d (idMinus (adMap d U)) ρ.1 =
            Matrix.vecMulVec (omegaVecGen d) (star (omegaVecGen d)) -
              Matrix.vecMulVec (unitaryVecGen d U) (star (unitaryVecGen d U)) from by
            calc
              tensorWithIdentity d d (idMinus (adMap d U)) ρ.1
                  = ρ.1 - tensorWithIdentity d d (adMap d U) ρ.1 := by
                      rfl
              _ = ρ.1 - Matrix.vecMulVec (unitaryVecGen d U) (star (unitaryVecGen d U)) := by
                    rw [hσ]
              _ = Matrix.vecMulVec (omegaVecGen d) (star (omegaVecGen d)) -
                    Matrix.vecMulVec (unitaryVecGen d U) (star (unitaryVecGen d U)) := by
                    simp [ρ, phiStateGen]]
      exact traceNorm_vecMulVec_sub_vecMulVec_of_orthogonal
        (omegaVecGen d) (unitaryVecGen d U)
        (omegaVecGen_dot_self d)
        (unitaryVecGen_dot_self (d := d) U hU)
        (omegaVecGen_orthogonal_unitaryVecGen (d := d) U htrace)
    linarith [hwit, hnorm]
  exact le_antisymm hup hlow

/-- The phase-unitary trace vanishes because it is the full sum of the nontrivial `d`th
roots of unity. -/
theorem trace_Ud_eq_zero (d : ℕ) [Fact (1 < d)] :
    Matrix.trace (Ud d) = 0 := by
  have hd_ne_zero : d ≠ 0 := Nat.ne_of_gt (lt_trans Nat.zero_lt_one ‹Fact (1 < d)›.out)
  let ζ : ℂ := Complex.exp ((2 * Real.pi * Complex.I) / (d : ℂ))
  have hprim : IsPrimitiveRoot ζ d := by
    simpa [ζ] using Complex.isPrimitiveRoot_exp d hd_ne_zero
  have hpow :
      ∀ i : Fin d,
        Complex.exp ((2 * Real.pi * Complex.I * (i : ℂ)) / (d : ℂ)) = ζ ^ (i : ℕ) := by
    intro i
    calc
      Complex.exp ((2 * Real.pi * Complex.I * (i : ℂ)) / (d : ℂ))
        = Complex.exp (((i : ℕ) : ℂ) * ((2 * Real.pi * Complex.I) / (d : ℂ))) := by
            ring_nf
      _ = ζ ^ (i : ℕ) := by
            rw [Complex.exp_nat_mul]
  have htrace :
      Matrix.trace (Ud d) = ∑ i : Fin d, ζ ^ (i : ℕ) := by
    simp [Ud, Matrix.trace_diagonal, hpow]
  have hsum :
      (∑ i : Fin d, ζ ^ (i : ℕ)) = Finset.sum (Finset.range d) (fun i : ℕ => ζ ^ i) := by
    simpa using (Fin.sum_univ_eq_sum_range (fun i : ℕ => ζ ^ i) d)
  calc
    Matrix.trace (Ud d) = ∑ i : Fin d, ζ ^ (i : ℕ) := htrace
    _ = Finset.sum (Finset.range d) (fun i : ℕ => ζ ^ i) := hsum
    _ = 0 := by
          simpa using hprim.geom_sum_eq_zero ‹Fact (1 < d)›.out

/-- Finite-dimensional attainment of the left-hand diamond norm in the positive-gap argument.
    This compactness/maximizer step is background to the paper's main flow. -/
axiom exists_maximizing_state
    {d : Type u} [Fintype d] [DecidableEq d] [Nonempty d]
    (T : Channel d) (hT : IsQuantumChannel T) (hΦ : idMinus T ≠ 0) :
    ∃ ρ : DensityState (d × d),
      traceNormOp
          (tensorWithIdentity d d ((transposeMap d).comp (idMinus T)) ρ.1) =
        diamondOp ((transposeMap d).comp (idMinus T)) ∧
      tensorWithIdentity d d (idMinus T) ρ.1 ≠ 0

/-- Background spectral form of a nonzero rank-two traceless Hermitian matrix. -/
axiom rank_two_traceless_hermitian_decomposition
    {d : Type u} [Fintype d] [DecidableEq d] [Nonempty d]
    {X : Matrix (d × d) (d × d) ℂ} :
    X ≠ 0 →
    Matrix.IsHermitian X →
    Matrix.trace X = 0 →
    X.rank = 2 →
    ∃ c : ℂ, ∃ ψ φ : d × d → ℂ,
      c ≠ 0 ∧
      X = c • (Matrix.vecMulVec ψ (star ψ) - Matrix.vecMulVec φ (star φ))

/-- Background pure-state form of Uhlmann's theorem. -/
axiom uhlmann_theorem_pure
    {d : Type u} [Fintype d] [DecidableEq d]
    (ψ φ : d × d → ℂ)
    (hred :
      partialTraceLeft d d (Matrix.vecMulVec ψ (star ψ)) =
        partialTraceLeft d d (Matrix.vecMulVec φ (star φ))) :
    ∃ U : Matrix d d ℂ, Uᴴ * U = 1 ∧
      φ = fun ij => ∑ a, U ij.1 a * ψ (a, ij.2)

set_option maxHeartbeats 1000000
/-- Background unitary diagonalization theorem. -/
theorem unitary_diagonalization
    {d : Type u} [Fintype d] [DecidableEq d]
    (U : Matrix d d ℂ) (hU : Uᴴ * U = 1) :
    ∃ V : Matrix d d ℂ, ∃ ω : d → ℂ,
      Vᴴ * V = 1 ∧
      (∀ i, ω i * star (ω i) = 1) ∧
      U = V * Matrix.diagonal ω * Vᴴ := by
  let L : EuclideanSpace ℂ d →ₗ[ℂ] EuclideanSpace ℂ d := Matrix.toEuclideanLin U
  have toEuclideanLin_mul :
      ∀ A B : Matrix d d ℂ,
        Matrix.toEuclideanLin (A * B) = Matrix.toEuclideanLin A ∘ₗ Matrix.toEuclideanLin B := by
    intro A B
    rw [Matrix.toEuclideanLin_eq_toLin_orthonormal]
    simpa [Matrix.toEuclideanLin_eq_toLin_orthonormal] using
      (Matrix.toLin_mul
        (EuclideanSpace.basisFun d ℂ).toBasis
        (EuclideanSpace.basisFun d ℂ).toBasis
        (EuclideanSpace.basisFun d ℂ).toBasis A B)
  have hLadjL : LinearMap.adjoint L ∘ₗ L = LinearMap.id := by
    calc
      LinearMap.adjoint L ∘ₗ L = Matrix.toEuclideanLin Uᴴ ∘ₗ Matrix.toEuclideanLin U := by
        simp [L, Matrix.toEuclideanLin_conjTranspose_eq_adjoint]
      _ = Matrix.toEuclideanLin (Uᴴ * U) := (toEuclideanLin_mul _ _).symm
      _ = Matrix.toEuclideanLin (1 : Matrix d d ℂ) := by rw [hU]
      _ = LinearMap.id := by
        ext x i
        simp [Matrix.toEuclideanLin_eq_toLin_orthonormal]
  have hUmem : U ∈ Matrix.unitaryGroup d ℂ := (Matrix.mem_unitaryGroup_iff').2 hU
  have hUright : U * Uᴴ = 1 := (Matrix.mem_unitaryGroup_iff.mp hUmem)
  have hLLadj : L ∘ₗ LinearMap.adjoint L = LinearMap.id := by
    calc
      L ∘ₗ LinearMap.adjoint L = Matrix.toEuclideanLin U ∘ₗ Matrix.toEuclideanLin Uᴴ := by
        simp [L, Matrix.toEuclideanLin_conjTranspose_eq_adjoint]
      _ = Matrix.toEuclideanLin (U * Uᴴ) := (toEuclideanLin_mul _ _).symm
      _ = Matrix.toEuclideanLin (1 : Matrix d d ℂ) := by rw [hUright]
      _ = LinearMap.id := by
        ext x i
        simp [Matrix.toEuclideanLin_eq_toLin_orthonormal]
  have hcomm : Commute L (LinearMap.adjoint L) := by
    change L * LinearMap.adjoint L = LinearMap.adjoint L * L
    simpa [Module.End.mul_eq_comp] using hLLadj.trans hLadjL.symm
  let A0 : EuclideanSpace ℂ d →ₗ[ℂ] EuclideanSpace ℂ d := L + LinearMap.adjoint L
  let K0 : EuclideanSpace ℂ d →ₗ[ℂ] EuclideanSpace ℂ d := Complex.I • (LinearMap.adjoint L - L)
  have hA0self : IsSelfAdjoint A0 := by
    rw [LinearMap.isSelfAdjoint_iff']
    simp [A0, add_comm]
  have hK0self : IsSelfAdjoint K0 := by
    rw [LinearMap.isSelfAdjoint_iff']
    have hI : star (Complex.I : ℂ) = -Complex.I := by
      norm_num [Complex.ext_iff]
    calc
      LinearMap.adjoint K0 =
          star (Complex.I : ℂ) • LinearMap.adjoint (LinearMap.adjoint L - L) := by
            simp [K0, map_smulₛₗ LinearMap.adjoint]
      _ = (-Complex.I) • (L - LinearMap.adjoint L) := by
            simp [hI]
      _ = Complex.I • (LinearMap.adjoint L - L) := by
            simp [sub_eq_add_neg, add_comm, smul_add]
      _ = K0 := by
            rfl
  let A : EuclideanSpace ℂ d →ₗ[ℂ] EuclideanSpace ℂ d := ((1 / 2 : ℂ)) • A0
  let B : EuclideanSpace ℂ d →ₗ[ℂ] EuclideanSpace ℂ d := ((1 / 2 : ℂ)) • K0
  have hAself : IsSelfAdjoint A := by
    have hhalf : star ((1 / 2 : ℂ)) = (1 / 2 : ℂ) := by
      norm_num [Complex.ext_iff]
    have hA0adj : LinearMap.adjoint A0 = A0 := by
      simpa [LinearMap.isSelfAdjoint_iff'] using hA0self
    have hAadj : LinearMap.adjoint A = A := by
      calc
        LinearMap.adjoint A = LinearMap.adjoint (((1 / 2 : ℂ)) • A0) := by
          rfl
        _ = (starRingEnd ℂ ((1 / 2 : ℂ))) • LinearMap.adjoint A0 := by
          rw [map_smulₛₗ LinearMap.adjoint]
        _ = star ((1 / 2 : ℂ)) • LinearMap.adjoint A0 := by
          rw [starRingEnd_apply]
        _ = (1 / 2 : ℂ) • LinearMap.adjoint A0 := by
          rw [hhalf]
        _ = (1 / 2 : ℂ) • A0 := by
          rw [hA0adj]
        _ = A := by
          rfl
    exact (LinearMap.isSelfAdjoint_iff').2 hAadj
  have hBself : IsSelfAdjoint B := by
    have hhalf : star ((1 / 2 : ℂ)) = (1 / 2 : ℂ) := by
      norm_num [Complex.ext_iff]
    have hK0adj : LinearMap.adjoint K0 = K0 := by
      simpa [LinearMap.isSelfAdjoint_iff'] using hK0self
    have hBadj : LinearMap.adjoint B = B := by
      calc
        LinearMap.adjoint B = LinearMap.adjoint (((1 / 2 : ℂ)) • K0) := by
          rfl
        _ = (starRingEnd ℂ ((1 / 2 : ℂ))) • LinearMap.adjoint K0 := by
          rw [map_smulₛₗ LinearMap.adjoint]
        _ = star ((1 / 2 : ℂ)) • LinearMap.adjoint K0 := by
          rw [starRingEnd_apply]
        _ = (1 / 2 : ℂ) • LinearMap.adjoint K0 := by
          rw [hhalf]
        _ = (1 / 2 : ℂ) • K0 := by
          rw [hK0adj]
        _ = B := by
          rfl
    exact (LinearMap.isSelfAdjoint_iff').2 hBadj
  have hAsym : A.IsSymmetric := (LinearMap.isSymmetric_iff_isSelfAdjoint A).mpr hAself
  have hBsym : B.IsSymmetric := (LinearMap.isSymmetric_iff_isSelfAdjoint B).mpr hBself
  have hA0K0 : Commute A0 K0 := by
    exact (Commute.add_left (hcomm.sub_right (Commute.refl L))
      ((Commute.refl (LinearMap.adjoint L)).sub_right hcomm.symm)).smul_right Complex.I
  have hABcomm : Commute A B := by
    exact (hA0K0.smul_left ((1 / 2 : ℂ))).smul_right ((1 / 2 : ℂ))
  let Vpair : ℂ × ℂ → Submodule ℂ (EuclideanSpace ℂ d) := fun z =>
    eigenspace A z.2 ⊓ eigenspace B z.1
  let ι := {z : ℂ × ℂ // Vpair z ≠ ⊥}
  haveI : Finite ι := by
    let f : ι → Eigenvalues B × Eigenvalues A := fun z =>
      ⟨⟨z.1.1, by
          have hz : ⊥ < Vpair z.1 := bot_lt_iff_ne_bot.mpr z.2
          exact bot_lt_iff_ne_bot.mp <| lt_of_lt_of_le hz inf_le_right⟩,
        ⟨z.1.2, by
          have hz : ⊥ < Vpair z.1 := bot_lt_iff_ne_bot.mpr z.2
          exact bot_lt_iff_ne_bot.mp <| lt_of_lt_of_le hz inf_le_left⟩⟩
    exact Finite.of_injective f (by
      intro z1 z2 h
      apply Subtype.ext
      apply Prod.ext
      · exact congrArg Subtype.val (congrArg Prod.fst h)
      · exact congrArg Subtype.val (congrArg Prod.snd h))
  letI : Fintype ι := Fintype.ofFinite ι
  letI : DecidableEq ι := Classical.decEq ι
  let Vsub : ι → Submodule ℂ (EuclideanSpace ℂ d) := fun z => Vpair z.1
  have horthPair := LinearMap.IsSymmetric.orthogonalFamily_eigenspace_inf_eigenspace hAsym hBsym
  have horth : OrthogonalFamily ℂ (fun z : ι => Vsub z) fun z => (Vsub z).subtypeₗᵢ := by
    apply OrthogonalFamily.of_pairwise
    intro z1 z2 hne
    simpa [Vsub] using
      horthPair.pairwise (show z1.1 ≠ z2.1 from fun h => hne (Subtype.ext h))
  have htop : (⨆ z : ι, Vsub z) = ⊤ := by
    change (⨆ z : {z : ℂ × ℂ // Vpair z ≠ ⊥}, Vpair z.1) = ⊤
    rw [iSup_ne_bot_subtype]
    change (⨆ z : ℂ × ℂ, Vpair z) = ⊤
    rw [iSup_prod]
    rw [iSup_comm]
    simpa [Vpair] using
      LinearMap.IsSymmetric.iSup_iSup_eigenspace_inf_eigenspace_eq_top_of_commute
        hAsym hBsym hABcomm
  have hs : DirectSum.IsInternal Vsub :=
    horth.isInternal_iff.mpr <| by
      simpa [Submodule.orthogonal_eq_bot_iff] using htop
  let e : d ≃ Fin (Fintype.card d) := Fintype.equivOfCardEq (by simp)
  let b0 : OrthonormalBasis (Fin (Fintype.card d)) ℂ (EuclideanSpace ℂ d) :=
    hs.subordinateOrthonormalBasis (hn := finrank_euclideanSpace) horth
  let b : OrthonormalBasis d ℂ (EuclideanSpace ℂ d) := b0.reindex e.symm
  let idx : d → ι := fun i =>
    hs.subordinateOrthonormalBasisIndex (hn := finrank_euclideanSpace) (e i) horth
  let ω : d → ℂ := fun i => (idx i).1.2 + Complex.I * (idx i).1.1
  have hsub : ∀ i : d, b i ∈ Vsub (idx i) := by
    intro i
    simpa [b, idx, Vsub] using
      hs.subordinateOrthonormalBasis_subordinate (hn := finrank_euclideanSpace) (a := e i) horth
  have hLdecomp : L = A + Complex.I • B := by
    ext x i
    change (L x) i =
      ((1 / 2 : ℂ) * ((L x) i + ((LinearMap.adjoint L) x) i) +
        Complex.I * ((1 / 2 : ℂ) * (Complex.I * (((LinearMap.adjoint L) x) i - (L x) i))))
    ring_nf
    norm_num
    ring_nf
    have hone : (L x).ofLp i * ((1 : ℕ) : ℂ) = (L x).ofLp i := by
      norm_num
    exact hone.symm
  have hLadj : LinearMap.adjoint L = A - Complex.I • B := by
    have hAadj : LinearMap.adjoint A = A := by
      simpa [LinearMap.isSelfAdjoint_iff'] using hAself
    have hBadj : LinearMap.adjoint B = B := by
      simpa [LinearMap.isSelfAdjoint_iff'] using hBself
    have hI : star (Complex.I : ℂ) = -Complex.I := by
      norm_num [Complex.ext_iff]
    rw [hLdecomp]
    simp [map_smulₛₗ LinearMap.adjoint, hAadj, hBadj, hI, sub_eq_add_neg]
  have hLapply : ∀ i : d, L (b i) = ω i • b i := by
    intro i
    have hAi : b i ∈ eigenspace A ((idx i).1.2) := by
      exact (Submodule.mem_inf.mp (hsub i)).1
    have hBi : b i ∈ eigenspace B ((idx i).1.1) := by
      exact (Submodule.mem_inf.mp (hsub i)).2
    rw [hLdecomp]
    simpa [ω, smul_smul, mul_assoc] using
      show A (b i) + Complex.I • B (b i) = ω i • b i by
        simp [mem_eigenspace_iff.mp hAi, mem_eigenspace_iff.mp hBi, add_smul, ω, smul_smul,
          mul_assoc]
  have hLadj_apply : ∀ i : d, LinearMap.adjoint L (b i) = star (ω i) • b i := by
    intro i
    have hAi : b i ∈ eigenspace A ((idx i).1.2) := by
      exact (Submodule.mem_inf.mp (hsub i)).1
    have hBi : b i ∈ eigenspace B ((idx i).1.1) := by
      exact (Submodule.mem_inf.mp (hsub i)).2
    have hne : b i ≠ 0 := by
      simpa using b.toBasis.ne_zero i
    have hAreal : star ((idx i).1.2) = (idx i).1.2 := by
      simpa using hAsym.conj_eigenvalue_eq_self (hasEigenvalue_of_hasEigenvector ⟨hAi, hne⟩)
    have hBreal : star ((idx i).1.1) = (idx i).1.1 := by
      simpa using hBsym.conj_eigenvalue_eq_self (hasEigenvalue_of_hasEigenvector ⟨hBi, hne⟩)
    rw [hLadj]
    simpa [ω, smul_smul, mul_assoc] using
      show A (b i) + -(Complex.I • B (b i)) = star (ω i) • b i by
        simp [ω, hAreal, hBreal, mem_eigenspace_iff.mp hAi, mem_eigenspace_iff.mp hBi,
          sub_eq_add_neg, add_smul, smul_smul, mul_assoc]
  have hω : ∀ i : d, ω i * star (ω i) = 1 := by
    intro i
    have hne : b i ≠ 0 := by
      simpa using b.toBasis.ne_zero i
    have hcomp := congrArg (fun F : EuclideanSpace ℂ d →ₗ[ℂ] EuclideanSpace ℂ d => F (b i)) hLLadj
    have hscal : (ω i * star (ω i)) • b i = b i := by
      simpa [LinearMap.comp_apply, hLapply i, hLadj_apply i, smul_smul, mul_comm, mul_left_comm,
        mul_assoc] using hcomp
    have hcoord := congrArg (fun v : EuclideanSpace ℂ d => (b.repr v) i) hscal
    simpa using hcoord
  let bStd := (EuclideanSpace.basisFun d ℂ).toBasis
  let V : Matrix d d ℂ := bStd.toMatrix b.toBasis
  have hV : Vᴴ * V = 1 := by
    exact (Matrix.mem_unitaryGroup_iff'.mp
      ((EuclideanSpace.basisFun d ℂ).toMatrix_orthonormalBasis_mem_unitary b))
  have hVstar : b.toBasis.toMatrix bStd = Vᴴ := by
    have htmp : V = (b.toBasis.toMatrix bStd)ᴴ := by
      simpa [V] using
        (LinearMap.toMatrix_adjoint (v₁ := (EuclideanSpace.basisFun d ℂ)) (v₂ := b)
          (f := (LinearMap.id : EuclideanSpace ℂ d →ₗ[ℂ] EuclideanSpace ℂ d)))
    simpa [V] using (congrArg Matrix.conjTranspose htmp).symm
  have hdiag : LinearMap.toMatrix b.toBasis b.toBasis L = Matrix.diagonal ω := by
    ext i j
    by_cases hij : i = j
    · subst hij
      rw [show LinearMap.toMatrix b.toBasis b.toBasis L i i = LinearMap.toMatrixOrthonormal b L i i by
            rfl, LinearMap.toMatrixOrthonormal_apply_apply]
      simp [hLapply]
    · rw [show LinearMap.toMatrix b.toBasis b.toBasis L i j = LinearMap.toMatrixOrthonormal b L i j by
            rfl, LinearMap.toMatrixOrthonormal_apply_apply]
      simp [hLapply, hij]
  have hUstd : LinearMap.toMatrix bStd bStd L = U := by
    change (LinearMap.toMatrix bStd bStd) ((Matrix.toLin bStd bStd) U) = U
    exact LinearMap.toMatrix_toLin bStd bStd U
  have hchange : V * Matrix.diagonal ω * b.toBasis.toMatrix bStd = U := by
    calc
      V * Matrix.diagonal ω * b.toBasis.toMatrix bStd
          = bStd.toMatrix b.toBasis * LinearMap.toMatrix b.toBasis b.toBasis L *
              b.toBasis.toMatrix bStd := by
                rw [hdiag]
      _ = LinearMap.toMatrix bStd bStd L := by
            simpa [V] using
              (basis_toMatrix_mul_linearMap_toMatrix_mul_basis_toMatrix
                (b := bStd) (b' := b.toBasis) (c := bStd) (c' := b.toBasis) (f := L))
      _ = U := hUstd
  exact ⟨V, ω, hV, hω, by simpa [hVstar] using hchange.symm⟩

private def cotSeq (n : ℕ) : ℝ :=
  Real.cot (Real.pi / (2 * ((n : ℝ) + 2))) / ((n : ℝ) + 2)

private def xSeq (n : ℕ) : ℝ :=
  Real.pi / (2 * ((n : ℝ) + 2))

private theorem cotSeq_eq (n : ℕ) :
    cotSeq n = (2 / Real.pi) * (Real.cos (xSeq n) / Real.sinc (xSeq n)) := by
  have hxne : xSeq n ≠ 0 := by
    unfold xSeq
    positivity
  have hsinne : Real.sin (xSeq n) ≠ 0 := by
    have hxpos : 0 < xSeq n := by
      unfold xSeq
      positivity
    have hxle : xSeq n ≤ Real.pi / 4 := by
      unfold xSeq
      field_simp [show (2 * ((n : ℝ) + 2)) ≠ 0 by positivity]
      nlinarith [Real.pi_pos, show (0 : ℝ) ≤ n by positivity]
    exact
      (Real.sin_pos_of_pos_of_lt_pi hxpos
        (lt_of_le_of_lt hxle (by nlinarith [Real.pi_pos]))).ne'
  unfold cotSeq
  rw [Real.cot_eq_cos_div_sin, Real.sinc_of_ne_zero hxne]
  unfold xSeq
  field_simp [Real.pi_ne_zero, hxne, hsinne]

private theorem tendsto_xSeq_zero : Tendsto xSeq atTop (𝓝 0) := by
  have hinv : Tendsto (fun n : ℕ => ((n : ℝ) + (1 + 1))⁻¹) atTop (𝓝 0) := by
    have hinv0 := ((tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).comp (tendsto_add_atTop_nat 1))
    convert hinv0 using 1
    ext n
    simp [Function.comp, Nat.cast_add, Nat.cast_one, add_assoc]
  have hxEq : xSeq = fun n : ℕ => (Real.pi / 2) * (((n : ℝ) + (1 + 1))⁻¹) := by
    funext n
    have hadd : (n : ℝ) + (1 + 1 : ℝ) = (n : ℝ) + 2 := by
      norm_num
    rw [hadd]
    unfold xSeq
    field_simp [show ((n : ℝ) + 2) ≠ 0 by positivity, Real.pi_ne_zero]
  have hmul : Tendsto (fun n : ℕ => (Real.pi / 2) * (((n : ℝ) + (1 + 1))⁻¹)) atTop (𝓝 0) := by
    simpa using (Tendsto.const_mul (Real.pi / 2) hinv)
  simpa [hxEq, add_assoc] using hmul

private theorem tendsto_cotSeq : Tendsto cotSeq atTop (𝓝 ((2 : ℝ) / Real.pi)) := by
  have hcos : Tendsto (fun n => Real.cos (xSeq n)) atTop (𝓝 1) := by
    simpa using (Real.continuous_cos.tendsto 0).comp tendsto_xSeq_zero
  have hsinc : Tendsto (fun n => Real.sinc (xSeq n)) atTop (𝓝 1) := by
    simpa [Real.sinc_zero] using (Real.continuous_sinc.tendsto 0).comp tendsto_xSeq_zero
  have hratio : Tendsto (fun n => Real.cos (xSeq n) / Real.sinc (xSeq n)) atTop (𝓝 1) := by
    simpa using hcos.div hsinc one_ne_zero
  have hmul :
      Tendsto (fun n => ((2 : ℝ) / Real.pi) * (Real.cos (xSeq n) / Real.sinc (xSeq n))) atTop
        (𝓝 (2 / Real.pi)) := by
    simpa using (Tendsto.const_mul ((2 : ℝ) / Real.pi) hratio)
  convert hmul using 1
  ext n
  exact cotSeq_eq n

/-- Background asymptotic cotangent lower bound used to pass from finite `d`
    to the universal constant `2 / π`. -/
theorem asymptotic_cotangent_lower_bound
    {α : ℝ} :
    (∀ d : ℕ, 2 ≤ d → Real.cot (Real.pi / (2 * (d : ℝ))) / (d : ℝ) ≤ α) →
      (2 : ℝ) / Real.pi ≤ α := by
  intro hα
  have hbound : ∀ n : ℕ, cotSeq n ≤ α := by
    intro n
    simpa [cotSeq, Nat.cast_add, Nat.cast_one, add_assoc, add_left_comm, add_comm] using
      hα (n + 2) (by omega)
  exact le_of_tendsto' tendsto_cotSeq hbound

/-- Trace equals the trace of the left partial trace. -/
theorem trace_eq_trace_partialTraceLeft
    {d k : Type u} [Fintype d] [DecidableEq d] [Fintype k] [DecidableEq k]
    (X : Matrix (d × k) (d × k) ℂ) :
    Matrix.trace X = Matrix.trace (partialTraceLeft d k X) := by
  calc
    Matrix.trace X = ∑ a : d, ∑ i : k, X (a, i) (a, i) := by
      simp [Matrix.trace, Fintype.sum_prod_type]
    _ = ∑ i : k, ∑ a : d, X (a, i) (a, i) := by
      simpa using
        (Finset.sum_comm
          (s := (Finset.univ : Finset d))
          (t := (Finset.univ : Finset k))
          (f := fun a i => X (a, i) (a, i)))
    _ = Matrix.trace (partialTraceLeft d k X) := by
      simp [partialTraceLeft, Matrix.trace]

/-- Tensoring a trace-annihilating map with the identity has vanishing left partial trace. -/
theorem partialTraceLeft_tensor_zero
    {d k : Type u} [Fintype d] [DecidableEq d] [Fintype k] [DecidableEq k]
    (Ψ : Channel d) (hT : IsTraceAnnihilating Ψ)
    (Z : Matrix (d × k) (d × k) ℂ) :
    partialTraceLeft d k (tensorWithIdentity d k Ψ Z) = 0 := by
  ext i j
  have htrace :
      Matrix.trace (Ψ (fun a b : d => Z (a, i) (b, j))) = 0 :=
    hT _
  simpa [partialTraceLeft, tensorWithIdentity, Matrix.trace] using htrace

/-- Tensoring a trace-annihilating map with the identity gives traceless output. -/
theorem tensorWithIdentity_trace_zero
    {d k : Type u} [Fintype d] [DecidableEq d] [Fintype k] [DecidableEq k]
    (Ψ : Channel d) (hT : IsTraceAnnihilating Ψ)
    (Z : Matrix (d × k) (d × k) ℂ) :
    Matrix.trace (tensorWithIdentity d k Ψ Z) = 0 := by
  rw [trace_eq_trace_partialTraceLeft]
  simpa using
    congrArg Matrix.trace (partialTraceLeft_tensor_zero (d := d) (k := k) Ψ hT Z)

/-- Tensoring a Hermiticity-preserving map with the identity preserves Hermiticity. -/
theorem tensorWithIdentity_hermitian
    {d k : Type u} [Fintype d] [DecidableEq d] [Fintype k] [DecidableEq k]
    (Ψ : Channel d) (hH : IsHermiticityPreserving Ψ)
    (ρ : Matrix (d × k) (d × k) ℂ) (hρ : IsDensityState ρ) :
    Matrix.IsHermitian (tensorWithIdentity d k Ψ ρ) := by
  change (tensorWithIdentity d k Ψ ρ)ᴴ = tensorWithIdentity d k Ψ ρ
  ext p q
  let A : Matrix d d ℂ := fun i j => ρ (i, p.2) (j, q.2)
  have hρh : Matrix.IsHermitian ρ := hρ.1.isHermitian
  have hA : Aᴴ = fun i j : d => ρ (i, q.2) (j, p.2) := by
    ext i j
    simpa [A, Matrix.conjTranspose_apply] using
      congrArg (fun M => M (i, q.2) (j, p.2)) hρh.eq
  have hcomm := hH A
  have hpoint : Ψ Aᴴ q.1 p.1 = star (Ψ A p.1 q.1) := by
    simpa [Matrix.conjTranspose_apply] using congrArg (fun M => M q.1 p.1) hcomm
  have hpoint' : star (Ψ Aᴴ q.1 p.1) = Ψ A p.1 q.1 := by
    simpa using congrArg star hpoint
  simpa [A, hA, tensorWithIdentity, Matrix.conjTranspose_apply] using hpoint'

/-- Card-product square-root identity used for dimension reduction. -/
theorem sqrt_card_prod_self
    {d k : Type u} [Fintype d] [Fintype k] :
    Real.sqrt (Fintype.card (d × k) : ℝ) =
      Real.sqrt (Fintype.card d : ℝ) * Real.sqrt (Fintype.card k : ℝ) := by
  rw [Fintype.card_prod]
  rw [Nat.cast_mul]
  rw [Real.sqrt_mul (show (0 : ℝ) ≤ Fintype.card d by positivity)]
  -- no further simplification needed

end
end Diamond
