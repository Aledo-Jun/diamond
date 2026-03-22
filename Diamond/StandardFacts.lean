import Diamond.Setups
import Diamond.Theorem.Lemma1
import Diamond.Theorem.Lemma2
import Diamond.Theorem.Lemma3
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Sinc
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Analysis.Complex.Norm
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

theorem traceNormOp_eq_zero_iff
    {d : Type u} [Fintype d] [DecidableEq d]
    {X : Matrix d d ℂ} : traceNormOp X = 0 ↔ X = 0 := by
  constructor
  · intro h
    unfold traceNormOp traceNorm at h
    have hsqrt_zero :
        ∀ i : d, Real.sqrt ((Matrix.isHermitian_conjTranspose_mul_self X).eigenvalues i) = 0 := by
      intro i
      exact (Finset.sum_eq_zero_iff_of_nonneg (fun j _ => Real.sqrt_nonneg _)).mp h i (by simp)
    have heig_zero :
        ∀ i : d, (Matrix.isHermitian_conjTranspose_mul_self X).eigenvalues i = 0 := by
      intro i
      have hnonneg : 0 ≤ (Matrix.isHermitian_conjTranspose_mul_self X).eigenvalues i := by
        exact Matrix.eigenvalues_conjTranspose_mul_self_nonneg X i
      nlinarith [Real.sq_sqrt hnonneg, hsqrt_zero i]
    have htrace_zero : Complex.re (Matrix.trace (Xᴴ * X)) = 0 := by
      rw [(Matrix.isHermitian_conjTranspose_mul_self X).trace_eq_sum_eigenvalues]
      simp [heig_zero]
    have hhs_sq : hsNormOp X ^ 2 = 0 := by
      rw [hsNorm_sq_eq_re_trace_conjTranspose_mul_self, htrace_zero]
    have hhs : hsNormOp X = 0 := by
      have hnonneg : 0 ≤ hsNormOp X := hsNorm_nonneg X
      nlinarith
    exact hsNormOp_eq_zero_iff.mp hhs
  · intro h
    subst h
    simpa using traceNormOp_posSemidef_eq_trace
      (A := (0 : Matrix d d ℂ)) Matrix.PosSemidef.zero

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

set_option backward.isDefEq.respectTransparency false in
private theorem posSemidef_iff_eq_conjTranspose_mul_self'
    {n : Type u} [Fintype n] {A : Matrix n n ℂ} :
    A.PosSemidef ↔ ∃ B : Matrix n n ℂ, A = Bᴴ * B := by
  classical
  exact Matrix.nonneg_iff_posSemidef (A := A) |>.eq ▸
    CStarAlgebra.nonneg_iff_eq_star_mul_self

/-- Concrete witness bound for the diamond norm defined in `Setups`. -/
-- Immediate from the definition of `diamondNormAt`; kept as an explicit axiom in this split
-- to avoid introducing an auxiliary compactness/attainment argument at this layer.
theorem traceNorm_apply_le_diamond
    {d : Type u} [Fintype d] [DecidableEq d] {k : Type u}
    [Fintype k] [DecidableEq k]
    (Φ : Channel d) (ρ : DensityState (d × k)) :
    traceNormOp (tensorWithIdentity d k Φ ρ.1) ≤ diamondNormAt (d := d) (k := k) Φ := by
  let Ψ : Channel (d × k) := tensorWithIdentity d k Φ
  let B : (d × k) × (d × k) → ℝ := fun p =>
    hsNormOp (Ψ (Matrix.single p.1 p.2 (1 : ℂ)))
  have hρhs : hsNormOp ρ.1 ≤ 1 := by
    rcases posSemidef_iff_eq_conjTranspose_mul_self'.mp ρ.2.1 with ⟨M, hM⟩
    have hsum : ∑ i, ∑ j, ‖M i j‖ ^ (2 : ℝ) = 1 := by
      have htrace : Matrix.trace (Mᴴ * M) = 1 := by
        simpa [hM] using ρ.2.2
      have hre := congrArg Complex.re htrace
      have haux :
          Complex.re (Matrix.trace (Mᴴ * M)) =
            ∑ i, ∑ j, ‖M i j‖ ^ (2 : ℝ) := by
        calc
          Complex.re (Matrix.trace (Mᴴ * M)) = ∑ i, Complex.re ((Mᴴ * M) i i) := by
            simp [Matrix.trace]
          _ = ∑ i, ∑ j, ‖M j i‖ ^ (2 : ℝ) := by
                simp [Matrix.mul_apply, Matrix.conjTranspose_apply, RCLike.norm_sq_eq_def]
          _ = ∑ i, ∑ j, ‖M i j‖ ^ (2 : ℝ) := by
                rw [Finset.sum_comm]
      simpa [haux] using hre
    have hMnorm : hsNormOp M = 1 := by
      change ‖M‖ = 1
      rw [Matrix.frobenius_norm_def, hsum]
      norm_num
    have hMstar : hsNormOp Mᴴ = hsNormOp M := by
      change ‖Mᴴ‖ = ‖M‖
      exact Matrix.frobenius_norm_conjTranspose M
    calc
      hsNormOp ρ.1 = hsNormOp (Mᴴ * M) := by
        rw [hM]
      _ ≤ hsNormOp Mᴴ * hsNormOp M := by
        change ‖Mᴴ * M‖ ≤ ‖Mᴴ‖ * ‖M‖
        exact Matrix.frobenius_norm_mul _ _
      _ = hsNormOp M * hsNormOp M := by
        rw [hMstar]
      _ = 1 := by
        rw [hMnorm]
        ring
  have hdecomp (A : Matrix (d × k) (d × k) ℂ) :
      A = ∑ i : d × k, ∑ j : d × k, A i j • Matrix.single i j (1 : ℂ) := by
    simpa [Matrix.smul_single] using Matrix.matrix_eq_sum_single A
  have hhs (A : Matrix (d × k) (d × k) ℂ) :
      hsNormOp (Ψ A) ≤
        hsNormOp A * Real.sqrt (∑ p : (d × k) × (d × k), B p ^ (2 : ℝ)) := by
    let coeff : (d × k) × (d × k) → ℝ := fun p => ‖A p.1 p.2‖
    have hsingleSum :
        (∑ i : d × k, ∑ j : d × k, Matrix.single i j (A i j)) =
          ∑ i : d × k, ∑ j : d × k, A i j • Matrix.single i j (1 : ℂ) := by
      refine Finset.sum_congr rfl ?_
      intro i hi
      refine Finset.sum_congr rfl ?_
      intro j hj
      simp [Matrix.smul_single]
    have hrew :
        hsNormOp (Ψ A) =
          hsNormOp (Ψ (∑ i : d × k, ∑ j : d × k, A i j • Matrix.single i j (1 : ℂ))) := by
      calc
        hsNormOp (Ψ A) =
            hsNormOp (Ψ (∑ i : d × k, ∑ j : d × k, Matrix.single i j (A i j))) := by
              exact congrArg (fun M => hsNormOp (Ψ M)) (Matrix.matrix_eq_sum_single A)
        _ = hsNormOp (Ψ (∑ i : d × k, ∑ j : d × k, A i j • Matrix.single i j (1 : ℂ))) := by
              rw [hsingleSum]
    have hsum :
        hsNormOp (Ψ A) ≤
          ∑ p : (d × k) × (d × k), coeff p * B p := by
      have hmap :
          Ψ (∑ i : d × k, ∑ j : d × k, A i j • Matrix.single i j (1 : ℂ)) =
            ∑ i : d × k, ∑ j : d × k, A i j • Ψ (Matrix.single i j (1 : ℂ)) := by
              rw [map_sum]
              refine Finset.sum_congr rfl ?_
              intro i hi
              rw [map_sum]
              refine Finset.sum_congr rfl ?_
              intro j hj
              rw [map_smul]
      calc
        hsNormOp (Ψ A) =
            hsNormOp (Ψ (∑ i : d × k, ∑ j : d × k, A i j • Matrix.single i j (1 : ℂ))) := hrew
        _
          = ‖∑ i : d × k, ∑ j : d × k, A i j • Ψ (Matrix.single i j (1 : ℂ))‖ := by
              rw [hsNormOp, hsNorm, hmap]
        _ ≤ ∑ i : d × k, ‖∑ j : d × k, A i j • Ψ (Matrix.single i j (1 : ℂ))‖ := by
              exact norm_sum_le _ _
        _ ≤ ∑ i : d × k, ∑ j : d × k, ‖A i j • Ψ (Matrix.single i j (1 : ℂ))‖ := by
              refine Finset.sum_le_sum ?_
              intro i hi
              exact norm_sum_le _ _
        _ = ∑ i : d × k, ∑ j : d × k, ‖A i j‖ * hsNormOp (Ψ (Matrix.single i j (1 : ℂ))) := by
              simp [hsNormOp, hsNorm, norm_smul]
        _ = ∑ p : (d × k) × (d × k), coeff p * B p := by
              simp [coeff, B, Fintype.sum_prod_type]
    have hcs :
        ∑ p : (d × k) × (d × k), coeff p * B p ≤
          Real.sqrt (∑ p : (d × k) × (d × k), coeff p ^ (2 : ℝ)) *
            Real.sqrt (∑ p : (d × k) × (d × k), B p ^ (2 : ℝ)) := by
      simpa using Real.sum_mul_le_sqrt_mul_sqrt (Finset.univ : Finset ((d × k) × (d × k))) coeff B
    have hcoeff :
        Real.sqrt (∑ p : (d × k) × (d × k), coeff p ^ (2 : ℝ)) = hsNormOp A := by
      have hnonneg :
          0 ≤ ∑ p : (d × k) × (d × k), coeff p ^ (2 : ℝ) := by
            positivity
      calc
        Real.sqrt (∑ p : (d × k) × (d × k), coeff p ^ (2 : ℝ))
          = (∑ p : (d × k) × (d × k), coeff p ^ (2 : ℝ)) ^ (1 / 2 : ℝ) := by
              rw [Real.sqrt_eq_rpow]
        _ = hsNormOp A := by
              simp [coeff, hsNormOp, hsNorm, Matrix.frobenius_norm_def, Fintype.sum_prod_type]
    calc
      hsNormOp (Ψ A) ≤ ∑ p : (d × k) × (d × k), coeff p * B p := hsum
      _ ≤ Real.sqrt (∑ p : (d × k) × (d × k), coeff p ^ (2 : ℝ)) *
            Real.sqrt (∑ p : (d × k) × (d × k), B p ^ (2 : ℝ)) := hcs
      _ = hsNormOp A * Real.sqrt (∑ p : (d × k) × (d × k), B p ^ (2 : ℝ)) := by
            rw [hcoeff]
  let C : ℝ := Real.sqrt (Fintype.card (d × k) : ℝ) *
      Real.sqrt (∑ p : (d × k) × (d × k), B p ^ (2 : ℝ))
  have hbound :
      BddAbove {r : ℝ | ∃ ρ' : DensityState (d × k), r = traceNormOp (Ψ ρ'.1)} := by
    refine ⟨C, ?_⟩
    intro r hr
    rcases hr with ⟨ρ', rfl⟩
    have hlemma2 :
        traceNormOp (Ψ ρ'.1) ≤
          Real.sqrt (Fintype.card (d × k) : ℝ) * hsNormOp (Ψ ρ'.1) := by
      simpa [Ψ] using lemma2 (Y := Ψ ρ'.1)
    have hhsρ : hsNormOp (Ψ ρ'.1) ≤
        hsNormOp ρ'.1 * Real.sqrt (∑ p : (d × k) × (d × k), B p ^ (2 : ℝ)) := hhs ρ'.1
    have hρ'hs : hsNormOp ρ'.1 ≤ 1 := by
      rcases posSemidef_iff_eq_conjTranspose_mul_self'.mp ρ'.2.1 with ⟨M, hM⟩
      have hsum : ∑ i, ∑ j, ‖M i j‖ ^ (2 : ℝ) = 1 := by
        have htrace : Matrix.trace (Mᴴ * M) = 1 := by
          simpa [hM] using ρ'.2.2
        have hre := congrArg Complex.re htrace
        have haux :
            Complex.re (Matrix.trace (Mᴴ * M)) =
              ∑ i, ∑ j, ‖M i j‖ ^ (2 : ℝ) := by
          calc
            Complex.re (Matrix.trace (Mᴴ * M)) = ∑ i, Complex.re ((Mᴴ * M) i i) := by
              simp [Matrix.trace]
            _ = ∑ i, ∑ j, ‖M j i‖ ^ (2 : ℝ) := by
                  simp [Matrix.mul_apply, Matrix.conjTranspose_apply, RCLike.norm_sq_eq_def]
            _ = ∑ i, ∑ j, ‖M i j‖ ^ (2 : ℝ) := by
                  rw [Finset.sum_comm]
        simpa [haux] using hre
      have hMnorm : hsNormOp M = 1 := by
        change ‖M‖ = 1
        rw [Matrix.frobenius_norm_def, hsum]
        norm_num
      have hMstar : hsNormOp Mᴴ = hsNormOp M := by
        change ‖Mᴴ‖ = ‖M‖
        exact Matrix.frobenius_norm_conjTranspose M
      calc
        hsNormOp ρ'.1 = hsNormOp (Mᴴ * M) := by rw [hM]
        _ ≤ hsNormOp Mᴴ * hsNormOp M := by
              change ‖Mᴴ * M‖ ≤ ‖Mᴴ‖ * ‖M‖
              exact Matrix.frobenius_norm_mul _ _
        _ = hsNormOp M * hsNormOp M := by rw [hMstar]
        _ = 1 := by rw [hMnorm]; ring
    calc
      traceNormOp (Ψ ρ'.1) ≤ Real.sqrt (Fintype.card (d × k) : ℝ) * hsNormOp (Ψ ρ'.1) := hlemma2
      _ ≤ Real.sqrt (Fintype.card (d × k) : ℝ) *
            (hsNormOp ρ'.1 * Real.sqrt (∑ p : (d × k) × (d × k), B p ^ (2 : ℝ))) := by
              exact mul_le_mul_of_nonneg_left hhsρ (Real.sqrt_nonneg _)
      _ ≤ Real.sqrt (Fintype.card (d × k) : ℝ) *
            (1 * Real.sqrt (∑ p : (d × k) × (d × k), B p ^ (2 : ℝ))) := by
              exact mul_le_mul_of_nonneg_left
                (mul_le_mul_of_nonneg_right hρ'hs (Real.sqrt_nonneg _))
                (Real.sqrt_nonneg _)
      _ = C := by
            simp [C]
  unfold diamondNormAt
  exact le_csSup hbound ⟨ρ, rfl⟩

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
            · simp [Matrix.kroneckerMap_apply]
            · intro z hz hzb
              have hbz' : b ≠ z := by
                exact fun h => hzb h.symm
              have hbz : (1 : Matrix k k ℂ) b z = 0 := by
                simp [hbz']
              simp [Matrix.kroneckerMap_apply, hbz]
            · simp
          have hright :
              (((U ⊗ₖ (1 : Matrix k k ℂ)) * X) * (U ⊗ₖ (1 : Matrix k k ℂ))ᴴ) (a, b) (c, e) =
                ∑ y : d, ((U ⊗ₖ (1 : Matrix k k ℂ)) * X) (a, b) (y, e) * star (U c y) := by
            rw [Matrix.mul_apply, Fintype.sum_prod_type]
            refine Finset.sum_congr rfl ?_
            intro y hy
            rw [Finset.sum_eq_single e]
            · simp [Matrix.kroneckerMap_apply, Matrix.conjTranspose_apply]
            · intro z hz hze
              have hez' : e ≠ z := by
                exact fun h => hze h.symm
              have hez : (1 : Matrix k k ℂ) e z = 0 := by
                simp [hez']
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
    (d : Type u) [Fintype d] [Nonempty d] :
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
            simp [omegaVecGen, mul_comm]
    _ = 1 := by
          rw [inv_sqrt_mul_inv_sqrt_card (d := d)]
          field_simp [show (Fintype.card d : ℂ) ≠ 0 by positivity]

private theorem densityState_hsNorm_le_one
    {n : Type u} [Fintype n] [DecidableEq n]
    (ρ : DensityState n) : hsNormOp ρ.1 ≤ 1 := by
  rcases posSemidef_iff_eq_conjTranspose_mul_self'.mp ρ.2.1 with ⟨B, hB⟩
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
    exact Matrix.frobenius_norm_conjTranspose B
  calc
    hsNormOp ρ.1 = hsNormOp (Bᴴ * B) := by
      rw [hB]
    _ ≤ hsNormOp Bᴴ * hsNormOp B := by
      change ‖Bᴴ * B‖ ≤ ‖Bᴴ‖ * ‖B‖
      exact Matrix.frobenius_norm_mul _ _
    _ = hsNormOp B * hsNormOp B := by
      rw [hBstar]
    _ = 1 := by
      rw [hBnorm]
      ring

private theorem isClosed_isHermitian_set
    {n : Type u} :
    IsClosed {M : Matrix n n ℂ | Matrix.IsHermitian M} := by
  have hct : Continuous fun ρ : Matrix n n ℂ => ρᴴ := by
    fun_prop
  simpa [Matrix.IsHermitian, Set.setOf_eq_eq_singleton] using isClosed_eq hct continuous_id

private theorem continuous_dotProduct_mulVec
    {n : Type u} [Fintype n] (x : n → ℂ) :
    Continuous fun M : Matrix n n ℂ => star x ⬝ᵥ (M *ᵥ x) := by
  classical
  letI : NormedSpace ℂ (Matrix n n ℂ) := Matrix.frobeniusNormedSpace
  let f : Matrix n n ℂ →ₗ[ℂ] ℂ :=
    { toFun := fun M => star x ⬝ᵥ (M *ᵥ x)
      map_add' := by intro A B; simp [Matrix.add_mulVec, dotProduct_add]
      map_smul' := by intro c A; simp [Matrix.smul_mulVec, dotProduct_smul] }
  simpa using f.continuous_of_finiteDimensional

private theorem isClosed_posSemidef_set
    {n : Type u} [Finite n] :
    IsClosed {M : Matrix n n ℂ | M.PosSemidef} := by
  classical
  letI : Fintype n := Fintype.ofFinite n
  suffices
      IsClosed {M : Matrix n n ℂ | M.IsHermitian ∧ ∀ x : n → ℂ, 0 ≤ star x ⬝ᵥ (M *ᵥ x)} by
    simpa [Matrix.posSemidef_iff_dotProduct_mulVec] using this
  refine isClosed_isHermitian_set.inter ?_
  have hquad :
      IsClosed {M : Matrix n n ℂ | ∀ x : n → ℂ, 0 ≤ star x ⬝ᵥ (M *ᵥ x)} := by
    simpa [Set.setOf_forall] using
      (isClosed_iInter
        (f := fun x : n → ℂ => {M : Matrix n n ℂ | 0 ≤ star x ⬝ᵥ (M *ᵥ x)})
        fun x => by
          simpa [Set.preimage, Set.setOf_mem_eq] using
            (isClosed_Ici.preimage (continuous_dotProduct_mulVec x) :
              IsClosed ((fun M : Matrix n n ℂ => star x ⬝ᵥ (M *ᵥ x)) ⁻¹' Set.Ici (0 : ℂ))))
  exact hquad

private theorem isCompact_densityStateSet
    {n : Type u} [Fintype n] [DecidableEq n] :
    IsCompact ({ρ : Matrix n n ℂ | IsDensityState ρ} : Set (Matrix n n ℂ)) := by
  letI : NormedAddCommGroup (Matrix n n ℂ) := Matrix.frobeniusNormedAddCommGroup
  letI : NormedSpace ℂ (Matrix n n ℂ) := Matrix.frobeniusNormedSpace
  have hclosed : IsClosed ({ρ : Matrix n n ℂ | IsDensityState ρ} : Set (Matrix n n ℂ)) := by
    have htr : IsClosed {A : Matrix n n ℂ | Matrix.trace A = 1} := by
      simpa using
        isClosed_eq ((Matrix.traceLinearMap n ℂ ℂ).continuous_of_finiteDimensional) continuous_const
    simpa [IsDensityState, Set.setOf_and] using isClosed_posSemidef_set.inter htr
  have hbounded :
      Bornology.IsBounded ({ρ : Matrix n n ℂ | IsDensityState ρ} : Set (Matrix n n ℂ)) := by
    refine (Metric.isBounded_closedBall (x := (0 : Matrix n n ℂ)) (r := 1)).subset ?_
    intro ρ hρ
    simp [Metric.mem_closedBall, dist_eq_norm]
    simpa [hsNormOp, hsNorm] using densityState_hsNorm_le_one ⟨ρ, hρ⟩
  letI : FiniteDimensional ℂ (Matrix n n ℂ) := inferInstance
  letI : ProperSpace (Matrix n n ℂ) :=
    @FiniteDimensional.proper ℂ inferInstance (Matrix n n ℂ)
      Matrix.frobeniusNormedAddCommGroup Matrix.frobeniusNormedSpace inferInstance inferInstance
  exact Metric.isCompact_of_isClosed_isBounded hclosed hbounded

private theorem isCompact_unitarySet
    {n : Type u} [Fintype n] [DecidableEq n] :
    IsCompact ({U : Matrix n n ℂ | U ∈ Matrix.unitaryGroup n ℂ} : Set (Matrix n n ℂ)) := by
  letI : NormedAddCommGroup (Matrix n n ℂ) := Matrix.frobeniusNormedAddCommGroup
  letI : NormedSpace ℂ (Matrix n n ℂ) := Matrix.frobeniusNormedSpace
  have hclosed :
      IsClosed ({U : Matrix n n ℂ | U ∈ Matrix.unitaryGroup n ℂ} : Set (Matrix n n ℂ)) := by
    have hct : Continuous fun U : Matrix n n ℂ => U * Uᴴ := by
      have hstar : Continuous fun U : Matrix n n ℂ => Uᴴ := by
        fun_prop
      exact continuous_id.mul hstar
    simpa [Matrix.mem_unitaryGroup_iff, Set.setOf_eq_eq_singleton] using
      isClosed_eq hct continuous_const
  have hbounded :
      Bornology.IsBounded
        ({U : Matrix n n ℂ | U ∈ Matrix.unitaryGroup n ℂ} : Set (Matrix n n ℂ)) := by
    refine
      (Metric.isBounded_closedBall (x := (0 : Matrix n n ℂ))
        (r := (Fintype.card n : ℝ))).subset ?_
    intro U hU
    simp only [Metric.mem_closedBall, dist_zero_right]
    rw [Matrix.frobenius_norm_def]
    have hsum :
        ∑ i : n, ∑ j : n, ‖U i j‖ ^ (2 : ℝ) ≤ ∑ i : n, ∑ j : n, (1 : ℝ) ^ (2 : ℝ) := by
      refine Finset.sum_le_sum ?_
      intro i hi
      refine Finset.sum_le_sum ?_
      intro j hj
      have hentry : ‖U i j‖ ≤ 1 := entry_norm_bound_of_unitary hU i j
      have hsq : ‖U i j‖ ^ (2 : ℝ) ≤ 1 := by
        have hmul := mul_le_mul hentry hentry (norm_nonneg _) (by positivity : (0 : ℝ) ≤ 1)
        simpa [pow_two] using hmul
      simpa [pow_two] using hsq
    have hsum' : ∑ i : n, ∑ j : n, ‖U i j‖ ^ (2 : ℝ) ≤ (Fintype.card n : ℝ) ^ 2 := by
      simpa [pow_two] using hsum
    have hcard_nonneg : 0 ≤ (Fintype.card n : ℝ) := by positivity
    have hsqrt : Real.sqrt (∑ i : n, ∑ j : n, ‖U i j‖ ^ (2 : ℝ)) ≤ (Fintype.card n : ℝ) := by
      exact (Real.sqrt_le_iff).2 ⟨hcard_nonneg, hsum'⟩
    rw [← Real.sqrt_eq_rpow]
    exact hsqrt
  letI : FiniteDimensional ℂ (Matrix n n ℂ) := inferInstance
  letI : ProperSpace (Matrix n n ℂ) :=
    @FiniteDimensional.proper ℂ inferInstance (Matrix n n ℂ)
      Matrix.frobeniusNormedAddCommGroup Matrix.frobeniusNormedSpace inferInstance inferInstance
  exact Metric.isCompact_of_isClosed_isBounded hclosed hbounded

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

private theorem tensorWithIdentity_phiStateGen_entry
    {d : Type u} [Fintype d] [DecidableEq d] [Nonempty d]
    (Φ : Channel d) (i j b e : d) :
    tensorWithIdentity d d Φ (phiStateGen d) (i, b) (j, e) =
      ((Fintype.card d : ℂ)⁻¹) * Φ (Matrix.single b e (1 : ℂ)) i j := by
  have hmat :
      (fun p q : d => phiStateGen d (p, b) (q, e)) =
        Matrix.single b e ((Fintype.card d : ℂ)⁻¹) := by
    ext p q
    by_cases hpb : p = b
    · by_cases hqe : q = e
      · subst hpb; subst hqe
        simp [phiStateGen_apply]
      · subst hpb
        have heq : e ≠ q := by
          intro h
          exact hqe h.symm
        simp [phiStateGen_apply, hqe, heq]
    · by_cases hqe : q = e
      · subst hqe
        have hbp : b ≠ p := by
          intro h
          exact hpb h.symm
        simp [phiStateGen_apply, hpb, hbp]
      · have hbp : b ≠ p := by
          intro h
          exact hpb h.symm
        have heq : e ≠ q := by
          intro h
          exact hqe h.symm
        simp [phiStateGen_apply, hpb, hbp, hqe, heq]
  have hsingle :
      Matrix.single b e ((Fintype.card d : ℂ)⁻¹) =
        ((Fintype.card d : ℂ)⁻¹) • Matrix.single b e (1 : ℂ) := by
    ext p q
    by_cases hpb : p = b
    · by_cases hqe : q = e
      · simp [hpb, hqe]
      · simp [Matrix.single_apply, hpb]
    · by_cases hqe : q = e
      · simp [Matrix.single_apply, hqe]
      · simp [Matrix.single_apply]
  change Φ (fun p q : d => phiStateGen d (p, b) (q, e)) i j =
    ((Fintype.card d : ℂ)⁻¹) * Φ (Matrix.single b e (1 : ℂ)) i j
  rw [hmat, hsingle, map_smul]
  simp

private theorem tensorWithIdentity_phiStateGen_ne_zero_of_ne_zero
    {d : Type u} [Fintype d] [DecidableEq d] [Nonempty d]
    {Φ : Channel d} (hΦ : Φ ≠ 0) :
    tensorWithIdentity d d Φ (phiStateGen d) ≠ 0 := by
  intro hzero
  have hcard_ne : ((Fintype.card d : ℂ)⁻¹) ≠ 0 := by
    have hcard : (Fintype.card d : ℂ) ≠ 0 := by
      positivity
    exact inv_ne_zero hcard
  have hsingle : ∀ b e : d, Φ (Matrix.single b e (1 : ℂ)) = 0 := by
    intro b e
    ext i j
    have hentry := congrArg (fun M : Matrix (d × d) (d × d) ℂ => M (i, b) (j, e)) hzero
    have hentry' :
        ((Fintype.card d : ℂ)⁻¹) * Φ (Matrix.single b e (1 : ℂ)) i j = 0 := by
      simpa
        [tensorWithIdentity_phiStateGen_entry (Φ := Φ) (i := i) (j := j) (b := b) (e := e)]
        using hentry
    exact (mul_eq_zero.mp hentry').resolve_left hcard_ne
  apply hΦ
  ext X i j
  have hsingle_smul :
      ∀ b e : d, Φ (Matrix.single b e (X b e)) = X b e • Φ (Matrix.single b e (1 : ℂ)) := by
    intro b e
    have hsingle' : Matrix.single b e (X b e) = X b e • Matrix.single b e (1 : ℂ) := by
      ext a c
      by_cases hab : a = b
      · by_cases hce : c = e
        · subst hab; subst hce
          simp
        · simp [Matrix.single_apply, hab]
      · simp [Matrix.single_apply]
    rw [hsingle', map_smul]
  have hdecomp : X = ∑ b : d, ∑ e : d, Matrix.single b e (X b e) := by
    simpa using Matrix.matrix_eq_sum_single X
  have hXzero : Φ X = 0 := by
    rw [hdecomp, map_sum]
    apply Finset.sum_eq_zero
    intro b hb
    rw [map_sum]
    apply Finset.sum_eq_zero
    intro e he
    rw [hsingle_smul, hsingle]
    simp
  simpa using congrArg (fun M : Matrix d d ℂ => M i j) hXzero

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
        tensorWithIdentity d d (transposeMap d) ρ.1 =
          ((Fintype.card d : ℂ)⁻¹) • swapMatrixGen d := by
      simpa [ρ] using transpose_phiStateGen_eq_swap d
    have hU : swapMatrixGen d * (swapMatrixGen d)ᴴ = 1 := by
      rw [swapMatrixGen_conjTranspose, swapMatrixGen_mul_self]
    have hswapNorm :
        traceNormOp (((Fintype.card d : ℂ)⁻¹) • swapMatrixGen d) = (Fintype.card d : ℝ) := by
      calc
        traceNormOp (((Fintype.card d : ℂ)⁻¹) • swapMatrixGen d)
          = traceNormOp ((((Fintype.card d : ℂ)⁻¹) • (1 : Matrix (d × d) (d × d) ℂ)) *
              swapMatrixGen d) := by
                congr 1
                symm
                calc
                  (((Fintype.card d : ℂ)⁻¹) • (1 : Matrix (d × d) (d × d) ℂ)) *
                      swapMatrixGen d =
                    ((Fintype.card d : ℂ)⁻¹) •
                      ((1 : Matrix (d × d) (d × d) ℂ) * swapMatrixGen d) :=
                    smul_mul_assoc ((Fintype.card d : ℂ)⁻¹)
                      (1 : Matrix (d × d) (d × d) ℂ) (swapMatrixGen d)
                  _ = ((Fintype.card d : ℂ)⁻¹) • swapMatrixGen d := by
                    rw [one_mul]
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
          simp [Matrix.diag, Matrix.mul_apply, Matrix.conjTranspose_apply, mul_comm]
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
          · simp [omegaVecGen, unitaryVecGen, c, mul_left_comm, mul_comm]
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
          · simp
          · intro y hy hyb
            have hby' : b ≠ y := by
              exact fun h => hyb h.symm
            have hby : (1 : Matrix d d ℂ) b y = 0 := by
              simp [hby']
            simp [hby, omegaVecGen]
          · simp
    _ = unitaryVecGen d U (a, b) := by
          simp [omegaVecGen, unitaryVecGen, mul_comm]

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
          · simp [Matrix.kroneckerMap_apply, Matrix.conjTranspose_apply]
          · intro y hy hyb
            have hby' : b ≠ y := by
              exact fun h => hyb h.symm
            simp [Matrix.kroneckerMap_apply, Matrix.conjTranspose_apply, hby']
          · simp
    _ = star (unitaryVecGen d U (a, b)) := by
      rw [Finset.sum_eq_single b]
      · simp [omegaVecGen, unitaryVecGen, mul_comm]
      · intro x hx hxb
        simp [omegaVecGen, hxb]
      · simp

private theorem vecMulVec_isDensityState_of_dotProduct_one
    {ι : Type u} [Fintype ι] [DecidableEq ι] (ψ : ι → ℂ)
    (hψ : ψ ⬝ᵥ star ψ = 1) :
    IsDensityState (Matrix.vecMulVec ψ (star ψ)) := by
  refine ⟨?_, ?_⟩
  · simpa using Matrix.posSemidef_vecMulVec_self_star ψ
  · rw [Matrix.trace_vecMulVec, hψ]

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
  have hρtr : Matrix.trace ρ = 1 := by
    change Matrix.trace (Matrix.vecMulVec ψ (star ψ)) = 1
    rw [Matrix.trace_vecMulVec, hψ]
  have hσtr : Matrix.trace σ = 1 := by
    change Matrix.trace (Matrix.vecMulVec φ (star φ)) = 1
    rw [Matrix.trace_vecMulVec, hφ]
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

private theorem partialTranspose_hermitian
    {d k : Type u} [Fintype d] [DecidableEq d] [Fintype k] [DecidableEq k]
    {X : Matrix (d × k) (d × k) ℂ} (hX : Matrix.IsHermitian X) :
    Matrix.IsHermitian (partialTransposeMap d k X) := by
  change (partialTransposeMap d k X)ᴴ = partialTransposeMap d k X
  ext i j
  rcases i with ⟨a, b⟩
  rcases j with ⟨c, e⟩
  change star (X (a, e) (c, b)) = X (c, b) (a, e)
  simpa [Matrix.conjTranspose_apply] using
    congrArg (fun M : Matrix (d × k) (d × k) ℂ => M (c, b) (a, e)) hX

private theorem tensorWithIdentity_hermitian_aux
    {d k : Type u} [Fintype d] [DecidableEq d] [Fintype k] [DecidableEq k]
    {Φ : Channel d} (hΦ : IsHermiticityPreserving Φ)
    {ρ : Matrix (d × k) (d × k) ℂ} (hρ : Matrix.IsHermitian ρ) :
    Matrix.IsHermitian (tensorWithIdentity d k Φ ρ) := by
  change (tensorWithIdentity d k Φ ρ)ᴴ = tensorWithIdentity d k Φ ρ
  ext i j
  rcases i with ⟨a, b⟩
  rcases j with ⟨c, e⟩
  let M : Matrix d d ℂ := fun p q => ρ (p, b) (q, e)
  have hM :
      Mᴴ = (fun p q : d => ρ (p, e) (q, b)) := by
    ext p q
    change star (ρ (q, b) (p, e)) = ρ (p, e) (q, b)
    simpa [Matrix.conjTranspose_apply] using
      congrArg (fun X : Matrix (d × k) (d × k) ℂ => X (p, e) (q, b)) hρ
  have hentry :
      Φ (fun p q : d => ρ (p, e) (q, b)) c a = star (Φ M a c) := by
    simpa [hM, Matrix.conjTranspose_apply] using
      congrArg (fun X : Matrix d d ℂ => X c a) (hΦ M)
  simpa [tensorWithIdentity, M, Matrix.conjTranspose_apply] using congrArg star hentry

private theorem transpose_comp_ne_zero_of_ne_zero
    {d : Type u} [Fintype d] [DecidableEq d]
    {Φ : Channel d} (hΦ : Φ ≠ 0) :
    (transposeMap d).comp Φ ≠ 0 := by
  intro hzero
  apply hΦ
  ext X i j
  have hX : transposeMap d (Φ X) = 0 := by
    simpa using congrArg (fun Ψ : Channel d => Ψ X) hzero
  have hij := congrArg (fun M : Matrix d d ℂ => M j i) hX
  simpa [transposeMap] using hij

private theorem hermitian_unitary_trace_real_le_traceNorm
    {n : Type u} [Fintype n] [DecidableEq n]
    {H U : Matrix n n ℂ} (hH : Matrix.IsHermitian H) (hU : U ∈ Matrix.unitaryGroup n ℂ) :
    Complex.re (Matrix.trace (U * H)) ≤ traceNormOp H := by
  let V : Matrix n n ℂ := hH.eigenvectorUnitary
  let D : Matrix n n ℂ := Matrix.diagonal (fun i => ((hH.eigenvalues i : ℝ) : ℂ))
  let W : Matrix n n ℂ := Vᴴ * U * V
  have hVmem : V ∈ Matrix.unitaryGroup n ℂ := hH.eigenvectorUnitary.property
  have hWmem : W ∈ Matrix.unitaryGroup n ℂ := by
    rw [Matrix.mem_unitaryGroup_iff']
    have hUu : Uᴴ * U = 1 := Matrix.mem_unitaryGroup_iff'.mp hU
    have hVu : V * Vᴴ = 1 := Matrix.mem_unitaryGroup_iff.mp hVmem
    have hVu' : Vᴴ * V = 1 := Matrix.mem_unitaryGroup_iff'.mp hVmem
    calc
      Wᴴ * W = Vᴴ * Uᴴ * V * (Vᴴ * U * V) := by simp [W, Matrix.mul_assoc]
      _ = Vᴴ * Uᴴ * (V * Vᴴ) * U * V := by simp [Matrix.mul_assoc]
      _ = Vᴴ * Uᴴ * U * V := by simp [hVu, Matrix.mul_assoc]
      _ = Vᴴ * V := by simp [hUu, Matrix.mul_assoc]
      _ = 1 := hVu'
  have htrace : Matrix.trace (U * H) = Matrix.trace (W * D) := by
    calc
      Matrix.trace (U * H) = Matrix.trace (U * (V * D * Vᴴ)) := by
        simpa [V, D, Unitary.conjStarAlgAut_apply, Matrix.mul_assoc] using
          congrArg (fun X => Matrix.trace (U * X)) hH.spectral_theorem
      _ = Matrix.trace ((U * V) * D * Vᴴ) := by
        simp [Matrix.mul_assoc]
      _ = Matrix.trace (Vᴴ * (U * V) * D) := by
        simpa [Matrix.mul_assoc] using Matrix.trace_mul_cycle (U * V) D Vᴴ
      _ = Matrix.trace (W * D) := by
        simp [W, Matrix.mul_assoc]
  have hdiag :
      Complex.re (Matrix.trace (W * D)) ≤ ∑ i, |hH.eigenvalues i| := by
    calc
      Complex.re (Matrix.trace (W * D)) = ∑ i, Complex.re ((W * D) i i) := by
        simp [Matrix.trace]
      _ ≤ ∑ i, |hH.eigenvalues i| := by
        apply Finset.sum_le_sum
        intro i hi
        have hentry : ‖W i i‖ ≤ 1 := by
          simpa using entry_norm_bound_of_unitary hWmem i i
        have habs : |Complex.re (W i i)| ≤ 1 := by
          exact le_trans (Complex.abs_re_le_norm (W i i)) hentry
        have hmuldiag : (W * D) i i = W i i * (((hH.eigenvalues i : ℝ) : ℂ)) := by
          rw [Matrix.mul_apply]
          rw [Finset.sum_eq_single i]
          · simp [D]
          · intro j hj hji
            simp [D, hji]
          · simp [D]
        rw [hmuldiag]
        by_cases hi0 : 0 ≤ hH.eigenvalues i
        · have hrei : Complex.re (W i i) ≤ 1 := (abs_le.mp (by simpa using habs)).2
          have hmul : Complex.re (W i i) * hH.eigenvalues i ≤ hH.eigenvalues i := by
            nlinarith
          simpa [Complex.mul_re, abs_of_nonneg hi0, mul_comm] using hmul
        · have hi0' : hH.eigenvalues i < 0 := lt_of_not_ge hi0
          have hrei : -1 ≤ Complex.re (W i i) := (abs_le.mp (by simpa using habs)).1
          have hmul : Complex.re (W i i) * hH.eigenvalues i ≤ -hH.eigenvalues i := by
            nlinarith
          simpa [Complex.mul_re, abs_of_neg hi0', mul_comm] using hmul
  calc
    Complex.re (Matrix.trace (U * H)) = Complex.re (Matrix.trace (W * D)) := by
      rw [htrace]
    _ ≤ ∑ i, |hH.eigenvalues i| := hdiag
    _ = traceNormOp H := by
      symm
      simpa using traceNormOp_hermitian_eq_sum_abs_eigenvalues hH

private theorem exists_unitary_trace_real_eq_traceNorm
    {n : Type u} [Fintype n] [DecidableEq n]
    {H : Matrix n n ℂ} (hH : Matrix.IsHermitian H) :
    ∃ U : Matrix n n ℂ, U ∈ Matrix.unitaryGroup n ℂ ∧
      Complex.re (Matrix.trace (U * H)) = traceNormOp H := by
  let V : Matrix n n ℂ := hH.eigenvectorUnitary
  let D : Matrix n n ℂ := Matrix.diagonal (fun i => ((hH.eigenvalues i : ℝ) : ℂ))
  let S : Matrix n n ℂ :=
    Matrix.diagonal (fun i => if 0 ≤ hH.eigenvalues i then (1 : ℂ) else -1)
  let U : Matrix n n ℂ := V * S * Vᴴ
  refine ⟨U, ?_, ?_⟩
  · have hVmem : V ∈ Matrix.unitaryGroup n ℂ := hH.eigenvectorUnitary.property
    have hVstar : Vᴴ ∈ Matrix.unitaryGroup n ℂ := by
      rw [Matrix.mem_unitaryGroup_iff]
      simpa [star_eq_conjTranspose] using Matrix.mem_unitaryGroup_iff'.mp hVmem
    have hS : S ∈ Matrix.unitaryGroup n ℂ := by
      rw [Matrix.mem_unitaryGroup_iff']
      ext i j
      by_cases hij : i = j
      · subst hij
        by_cases h : 0 ≤ hH.eigenvalues i <;> simp [S, h]
      · have hji : j ≠ i := fun h => hij h.symm
        simp [S, hij, hji]
    have hVS : V * S ∈ Matrix.unitaryGroup n ℂ := by
      exact @Submonoid.mul_mem (Matrix n n ℂ) _ (Matrix.unitaryGroup n ℂ) V S hVmem hS
    exact @Submonoid.mul_mem (Matrix n n ℂ) _ (Matrix.unitaryGroup n ℂ) (V * S) Vᴴ hVS hVstar
  · have hmul : (V * S * Vᴴ) * (V * D * Vᴴ) = V * (S * D) * Vᴴ := by
      have hVmem : V ∈ Matrix.unitaryGroup n ℂ := hH.eigenvectorUnitary.property
      have hVu' : Vᴴ * V = 1 := Matrix.mem_unitaryGroup_iff'.mp hVmem
      calc
        (V * S * Vᴴ) * (V * D * Vᴴ) = V * S * (Vᴴ * (V * D * Vᴴ)) := by
          simp [Matrix.mul_assoc]
        _ = V * S * (((Vᴴ * V) * D) * Vᴴ) := by
          simp [Matrix.mul_assoc]
        _ = V * S * (D * Vᴴ) := by
          simp [hVu', Matrix.mul_assoc]
        _ = V * (S * D) * Vᴴ := by
          simp [Matrix.mul_assoc]
    have htrace : Matrix.trace (U * H) = Matrix.trace (S * D) := by
      calc
        Matrix.trace (U * H) = Matrix.trace ((V * S * Vᴴ) * (V * D * Vᴴ)) := by
          simpa [U, V, D, Unitary.conjStarAlgAut_apply, Matrix.mul_assoc] using
            congrArg (fun X => Matrix.trace (U * X)) hH.spectral_theorem
        _ = Matrix.trace (V * (S * D) * Vᴴ) := by
          rw [hmul]
        _ = Matrix.trace (S * D) := by
          rw [Matrix.trace_mul_cycle V (S * D) Vᴴ]
          have hVmem : V ∈ Matrix.unitaryGroup n ℂ := hH.eigenvectorUnitary.property
          have hVu' : Vᴴ * V = 1 := Matrix.mem_unitaryGroup_iff'.mp hVmem
          simp [hVu']
    rw [htrace]
    calc
      Complex.re (Matrix.trace (S * D)) = ∑ i, Complex.re ((S * D) i i) := by
        simp [Matrix.trace]
      _ = ∑ i, |hH.eigenvalues i| := by
        apply Finset.sum_congr rfl
        intro i hi
        have hmuldiag : (S * D) i i = S i i * (((hH.eigenvalues i : ℝ) : ℂ)) := by
          rw [Matrix.mul_apply]
          rw [Finset.sum_eq_single i]
          · simp [D]
          · intro j hj hji
            simp [D, hji]
          · simp [D]
        rw [hmuldiag]
        by_cases h : 0 ≤ hH.eigenvalues i
        · simp [S, h, abs_of_nonneg h]
        · have h' : hH.eigenvalues i < 0 := lt_of_not_ge h
          simp [S, h, abs_of_neg h']
      _ = traceNormOp H := by
        symm
        simpa using traceNormOp_hermitian_eq_sum_abs_eigenvalues hH

/-- Finite-dimensional attainment of the left-hand diamond norm in the positive-gap argument.
    This compactness/maximizer step is background to the paper's main flow. -/
theorem exists_maximizing_state
    {d : Type u} [Fintype d] [DecidableEq d] [Nonempty d]
    (T : Channel d) (hT : IsQuantumChannel T) (hΦ : idMinus T ≠ 0) :
    ∃ ρ : DensityState (d × d),
      traceNormOp
          (tensorWithIdentity d d ((transposeMap d).comp (idMinus T)) ρ.1) =
        diamondOp ((transposeMap d).comp (idMinus T)) ∧
      tensorWithIdentity d d (idMinus T) ρ.1 ≠ 0 := by
  let Φ : Channel d := idMinus T
  let LΦ : Channel d := (transposeMap d).comp Φ
  let Ψ : Channel (d × d) := (partialTransposeMap d d).comp (tensorWithIdentity d d Φ)
  let unitarySet : Set (Matrix (d × d) (d × d) ℂ) :=
    {U : Matrix (d × d) (d × d) ℂ | U ∈ Matrix.unitaryGroup (d × d) ℂ}
  let densitySet : Set (Matrix (d × d) (d × d) ℂ) :=
    {ρ : Matrix (d × d) (d × d) ℂ | IsDensityState ρ}
  let f : Matrix (d × d) (d × d) ℂ × Matrix (d × d) (d × d) ℂ → ℝ :=
    fun p => Complex.re (Matrix.trace (p.1 * Ψ p.2))
  have hcompact :
      IsCompact (unitarySet ×ˢ densitySet) := by
    simpa [unitarySet, densitySet] using
      (isCompact_unitarySet (n := d × d)).prod (isCompact_densityStateSet (n := d × d))
  have hfcont : Continuous f := by
    have hΨcont : Continuous fun ρ : Matrix (d × d) (d × d) ℂ => Ψ ρ := by
      simpa [Ψ] using Ψ.continuous_of_finiteDimensional
    have hmul :
        Continuous fun p : Matrix (d × d) (d × d) ℂ × Matrix (d × d) (d × d) ℂ =>
          p.1 * Ψ p.2 := by
      exact continuous_fst.mul (hΨcont.comp continuous_snd)
    have htrace :
        Continuous fun p : Matrix (d × d) (d × d) ℂ × Matrix (d × d) (d × d) ℂ =>
          Matrix.trace (p.1 * Ψ p.2) := by
      simpa using ((Matrix.traceLinearMap (d × d) ℂ ℂ).continuous_of_finiteDimensional.comp hmul)
    exact Complex.continuous_re.comp htrace
  have hnonempty : (unitarySet ×ˢ densitySet).Nonempty := by
    refine ⟨(1, phiStateGen d), ?_⟩
    refine ⟨?_, ?_⟩
    · change (1 : Matrix (d × d) (d × d) ℂ) ∈ Matrix.unitaryGroup (d × d) ℂ
      rw [Matrix.mem_unitaryGroup_iff]
      simp
    · exact phiStateGen_isDensityState d
  obtain ⟨p0, hp0mem, hp0max⟩ :=
    hcompact.exists_isMaxOn hnonempty hfcont.continuousOn
  let U0 : Matrix (d × d) (d × d) ℂ := p0.1
  let ρ0m : Matrix (d × d) (d × d) ℂ := p0.2
  have hU0 : U0 ∈ Matrix.unitaryGroup (d × d) ℂ := hp0mem.1
  have hρ0m : IsDensityState ρ0m := hp0mem.2
  let ρ0 : DensityState (d × d) := ⟨ρ0m, hρ0m⟩
  have hrewrite0 :
      tensorWithIdentity d d LΦ ρ0.1 = Ψ ρ0.1 := by
    simpa [LΦ, Ψ, LinearMap.comp_apply] using
      congrArg (fun F : Channel (d × d) => F ρ0.1)
        (tensorWithIdentity_comp_transpose (d := d) (k := d) (Φ := Φ))
  have hpoint :
      ∀ ρ : DensityState (d × d), traceNormOp (tensorWithIdentity d d LΦ ρ.1) ≤ f p0 := by
    intro ρ
    have hΦherm : IsHermiticityPreserving Φ := by
      simpa [Φ] using idMinus_isHermiticityPreserving T hT
    have hXh : Matrix.IsHermitian (tensorWithIdentity d d Φ ρ.1) := by
      exact tensorWithIdentity_hermitian_aux (d := d) (k := d) hΦherm ρ.2.1.isHermitian
    have hYh : Matrix.IsHermitian (Ψ ρ.1) := by
      simpa [Ψ, LinearMap.comp_apply] using
        partialTranspose_hermitian (d := d) (k := d) hXh
    have hrewrite :
        tensorWithIdentity d d LΦ ρ.1 = Ψ ρ.1 := by
      simpa [LΦ, Ψ, LinearMap.comp_apply] using
        congrArg (fun F : Channel (d × d) => F ρ.1)
          (tensorWithIdentity_comp_transpose (d := d) (k := d) (Φ := Φ))
    obtain ⟨Uρ, hUρ, hUρeq⟩ := exists_unitary_trace_real_eq_traceNorm hYh
    have hpρmem : (Uρ, ρ.1) ∈ unitarySet ×ˢ densitySet := ⟨hUρ, ρ.2⟩
    calc
      traceNormOp (tensorWithIdentity d d LΦ ρ.1) = traceNormOp (Ψ ρ.1) := by
        rw [hrewrite]
      _ = f (Uρ, ρ.1) := by
        symm
        simpa [f] using hUρeq
      _ ≤ f p0 := by
        exact hp0max hpρmem
  have hdiamond_le : diamondOp LΦ ≤ f p0 := by
    refine diamond_le_of_pointwise_nonempty (d := d) (Φ := LΦ) (b := f p0) ?_
    intro ρ
    exact hpoint ρ
  have hΦherm : IsHermiticityPreserving Φ := by
    simpa [Φ] using idMinus_isHermiticityPreserving T hT
  have hX0h :
      Matrix.IsHermitian (tensorWithIdentity d d Φ ρ0.1) := by
    exact tensorWithIdentity_hermitian_aux (d := d) (k := d) hΦherm ρ0.2.1.isHermitian
  have hY0h : Matrix.IsHermitian (Ψ ρ0.1) := by
    simpa [Ψ, LinearMap.comp_apply] using
      partialTranspose_hermitian (d := d) (k := d) hX0h
  have hf_le_trace0 : f p0 ≤ traceNormOp (Ψ ρ0.1) := by
    simpa [f, U0, ρ0m, ρ0] using
      hermitian_unitary_trace_real_le_traceNorm hY0h hU0
  have htrace0_le :
      traceNormOp (Ψ ρ0.1) ≤ diamondOp LΦ := by
    rw [← hrewrite0]
    simpa [LΦ, diamondOp] using traceNorm_apply_le_diamond (d := d) (k := d) (Φ := LΦ) ρ0
  have hmax_eq :
      traceNormOp (tensorWithIdentity d d LΦ ρ0.1) = diamondOp LΦ := by
    apply le_antisymm
    · simpa [hrewrite0] using htrace0_le
    · calc
        diamondOp LΦ ≤ f p0 := hdiamond_le
        _ ≤ traceNormOp (Ψ ρ0.1) := hf_le_trace0
        _ = traceNormOp (tensorWithIdentity d d LΦ ρ0.1) := by
          rw [← hrewrite0]
  have hL_nonzero : LΦ ≠ 0 := by
    simpa [LΦ, Φ] using transpose_comp_ne_zero_of_ne_zero (d := d) hΦ
  let ρwit : DensityState (d × d) := ⟨phiStateGen d, phiStateGen_isDensityState d⟩
  have hwit_nonzero : tensorWithIdentity d d LΦ ρwit.1 ≠ 0 := by
    simpa [LΦ] using tensorWithIdentity_phiStateGen_ne_zero_of_ne_zero (d := d) hL_nonzero
  have hwit_pos : 0 < traceNormOp (tensorWithIdentity d d LΦ ρwit.1) := by
    have hne : traceNormOp (tensorWithIdentity d d LΦ ρwit.1) ≠ 0 := by
      intro hzero
      exact hwit_nonzero ((traceNormOp_eq_zero_iff).mp hzero)
    exact lt_of_le_of_ne (trNorm_nonneg _) (Ne.symm hne)
  have hdiamond_pos : 0 < diamondOp LΦ := by
    exact lt_of_lt_of_le hwit_pos
      (traceNorm_apply_le_diamond (d := d) (k := d) (Φ := LΦ) ρwit)
  have hρ0_nonzero : tensorWithIdentity d d Φ ρ0.1 ≠ 0 := by
    intro hzero
    have hLrho_zero : tensorWithIdentity d d LΦ ρ0.1 = 0 := by
      rw [hrewrite0]
      simp [Ψ, LinearMap.comp_apply, hzero]
    have htrace_zero : traceNormOp (tensorWithIdentity d d LΦ ρ0.1) = 0 := by
      exact (traceNormOp_eq_zero_iff).2 hLrho_zero
    have : diamondOp LΦ = 0 := by
      rw [← hmax_eq, htrace_zero]
    exact hdiamond_pos.ne' this
  refine ⟨ρ0, ?_, ?_⟩
  · simpa [LΦ] using hmax_eq
  · simpa [Φ] using hρ0_nonzero

/-- Background spectral form of a nonzero rank-two traceless Hermitian matrix. -/
theorem rank_two_traceless_hermitian_decomposition
    {d : Type u} [Fintype d] [Nonempty d]
    {X : Matrix (d × d) (d × d) ℂ} :
    X ≠ 0 →
    Matrix.IsHermitian X →
    Matrix.trace X = 0 →
    X.rank = 2 →
    ∃ c : ℂ, ∃ ψ φ : d × d → ℂ,
      c ≠ 0 ∧
      X = c • (Matrix.vecMulVec ψ (star ψ) - Matrix.vecMulVec φ (star φ)) := by
  classical
  intro hX0 hXh htr hr
  let _ := hX0
  let eig : d × d → ℝ := hXh.eigenvalues
  let S := {i : d × d // eig i ≠ 0}
  have hcardS : Fintype.card S = 2 := by
    have hrank : X.rank = Fintype.card S := by
      simpa [S, eig] using hXh.rank_eq_card_non_zero_eigs (A := X)
    exact hrank ▸ hr
  have hnat : Nat.card S = 2 := by
    rw [← Fintype.card_eq_nat_card]
    exact hcardS
  obtain ⟨iS, jS, hijS, hS_univ⟩ := Nat.card_eq_two_iff.mp hnat
  have hij : iS.1 ≠ jS.1 := by
    intro h
    exact hijS (Subtype.ext h)
  have hsupp : ∀ k : d × d, eig k ≠ 0 → k = iS.1 ∨ k = jS.1 := by
    intro k hk
    have hkS : (⟨k, hk⟩ : S) = iS ∨ (⟨k, hk⟩ : S) = jS := by
      have : (⟨k, hk⟩ : S) ∈ ({iS, jS} : Set S) := by
        rw [hS_univ]
        simp
      simpa [Set.mem_insert_iff, Set.mem_singleton_iff] using this
    exact hkS.elim
      (fun h => Or.inl (congrArg Subtype.val h))
      (fun h => Or.inr (congrArg Subtype.val h))
  have hsum_zero : ∑ k, eig k = 0 := by
    have htraceC : (∑ k, ((eig k : ℝ) : ℂ)) = 0 := by
      simpa [eig, hXh.trace_eq_sum_eigenvalues] using htr
    exact_mod_cast congrArg Complex.re htraceC
  have hsum_pair : ∑ k, eig k = eig iS.1 + eig jS.1 := by
    classical
    rw [Finset.sum_eq_add iS.1 jS.1 hij]
    · intro k hk hkij
      have hk0 : eig k = 0 := by
        by_cases hke : eig k = 0
        · exact hke
        · rcases hsupp k hke with hki | hkj
          · exact (hkij.1 hki).elim
          · exact (hkij.2 hkj).elim
      simp [hk0]
    · intro hi_not
      simp at hi_not
    · intro hj_not
      simp at hj_not
  have hpair : eig iS.1 + eig jS.1 = 0 := by
    simpa [hsum_pair] using hsum_zero
  have hj_eq : eig jS.1 = - eig iS.1 := by
    linarith
  let ψ : d × d → ℂ := ⇑(hXh.eigenvectorBasis iS.1)
  let φ : d × d → ℂ := ⇑(hXh.eigenvectorBasis jS.1)
  let c : ℂ := eig iS.1
  have hc : c ≠ 0 := by
    simpa [c, eig] using iS.2
  have hsingle (idx : d × d) :
      (hXh.eigenvectorUnitary : Matrix (d × d) (d × d) ℂ) * Matrix.single idx idx (1 : ℂ) *
          (star hXh.eigenvectorUnitary : Matrix (d × d) (d × d) ℂ)
        = Matrix.vecMulVec (⇑(hXh.eigenvectorBasis idx)) (star ⇑(hXh.eigenvectorBasis idx)) := by
    calc
      (hXh.eigenvectorUnitary : Matrix (d × d) (d × d) ℂ) * Matrix.single idx idx (1 : ℂ) *
          (star hXh.eigenvectorUnitary : Matrix (d × d) (d × d) ℂ)
        = (hXh.eigenvectorUnitary : Matrix (d × d) (d × d) ℂ) *
            Matrix.vecMulVec (Pi.single idx 1) (Pi.single idx 1) *
            (star hXh.eigenvectorUnitary : Matrix (d × d) (d × d) ℂ) := by
              rw [Matrix.single_eq_single_vecMulVec_single]
      _ = Matrix.vecMulVec ((hXh.eigenvectorUnitary : Matrix (d × d) (d × d) ℂ) *ᵥ Pi.single idx 1)
            (Pi.single idx 1) * (star hXh.eigenvectorUnitary : Matrix (d × d) (d × d) ℂ) := by
              rw [Matrix.mul_vecMulVec]
      _ = Matrix.vecMulVec ((hXh.eigenvectorUnitary : Matrix (d × d) (d × d) ℂ) *ᵥ Pi.single idx 1)
            ((Pi.single idx 1) ᵥ* (star hXh.eigenvectorUnitary : Matrix (d × d) (d × d) ℂ)) := by
              rw [Matrix.vecMulVec_mul]
      _ = Matrix.vecMulVec (⇑(hXh.eigenvectorBasis idx))
            ((Pi.single idx 1) ᵥ* (star hXh.eigenvectorUnitary : Matrix (d × d) (d × d) ℂ)) := by
              rw [hXh.eigenvectorUnitary_mulVec]
      _ = Matrix.vecMulVec (⇑(hXh.eigenvectorBasis idx)) (star ⇑(hXh.eigenvectorBasis idx)) := by
              rw [show
                (Pi.single idx 1) ᵥ* (star hXh.eigenvectorUnitary : Matrix (d × d) (d × d) ℂ) =
                  star ⇑(hXh.eigenvectorBasis idx) by
                ext b
                simp]
  have hi_single := hsingle iS.1
  have hj_single := hsingle jS.1
  have hD :
      Matrix.diagonal (fun k => ((eig k : ℝ) : ℂ)) =
        c • Matrix.single iS.1 iS.1 (1 : ℂ) + (-c) • Matrix.single jS.1 jS.1 (1 : ℂ) := by
    ext a b
    by_cases hab : a = b
    · subst b
      by_cases hai : a = iS.1
      · subst a
        have hji : jS.1 ≠ iS.1 := by
          exact fun h => hij h.symm
        have hnot : ¬ jS.1 = iS.1 := hji
        simp [c, eig, hnot]
      · by_cases haj : a = jS.1
        · subst a
          simp [c, eig, hj_eq, hij]
        · have hai' : iS.1 ≠ a := fun h => hai h.symm
          have haj' : jS.1 ≠ a := fun h => haj h.symm
          have ha0 : eig a = 0 := by
            by_cases hne : eig a = 0
            · exact hne
            · exfalso
              rcases hsupp a hne with h | h
              · exact hai h
              · exact haj h
          simp [hai', haj', c, ha0]
    · have hia : ¬ (iS.1 = a ∧ iS.1 = b) := by
        intro h
        exact hab (h.1.symm.trans h.2)
      have hja : ¬ (jS.1 = a ∧ jS.1 = b) := by
        intro h
        exact hab (h.1.symm.trans h.2)
      simp [hab, hia, hja]
  refine ⟨c, ψ, φ, hc, ?_⟩
  calc
    X = (hXh.eigenvectorUnitary : Matrix (d × d) (d × d) ℂ) *
          Matrix.diagonal (fun k => ((eig k : ℝ) : ℂ)) *
          (star hXh.eigenvectorUnitary : Matrix (d × d) (d × d) ℂ) := by
            simpa [eig, Unitary.conjStarAlgAut_apply] using hXh.spectral_theorem
    _ = (hXh.eigenvectorUnitary : Matrix (d × d) (d × d) ℂ) *
          (c • Matrix.single iS.1 iS.1 (1 : ℂ) + (-c) • Matrix.single jS.1 jS.1 (1 : ℂ)) *
          (star hXh.eigenvectorUnitary : Matrix (d × d) (d × d) ℂ) := by
            rw [hD]
    _ = ((hXh.eigenvectorUnitary : Matrix (d × d) (d × d) ℂ) *
            (c • Matrix.single iS.1 iS.1 (1 : ℂ)) *
            (star hXh.eigenvectorUnitary : Matrix (d × d) (d × d) ℂ)) +
          ((hXh.eigenvectorUnitary : Matrix (d × d) (d × d) ℂ) *
            ((-c) • Matrix.single jS.1 jS.1 (1 : ℂ)) *
            (star hXh.eigenvectorUnitary : Matrix (d × d) (d × d) ℂ)) := by
            simp [Matrix.mul_add, add_mul, Matrix.mul_assoc]
    _ = c • (((hXh.eigenvectorUnitary : Matrix (d × d) (d × d) ℂ) *
            Matrix.single iS.1 iS.1 (1 : ℂ) *
            (star hXh.eigenvectorUnitary : Matrix (d × d) (d × d) ℂ))) +
          (-c) • (((hXh.eigenvectorUnitary : Matrix (d × d) (d × d) ℂ) *
            Matrix.single jS.1 jS.1 (1 : ℂ) *
            (star hXh.eigenvectorUnitary : Matrix (d × d) (d × d) ℂ))) := by
            have h1 :
                (hXh.eigenvectorUnitary : Matrix (d × d) (d × d) ℂ) *
                    (c • Matrix.single iS.1 iS.1 (1 : ℂ)) *
                    (star hXh.eigenvectorUnitary : Matrix (d × d) (d × d) ℂ) =
                  c • ((hXh.eigenvectorUnitary : Matrix (d × d) (d × d) ℂ) *
                    Matrix.single iS.1 iS.1 (1 : ℂ) *
                    (star hXh.eigenvectorUnitary : Matrix (d × d) (d × d) ℂ)) := by
                      change ((hXh.eigenvectorUnitary : Matrix (d × d) (d × d) ℂ) *
                        (c • Matrix.single iS.1 iS.1 (1 : ℂ))) *
                        (star hXh.eigenvectorUnitary : Matrix (d × d) (d × d) ℂ) = _
                      rw [Matrix.mul_smul, Matrix.mul_assoc, Matrix.smul_mul]
                      simp [Matrix.mul_assoc]
            have h2 :
                (hXh.eigenvectorUnitary : Matrix (d × d) (d × d) ℂ) *
                    ((-c) • Matrix.single jS.1 jS.1 (1 : ℂ)) *
                    (star hXh.eigenvectorUnitary : Matrix (d × d) (d × d) ℂ) =
                  (-c) • ((hXh.eigenvectorUnitary : Matrix (d × d) (d × d) ℂ) *
                    Matrix.single jS.1 jS.1 (1 : ℂ) *
                    (star hXh.eigenvectorUnitary : Matrix (d × d) (d × d) ℂ)) := by
                      change ((hXh.eigenvectorUnitary : Matrix (d × d) (d × d) ℂ) *
                        ((-c) • Matrix.single jS.1 jS.1 (1 : ℂ))) *
                        (star hXh.eigenvectorUnitary : Matrix (d × d) (d × d) ℂ) = _
                      rw [Matrix.mul_smul, Matrix.mul_assoc, Matrix.smul_mul]
                      simp [Matrix.mul_assoc]
            rw [h1, h2]
    _ = c • Matrix.vecMulVec ψ (star ψ) + (-c) • Matrix.vecMulVec φ (star φ) := by
          rw [hi_single, hj_single]
    _ = c • (Matrix.vecMulVec ψ (star ψ) - Matrix.vecMulVec φ (star φ)) := by
          ext a b
          simp [sub_eq_add_neg]
          ring

/-- Vectorization of a square matrix as a pure state ket on `d × d`. -/
private def vecKetGen
    {d : Type u} [Fintype d] [DecidableEq d] (A : Matrix d d ℂ) : d × d → ℂ :=
  fun ij => A ij.1 ij.2

/-- The left partial trace of a vectorized rank-one operator is the transpose of the
    corresponding Gram matrix. -/
private theorem partialTraceLeft_vecMulVec_vecKetGen
    {d : Type u} [Fintype d] [DecidableEq d]
    (A B : Matrix d d ℂ) :
    partialTraceLeft d d (Matrix.vecMulVec (vecKetGen A) (star (vecKetGen B))) =
      (Bᴴ * A)ᵀ := by
  ext i j
  simp [partialTraceLeft, vecKetGen, Matrix.vecMulVec_apply, Matrix.mul_apply,
    Matrix.conjTranspose_apply, mul_comm]

/-- Equality of reduced states for vectorized pure states is equivalent to equality of the
    underlying Gram matrices. -/
private theorem partialTraceLeft_vecMulVec_eq_iff
    {d : Type u} [Fintype d] [DecidableEq d]
    {A B : Matrix d d ℂ} :
    partialTraceLeft d d (Matrix.vecMulVec (vecKetGen A) (star (vecKetGen A))) =
      partialTraceLeft d d (Matrix.vecMulVec (vecKetGen B) (star (vecKetGen B))) ↔
      Aᴴ * A = Bᴴ * B := by
  rw [partialTraceLeft_vecMulVec_vecKetGen (A := A) (B := A),
    partialTraceLeft_vecMulVec_vecKetGen (A := B) (B := B)]
  constructor
  · intro h
    exact Matrix.transpose_injective h
  · intro h
    exact congrArg Matrix.transpose h

/-- Matrix factorization form of Uhlmann's pure-state theorem. -/
private theorem uhlmann_matrix_factor
    {d : Type u} [Fintype d] [DecidableEq d]
    {A B : Matrix d d ℂ} (hGram : Aᴴ * A = Bᴴ * B) :
    ∃ U : Matrix d d ℂ, Uᴴ * U = 1 ∧ B = U * A := by
  let E := EuclideanSpace ℂ d
  let LA : E →ₗ[ℂ] E := Matrix.toEuclideanLin A
  let LB : E →ₗ[ℂ] E := Matrix.toEuclideanLin B
  have toEuclideanLin_mul :
      ∀ M N : Matrix d d ℂ,
        Matrix.toEuclideanLin (M * N) = Matrix.toEuclideanLin M ∘ₗ Matrix.toEuclideanLin N := by
    intro M N
    rw [Matrix.toEuclideanLin_eq_toLin_orthonormal]
    simpa [Matrix.toEuclideanLin_eq_toLin_orthonormal] using
      (Matrix.toLin_mul
        (EuclideanSpace.basisFun d ℂ).toBasis
        (EuclideanSpace.basisFun d ℂ).toBasis
        (EuclideanSpace.basisFun d ℂ).toBasis M N)
  have hAdj :
      LinearMap.adjoint LA ∘ₗ LA = LinearMap.adjoint LB ∘ₗ LB := by
    calc
      LinearMap.adjoint LA ∘ₗ LA = Matrix.toEuclideanLin (Aᴴ * A) := by
        rw [show LinearMap.adjoint LA = Matrix.toEuclideanLin Aᴴ by
              simp [LA, Matrix.toEuclideanLin_conjTranspose_eq_adjoint]]
        exact (toEuclideanLin_mul _ _).symm
      _ = Matrix.toEuclideanLin (Bᴴ * B) := by rw [hGram]
      _ = LinearMap.adjoint LB ∘ₗ LB := by
        rw [show LinearMap.adjoint LB = Matrix.toEuclideanLin Bᴴ by
              simp [LB, Matrix.toEuclideanLin_conjTranspose_eq_adjoint]]
        exact toEuclideanLin_mul _ _
  have hInner :
      ∀ x y : E, inner ℂ (LA x) (LA y) = inner ℂ (LB x) (LB y) := by
    intro x y
    calc
      inner ℂ (LA x) (LA y) = inner ℂ x ((LinearMap.adjoint LA ∘ₗ LA) y) := by
        simpa using (LinearMap.adjoint_inner_right (A := LA) (x := x) (y := LA y)).symm
      _ = inner ℂ x ((LinearMap.adjoint LB ∘ₗ LB) y) := by rw [hAdj]
      _ = inner ℂ (LB x) (LB y) := by
        simpa using (LinearMap.adjoint_inner_right (A := LB) (x := x) (y := LB y))
  have hKer : LinearMap.ker LA = LinearMap.ker LB := by
    ext x
    simp only [LinearMap.mem_ker]
    constructor <;> intro hx
    · have h0 : inner ℂ (LB x) (LB x) = 0 := by
        simpa [hx] using (hInner x x).symm
      exact (inner_self_eq_zero).1 h0
    · have h0 : inner ℂ (LA x) (LA x) = 0 := by
        simpa [hx] using hInner x x
      exact (inner_self_eq_zero).1 h0
  letI : Module.Free ℂ LA.range := Module.Free.of_divisionRing ℂ LA.range
  rcases LA.rangeRestrict.exists_rightInverse_of_surjective LA.range_rangeRestrict with ⟨g, hg⟩
  let Llin : LA.range →ₗ[ℂ] E := LB.comp g
  have hLinner : ∀ x y : LA.range, inner ℂ (Llin x) (Llin y) = inner ℂ x y := by
    intro x y
    have hx : LA (g x) = x := by
      exact congrArg Subtype.val (LinearMap.congr_fun hg x)
    have hy : LA (g y) = y := by
      exact congrArg Subtype.val (LinearMap.congr_fun hg y)
    calc
      inner ℂ (Llin x) (Llin y) = inner ℂ (LB (g x)) (LB (g y)) := by rfl
      _ = inner ℂ (LA (g x)) (LA (g y)) := by symm; exact hInner (g x) (g y)
      _ = inner ℂ x y := by simp [hx, hy]
  let L : LA.range →ₗᵢ[ℂ] E := by
    refine { toLinearMap := Llin, norm_map' := ?_ }
    intro x
    rw [norm_eq_sqrt_re_inner (𝕜 := ℂ) (x := Llin x),
      norm_eq_sqrt_re_inner (𝕜 := ℂ) (x := x), hLinner x x]
  let Ue : E →ₗᵢ[ℂ] E := L.extend
  have hL_apply (x : E) : L ⟨LA x, LinearMap.mem_range_self LA x⟩ = LB x := by
    have hxA : LA (g ⟨LA x, LinearMap.mem_range_self LA x⟩) = LA x := by
      exact congrArg Subtype.val (LinearMap.congr_fun hg ⟨LA x, LinearMap.mem_range_self LA x⟩)
    have hxKerA : g ⟨LA x, LinearMap.mem_range_self LA x⟩ - x ∈ LinearMap.ker LA := by
      simp [LinearMap.mem_ker, hxA]
    have hxKerB : g ⟨LA x, LinearMap.mem_range_self LA x⟩ - x ∈ LinearMap.ker LB := by
      simpa [hKer] using hxKerA
    have hxB : LB (g ⟨LA x, LinearMap.mem_range_self LA x⟩) = LB x := by
      apply sub_eq_zero.mp
      simpa [LinearMap.mem_ker, LinearMap.sub_apply] using hxKerB
    simpa [L, Llin] using hxB
  have hUeA : ∀ x : E, Ue (LA x) = LB x := by
    intro x
    let y : LA.range := ⟨LA x, LinearMap.mem_range_self LA x⟩
    calc
      Ue (LA x) = Ue y := by rfl
      _ = L y := by simpa [Ue] using (LinearIsometry.extend_apply (L := L) y)
      _ = LB x := by simpa [y] using hL_apply x
  have hUeAdjCLM :
      ContinuousLinearMap.adjoint Ue.toContinuousLinearMap ∘L Ue.toContinuousLinearMap = 1 := by
    exact (ContinuousLinearMap.norm_map_iff_adjoint_comp_self _).mp Ue.norm_map
  have hUeAdj : LinearMap.adjoint Ue.toLinearMap ∘ₗ Ue.toLinearMap = LinearMap.id := by
    simpa using congrArg ContinuousLinearMap.toLinearMap hUeAdjCLM
  let bStd := (EuclideanSpace.basisFun d ℂ).toBasis
  let U : Matrix d d ℂ := LinearMap.toMatrix bStd bStd Ue.toLinearMap
  have hU : Uᴴ * U = 1 := by
    have hmat := congrArg (LinearMap.toMatrix bStd bStd) hUeAdj
    rw [LinearMap.toMatrix_comp bStd bStd bStd, LinearMap.toMatrix_adjoint,
      LinearMap.toMatrix_id] at hmat
    simpa [U] using hmat
  have hAstd : LinearMap.toMatrix bStd bStd LA = A := by
    change (LinearMap.toMatrix bStd bStd) ((Matrix.toLin bStd bStd) A) = A
    exact LinearMap.toMatrix_toLin bStd bStd A
  have hBstd : LinearMap.toMatrix bStd bStd LB = B := by
    change (LinearMap.toMatrix bStd bStd) ((Matrix.toLin bStd bStd) B) = B
    exact LinearMap.toMatrix_toLin bStd bStd B
  have hBA : B = U * A := by
    have hcomp : Ue.toLinearMap ∘ₗ LA = LB := LinearMap.ext hUeA
    have hmat := congrArg (LinearMap.toMatrix bStd bStd) hcomp
    rw [LinearMap.toMatrix_comp bStd bStd bStd] at hmat
    simpa [U, hAstd, hBstd] using hmat.symm
  exact ⟨U, hU, hBA⟩

/-- Background pure-state form of Uhlmann's theorem. -/
theorem uhlmann_theorem_pure
    {d : Type u} [Fintype d] [DecidableEq d]
    (ψ φ : d × d → ℂ)
    (hred :
      partialTraceLeft d d (Matrix.vecMulVec ψ (star ψ)) =
        partialTraceLeft d d (Matrix.vecMulVec φ (star φ))) :
    ∃ U : Matrix d d ℂ, Uᴴ * U = 1 ∧
      φ = fun ij => ∑ a, U ij.1 a * ψ (a, ij.2) := by
  let A : Matrix d d ℂ := fun i j => ψ (i, j)
  let B : Matrix d d ℂ := fun i j => φ (i, j)
  have hredAB :
      partialTraceLeft d d (Matrix.vecMulVec (vecKetGen A) (star (vecKetGen A))) =
        partialTraceLeft d d (Matrix.vecMulVec (vecKetGen B) (star (vecKetGen B))) := by
    simpa [A, B, vecKetGen] using hred
  have hGram : Aᴴ * A = Bᴴ * B := (partialTraceLeft_vecMulVec_eq_iff.mp hredAB)
  obtain ⟨U, hU, hBA⟩ := uhlmann_matrix_factor hGram
  refine ⟨U, hU, ?_⟩
  funext ij
  have hij := congrArg (fun M : Matrix d d ℂ => M ij.1 ij.2) hBA
  simpa [A, B, Matrix.mul_apply] using hij

set_option maxHeartbeats 1000000 in
-- The spectral argument below needs a larger heartbeat budget.
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
    simp [map_smulₛₗ LinearMap.adjoint, hAadj, hBadj, sub_eq_add_neg]
  have hLapply : ∀ i : d, L (b i) = ω i • b i := by
    intro i
    have hAi : b i ∈ eigenspace A ((idx i).1.2) := by
      exact (Submodule.mem_inf.mp (hsub i)).1
    have hBi : b i ∈ eigenspace B ((idx i).1.1) := by
      exact (Submodule.mem_inf.mp (hsub i)).2
    rw [hLdecomp]
    simpa [ω, smul_smul, mul_assoc] using
      show A (b i) + Complex.I • B (b i) = ω i • b i by
        simp [mem_eigenspace_iff.mp hAi, mem_eigenspace_iff.mp hBi, add_smul, ω, smul_smul]
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
          add_smul, smul_smul]
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
      rw [show LinearMap.toMatrix b.toBasis b.toBasis L i i =
            LinearMap.toMatrixOrthonormal b L i i by rfl,
        LinearMap.toMatrixOrthonormal_apply_apply]
      simp [hLapply]
    · rw [show LinearMap.toMatrix b.toBasis b.toBasis L i j =
            LinearMap.toMatrixOrthonormal b L i j by rfl,
        LinearMap.toMatrixOrthonormal_apply_apply]
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
    have hinv0 :=
      ((tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).comp (tendsto_add_atTop_nat 1))
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
