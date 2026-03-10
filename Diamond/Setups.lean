import Mathlib
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.LinearAlgebra.Matrix.Hermitian
import Mathlib.Analysis.Matrix.Normed
import Mathlib.LinearAlgebra.Eigenspace.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Real.Sqrt
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Multiset.Basic

open scoped BigOperators
open scoped ComplexOrder
open scoped Kronecker
open scoped MatrixOrder
open scoped Matrix.Norms.Frobenius
open Matrix

namespace Diamond

universe u

noncomputable section

abbrev Operator (d : Type u) [Fintype d] [DecidableEq d] := Matrix d d ℂ

abbrev Channel (d : Type u) [Fintype d] [DecidableEq d] :=
  Operator d →ₗ[ℂ] Operator d

/-- Hilbert--Schmidt norm, realized by the Frobenius norm. -/
def hsNorm
    {m n : Type u} [Fintype m] [DecidableEq m] [Fintype n] [DecidableEq n]
    (X : Matrix m n ℂ) : ℝ :=
  ‖X‖

/-- Trace norm, realized as the sum of the singular values. -/
def traceNormOp
    {d : Type u} [Fintype d] [DecidableEq d] (X : Matrix d d ℂ) : ℝ :=
  ∑ i, Real.sqrt ((Matrix.isHermitian_conjTranspose_mul_self X).eigenvalues i)

abbrev hsNormOp
    {m n : Type u} [Fintype m] [DecidableEq m] [Fintype n] [DecidableEq n]
    (X : Matrix m n ℂ) : ℝ :=
  hsNorm X

def IsDensityState
    {d : Type u} [Fintype d] [DecidableEq d] (ρ : Matrix d d ℂ) : Prop :=
  Matrix.PosSemidef ρ ∧ Matrix.trace ρ = 1

abbrev DensityState (d : Type u) [Fintype d] [DecidableEq d] :=
  {ρ : Matrix d d ℂ // IsDensityState ρ}

/-- Fixed-input diamond norm, written as an infimum of uniform trace-norm bounds. -/
def diamondNorm
    {d : Type u} [Fintype d] [DecidableEq d] (Φ : Channel d) : ℝ :=
  sInf {C : ℝ | ∀ ρ : DensityState d, traceNormOp (Φ ρ.1) ≤ C}

def IsHermiticityPreserving
    {d : Type u} [Fintype d] [DecidableEq d] (Φ : Channel d) : Prop :=
  ∀ X, Φ Xᴴ = (Φ X)ᴴ

def IsQuantumChannel
    {d : Type u} [Fintype d] [DecidableEq d] (T : Channel d) : Prop :=
  (∀ X, Matrix.trace (T X) = Matrix.trace X) ∧ IsHermiticityPreserving T

def IsTraceAnnihilating
    {d : Type u} [Fintype d] [DecidableEq d] (Φ : Channel d) : Prop :=
  ∀ X, Matrix.trace (Φ X) = 0

/-- Transposition. -/
def transposeMap (d : Type u) [Fintype d] [DecidableEq d] : Channel d where
  toFun := fun X => Xᵀ
  map_add' := by
    intro X Y
    ext i j
    simp
  map_smul' := by
    intro c X
    ext i j
    simp

/-- Tensor a map on the left factor with the identity on the right factor. -/
def tensorWithIdentity
    (d k : Type u) [Fintype d] [DecidableEq d] [Fintype k] [DecidableEq k]
    (Φ : Channel d) : Channel (d × k) where
  toFun := fun X i j =>
    Φ (fun p q : d => X (p, i.2) (q, j.2)) i.1 j.1
  map_add' := by
    intro X Y
    ext i j
    let X' : Operator d := fun p q => X (p, i.2) (q, j.2)
    let Y' : Operator d := fun p q => Y (p, i.2) (q, j.2)
    change (Φ (X' + Y')) i.1 j.1 = (Φ X' + Φ Y') i.1 j.1
    rw [map_add]
  map_smul' := by
    intro c X
    ext i j
    let X' : Operator d := fun p q => X (p, i.2) (q, j.2)
    change (Φ (c • X')) i.1 j.1 = (c • Φ X') i.1 j.1
    rw [map_smul]

/-- Partial transpose on the left tensor factor. -/
def partialTransposeMap
    (d k : Type u) [Fintype d] [DecidableEq d] [Fintype k] [DecidableEq k] :
    Channel (d × k) where
  toFun := fun X i j => X (j.1, i.2) (i.1, j.2)
  map_add' := by
    intro X Y
    ext i j
    simp
  map_smul' := by
    intro c X
    ext i j
    simp

/-- Stabilization with a same-size ancilla. -/
abbrev diamondOp
    {d : Type u} [Fintype d] [DecidableEq d] (Φ : Channel d) : ℝ :=
  diamondNorm (tensorWithIdentity d d Φ)

theorem tensorWithIdentity_comp_transpose
    (d k : Type u) [Fintype d] [DecidableEq d] [Fintype k] [DecidableEq k]
    (Φ : Channel d) :
    tensorWithIdentity d k ((transposeMap d).comp Φ) =
      (partialTransposeMap d k).comp (tensorWithIdentity d k Φ) := by
  ext X i j
  simp [tensorWithIdentity, partialTransposeMap, transposeMap, LinearMap.comp_apply]

/-- Partial trace over the left factor. -/
def partialTraceLeft
    (d k : Type u) [Fintype d] [DecidableEq d] [Fintype k] [DecidableEq k]
    (X : Matrix (d × k) (d × k) ℂ) : Matrix k k ℂ :=
  fun i j => ∑ a, X (a, i) (a, j)

/-- The map `X ↦ X - Φ X`. -/
def idMinus
    {d : Type u} [Fintype d] [DecidableEq d] (Φ : Channel d) : Channel d where
  toFun := fun X => X - Φ X
  map_add' := by
    intro X Y
    ext i j
    simp [map_add, sub_eq_add_neg, add_assoc, add_left_comm, add_comm]
  map_smul' := by
    intro c X
    ext i j
    simp [map_smul, sub_eq_add_neg, mul_add]

/-- Unitary conjugation. -/
def adMap (d : Type u) [Fintype d] [DecidableEq d]
    (U : Matrix d d ℂ) : Channel d where
  toFun := fun X => U * X * Uᴴ
  map_add' := by
    intro X Y
    simp [Matrix.mul_add, Matrix.add_mul, Matrix.mul_assoc]
  map_smul' := by
    intro c X
    simp [Matrix.mul_assoc]

/-- The phase unitary used in the lower-bound example. -/
def Ud (d : ℕ) [Fact (1 < d)] : Matrix (Fin d) (Fin d) ℂ :=
  Matrix.diagonal fun i =>
    Complex.exp ((2 * Real.pi * Complex.I * (i : ℂ)) / (d : ℂ))

def Lambda (d : ℕ) [Fact (1 < d)] : Channel (Fin d) :=
  (transposeMap (Fin d)).comp (idMinus (adMap (Fin d) (Ud d)))

theorem idMinus_isHermiticityPreserving
    {d : Type u} [Fintype d] [DecidableEq d]
    (T : Channel d) (hT : IsQuantumChannel T) :
    IsHermiticityPreserving (idMinus T) := by
  intro X
  simp [idMinus, hT.2 X]

theorem idMinus_isTraceAnnihilating
    {d : Type u} [Fintype d] [DecidableEq d]
    (T : Channel d) (hT : IsQuantumChannel T) :
    IsTraceAnnihilating (idMinus T) := by
  intro X
  calc
    Matrix.trace (idMinus T X) = Matrix.trace X - Matrix.trace (T X) := by
      simp [idMinus]
    _ = 0 := by
      simp [hT.1 X]

lemma hsNorm_sq_eq_re_trace_conjTranspose_mul_self
    {m n : Type u} [Fintype m] [DecidableEq m] [Fintype n] [DecidableEq n]
    (X : Matrix m n ℂ) :
    hsNormOp X ^ 2 = Complex.re (Matrix.trace (Xᴴ * X)) := by
  change ‖X‖ ^ 2 = Complex.re (Matrix.trace (Xᴴ * X))
  rw [Matrix.frobenius_norm_def]
  have hnonneg : 0 ≤ (∑ i, ∑ j, ‖X i j‖ ^ (2 : ℝ) : ℝ) := by
    positivity
  have htrace :
      Complex.re (Matrix.trace (Xᴴ * X)) =
        ∑ x : n, ∑ y : m, ((X y x).re * (X y x).re + (X y x).im * (X y x).im) := by
    simp [Matrix.trace, Matrix.mul_apply, Complex.mul_re]
  calc
    ((∑ i, ∑ j, ‖X i j‖ ^ (2 : ℝ) : ℝ) ^ (1 / 2 : ℝ)) ^ 2
      = (∑ i, ∑ j, ‖X i j‖ ^ (2 : ℝ) : ℝ) := by
          rw [← Real.sqrt_eq_rpow (∑ i, ∑ j, ‖X i j‖ ^ (2 : ℝ) : ℝ)]
          simpa [pow_two] using Real.sq_sqrt hnonneg
    _ = ∑ i, ∑ j, ((X i j).re * (X i j).re + (X i j).im * (X i j).im) := by
          refine Finset.sum_congr rfl ?_
          intro i hi
          refine Finset.sum_congr rfl ?_
          intro j hj
          simpa [Complex.normSq_apply] using (Complex.normSq_eq_norm_sq (X i j)).symm
    _ = ∑ x : n, ∑ y : m, ((X y x).re * (X y x).re + (X y x).im * (X y x).im) := by
          simpa using
            (Finset.sum_comm
              (s := (Finset.univ : Finset m))
              (t := (Finset.univ : Finset n))
              (f := fun i j => ((X i j).re * (X i j).re + (X i j).im * (X i j).im)))
    _ = Complex.re (Matrix.trace (Xᴴ * X)) := by
          exact htrace.symm

lemma hermitian_re_trace_conjTranspose_mul_self_eq_sum_sq_eigenvalues
    {d : Type u} [Fintype d] [DecidableEq d]
    {A : Matrix d d ℂ} (hA : Matrix.IsHermitian A) :
    Complex.re (Matrix.trace (Aᴴ * A)) = ∑ i, (hA.eigenvalues i) ^ 2 := by
  let U : Matrix d d ℂ := hA.eigenvectorUnitary
  let D : Matrix d d ℂ := Matrix.diagonal (fun i => ((hA.eigenvalues i : ℝ) : ℂ))
  let e := Unitary.conjStarAlgAut ℂ (Matrix d d ℂ) (star hA.eigenvectorUnitary)
  have hdiag : e A = D := by
    simpa [e, D] using hA.conjStarAlgAut_star_eigenvectorUnitary
  have hmul : e (A * A) = e A * e A := by
    exact map_mul e A A
  have hDsq : D * D = (star hA.eigenvectorUnitary : Matrix d d ℂ) * (A * A) * U := by
    calc
      D * D = e (A * A) := by
        rw [← hdiag]
        simpa [hdiag] using hmul.symm
      _ = (star hA.eigenvectorUnitary : Matrix d d ℂ) * (A * A) * U := by
        simp [e, U, Unitary.conjStarAlgAut_apply]
  have hUright : U * (star hA.eigenvectorUnitary : Matrix d d ℂ) = 1 := by
    simpa [U] using (Matrix.mem_unitaryGroup_iff).1 hA.eigenvectorUnitary.property
  have hAA : Aᴴ * A = A * A := by
    simpa [hA.eq]
  calc
    Complex.re (Matrix.trace (Aᴴ * A)) = Complex.re (Matrix.trace (A * A)) := by
      rw [hAA]
    _ = Complex.re (Matrix.trace ((star hA.eigenvectorUnitary : Matrix d d ℂ) * (A * A) * U)) := by
          rw [Matrix.trace_mul_cycle (star hA.eigenvectorUnitary : Matrix d d ℂ) (A * A) U]
          simp [hUright]
    _ = Complex.re (Matrix.trace (D * D)) := by
          rw [hDsq]
    _ = ∑ i, (hA.eigenvalues i) ^ 2 := by
          simp [D, Matrix.trace, pow_two]

/-- Left multiplication by an isometry preserves the concrete trace norm. -/
theorem traceNormOp_mul_left_isometry
    {d : Type u} [Fintype d] [DecidableEq d]
    (U X : Matrix d d ℂ) (hU : Uᴴ * U = 1) :
    traceNormOp (U * X) = traceNormOp X := by
  have hmul : (U * X)ᴴ * (U * X) = Xᴴ * X := by
    calc
      (U * X)ᴴ * (U * X) = Xᴴ * (Uᴴ * U) * X := by
        simp [Matrix.conjTranspose_mul, Matrix.mul_assoc]
      _ = Xᴴ * X := by
        simp [hU]
  dsimp [traceNormOp]
  have hEig :
      (Matrix.isHermitian_conjTranspose_mul_self (U * X)).eigenvalues =
        (Matrix.isHermitian_conjTranspose_mul_self X).eigenvalues := by
    apply
      (Matrix.IsHermitian.eigenvalues_eq_eigenvalues_iff
        (Matrix.isHermitian_conjTranspose_mul_self (U * X))
        (Matrix.isHermitian_conjTranspose_mul_self X)).2
    exact congrArg Matrix.charpoly hmul
  rw [hEig]

/-- Trace norm of a diagonal matrix is the sum of the absolute values of its diagonal entries. -/
theorem traceNormOp_diagonal
    {d : Type u} [Fintype d] [DecidableEq d] (z : d → ℂ) :
    traceNormOp (Matrix.diagonal z) = ∑ i, ‖z i‖ := by
  let hDiag :
      Matrix.IsHermitian
        (Matrix.diagonal fun i => ((Complex.normSq (z i) : ℂ))) :=
    Matrix.isHermitian_diagonal_of_self_adjoint
      (fun i => ((Complex.normSq (z i) : ℂ))) (by
        ext i
        simp)
  have hmat :
      (Matrix.diagonal z)ᴴ * Matrix.diagonal z =
        Matrix.diagonal fun i => ((Complex.normSq (z i) : ℂ)) := by
    ext i j
    by_cases hij : i = j
    · subst hij
      simp [Complex.normSq_eq_conj_mul_self]
    · simp [hij]
  have hEig :
      (Matrix.isHermitian_conjTranspose_mul_self (Matrix.diagonal z)).eigenvalues =
        hDiag.eigenvalues := by
    apply
      (Matrix.IsHermitian.eigenvalues_eq_eigenvalues_iff
        (Matrix.isHermitian_conjTranspose_mul_self (Matrix.diagonal z))
        hDiag).2
    exact congrArg Matrix.charpoly hmat
  dsimp [traceNormOp]
  rw [hEig]
  have hmultiset :
      Multiset.map hDiag.eigenvalues Finset.univ.val =
        Multiset.map (fun i => Complex.normSq (z i)) Finset.univ.val := by
    have hroots :
        Multiset.map Complex.re
            ((Matrix.diagonal fun i => ((Complex.normSq (z i) : ℂ))).charpoly.roots) =
          Multiset.map (fun i => Complex.normSq (z i)) Finset.univ.val := by
      rw [show
            (Matrix.diagonal fun i => ((Complex.normSq (z i) : ℂ))).charpoly.roots =
              Multiset.map (fun i => ((Complex.normSq (z i) : ℂ))) Finset.univ.val by
            simpa [Matrix.charpoly_diagonal] using
              (Polynomial.roots_multiset_prod_X_sub_C
                (s := Multiset.map
                  (fun i => ((Complex.normSq (z i) : ℂ))) Finset.univ.val))]
      simp
    rw [Matrix.IsHermitian.roots_charpoly_eq_eigenvalues hDiag] at hroots
    simpa [Multiset.map_map, Function.comp_def] using hroots
  have hsqrt := congrArg (Multiset.map Real.sqrt) hmultiset
  have hsum :
      ∑ i, Real.sqrt (hDiag.eigenvalues i) =
        ∑ i, Real.sqrt (Complex.normSq (z i)) := by
    simpa [Multiset.map_map] using congrArg Multiset.sum hsqrt
  simpa [RCLike.sqrt_normSq_eq_norm] using hsum

/-- The concrete trace norm is invariant under conjugate transpose. -/
theorem traceNormOp_conjTranspose
    {d : Type u} [Fintype d] [DecidableEq d] (X : Matrix d d ℂ) :
    traceNormOp Xᴴ = traceNormOp X := by
  dsimp [traceNormOp]
  have hEig :
      (Matrix.isHermitian_conjTranspose_mul_self Xᴴ).eigenvalues =
        (Matrix.isHermitian_conjTranspose_mul_self X).eigenvalues := by
    apply
      (Matrix.IsHermitian.eigenvalues_eq_eigenvalues_iff
        (Matrix.isHermitian_conjTranspose_mul_self Xᴴ)
        (Matrix.isHermitian_conjTranspose_mul_self X)).2
    simpa using Matrix.charpoly_mul_comm X Xᴴ
  rw [hEig]

/-- Right multiplication by an isometry preserves the concrete trace norm. -/
theorem traceNormOp_mul_right_isometry
    {d : Type u} [Fintype d] [DecidableEq d]
    (X U : Matrix d d ℂ) (hU : U * Uᴴ = 1) :
    traceNormOp (X * U) = traceNormOp X := by
  have hU' : (Uᴴ)ᴴ * Uᴴ = 1 := by
    simpa using hU
  calc
    traceNormOp (X * U) = traceNormOp ((X * U)ᴴ) := by
      symm
      exact traceNormOp_conjTranspose (X := X * U)
    _ = traceNormOp (Uᴴ * Xᴴ) := by
      rw [Matrix.conjTranspose_mul]
    _ = traceNormOp Xᴴ := by
      exact traceNormOp_mul_left_isometry (U := Uᴴ) (X := Xᴴ) hU'
    _ = traceNormOp X := by
      exact traceNormOp_conjTranspose (X := X)

/-- For Hermitian matrices, the concrete trace norm is the sum of the absolute eigenvalues. -/
theorem traceNormOp_hermitian_eq_sum_abs_eigenvalues
    {d : Type u} [Fintype d] [DecidableEq d]
    {A : Matrix d d ℂ} (hA : Matrix.IsHermitian A) :
    traceNormOp A = ∑ i, |hA.eigenvalues i| := by
  let U : Matrix d d ℂ := hA.eigenvectorUnitary
  let Ustar : Matrix d d ℂ := star hA.eigenvectorUnitary
  let D : Matrix d d ℂ := Matrix.diagonal (fun i => ((hA.eigenvalues i : ℝ) : ℂ))
  have hU_left : Uᴴ * U = 1 := by
    exact (Matrix.mem_unitaryGroup_iff').1 hA.eigenvectorUnitary.property
  have hUstar_right : Ustar * Ustarᴴ = 1 := by
    exact (Matrix.mem_unitaryGroup_iff).1 (star hA.eigenvectorUnitary).property
  calc
    traceNormOp A = traceNormOp (U * (D * Ustar)) := by
      simpa [Unitary.conjStarAlgAut_apply, U, Ustar, D, Matrix.mul_assoc] using
        congrArg traceNormOp hA.spectral_theorem
    _ = traceNormOp (D * Ustar) := by
      exact traceNormOp_mul_left_isometry (U := U) (X := D * Ustar) hU_left
    _ = traceNormOp D := by
      exact traceNormOp_mul_right_isometry (X := D) (U := Ustar) hUstar_right
    _ = ∑ i, |hA.eigenvalues i| := by
      simp [D, traceNormOp_diagonal]

/-- Lemma 1: For traceless Hermitian `X`, `‖X‖₂ ≤ (1 / √2) ‖X‖₁`. -/
theorem lemma1
    {d : Type u} [Fintype d] [DecidableEq d]
    {X : Matrix d d ℂ} (hHerm : Matrix.IsHermitian X) (hTrace : Matrix.trace X = 0) :
    hsNormOp X ≤ (1 / Real.sqrt 2) * traceNormOp X := by
  let p : d → ℝ := fun i => max (hHerm.eigenvalues i) 0
  let q : d → ℝ := fun i => max (-hHerm.eigenvalues i) 0
  have hp_nonneg : ∀ i, 0 ≤ p i := by
    intro i
    simp [p]
  have hq_nonneg : ∀ i, 0 ≤ q i := by
    intro i
    simp [q]
  have habs : ∀ i, |hHerm.eigenvalues i| = p i + q i := by
    intro i
    by_cases hi : 0 ≤ hHerm.eigenvalues i
    · simp [p, q, hi, abs_of_nonneg hi]
    · have hi' : hHerm.eigenvalues i < 0 := lt_of_not_ge hi
      simp [p, q, hi'.le, abs_of_neg hi']
  have hsub : ∀ i, hHerm.eigenvalues i = p i - q i := by
    intro i
    by_cases hi : 0 ≤ hHerm.eigenvalues i
    · simp [p, q, hi]
    · have hi' : hHerm.eigenvalues i < 0 := lt_of_not_ge hi
      simp [p, q, hi'.le]
  have hsq : ∀ i, (hHerm.eigenvalues i) ^ 2 = (p i) ^ 2 + (q i) ^ 2 := by
    intro i
    by_cases hi : 0 ≤ hHerm.eigenvalues i
    · simp [p, q, hi, pow_two]
    · have hi' : hHerm.eigenvalues i < 0 := lt_of_not_ge hi
      simp [p, q, hi'.le, pow_two]
  have hsum_zero : ∑ i, hHerm.eigenvalues i = 0 := by
    have htraceC : (∑ i, ((hHerm.eigenvalues i : ℝ) : ℂ)) = 0 := by
      simpa [hHerm.trace_eq_sum_eigenvalues] using hTrace
    exact_mod_cast congrArg Complex.re htraceC
  have hpq : ∑ i, p i = ∑ i, q i := by
    have hsum_sub : ∑ i, (p i - q i) = 0 := by
      simpa [hsub] using hsum_zero
    rw [Finset.sum_sub_distrib] at hsum_sub
    linarith
  have hsumsq_le : ∑ i, (hHerm.eigenvalues i) ^ 2 ≤ 2 * (∑ i, p i) ^ 2 := by
    calc
      ∑ i, (hHerm.eigenvalues i) ^ 2 = ∑ i, (p i) ^ 2 + ∑ i, (q i) ^ 2 := by
        simp [hsq, Finset.sum_add_distrib]
      _ ≤ (∑ i, p i) ^ 2 + (∑ i, q i) ^ 2 := by
        gcongr
        · exact Finset.sum_sq_le_sq_sum_of_nonneg (fun i _ => hp_nonneg i)
        · exact Finset.sum_sq_le_sq_sum_of_nonneg (fun i _ => hq_nonneg i)
      _ = 2 * (∑ i, p i) ^ 2 := by
        rw [hpq]
        ring
  have htraceNorm :
      (∑ i, |hHerm.eigenvalues i|) = 2 * ∑ i, p i := by
    calc
      (∑ i, |hHerm.eigenvalues i|) = ∑ i, (p i + q i) := by
        simp [habs]
      _ = ∑ i, p i + ∑ i, q i := by
        rw [Finset.sum_add_distrib]
      _ = 2 * ∑ i, p i := by
        rw [hpq]
        ring
  have hsqrt2_ne : Real.sqrt 2 ≠ 0 := by
    positivity
  have hrhs :
      ((1 / Real.sqrt 2) * (2 * ∑ i, p i)) ^ 2 = 2 * (∑ i, p i) ^ 2 := by
    field_simp [pow_two, hsqrt2_ne]
    nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 2 by positivity)]
  have hsqineq : hsNormOp X ^ 2 ≤ ((1 / Real.sqrt 2) * (∑ i, |hHerm.eigenvalues i|)) ^ 2 := by
    rw [hsNorm_sq_eq_re_trace_conjTranspose_mul_self,
      hermitian_re_trace_conjTranspose_mul_self_eq_sum_sq_eigenvalues hHerm]
    rw [htraceNorm, hrhs]
    exact hsumsq_le
  have hleft : 0 ≤ hsNormOp X := norm_nonneg _
  have hright : 0 ≤ (1 / Real.sqrt 2) * (∑ i, |hHerm.eigenvalues i|) := by
    positivity
  have hle_abs : hsNormOp X ≤ |(1 / Real.sqrt 2) * (∑ i, |hHerm.eigenvalues i|)| := by
    simpa [abs_of_nonneg hleft] using (sq_le_sq.mp hsqineq)
  calc
    hsNormOp X ≤ |(1 / Real.sqrt 2) * (∑ i, |hHerm.eigenvalues i|)| := hle_abs
    _ = (1 / Real.sqrt 2) * (∑ i, |hHerm.eigenvalues i|) := abs_of_nonneg hright
    _ = (1 / Real.sqrt 2) * traceNormOp X := by
      rw [traceNormOp_hermitian_eq_sum_abs_eigenvalues hHerm]

/-- Lemma 2: `‖Y‖₁ ≤ √N ‖Y‖₂` on an `N`-dimensional space. -/
theorem lemma2
    {ι : Type u} [Fintype ι] [DecidableEq ι]
    {Y : Matrix ι ι ℂ} :
    traceNormOp Y ≤ Real.sqrt (Fintype.card ι : ℝ) * hsNormOp Y := by
  let μ : ι → ℝ := (Matrix.isHermitian_conjTranspose_mul_self Y).eigenvalues
  have hμ_nonneg : ∀ i, 0 ≤ μ i := by
    intro i
    exact Matrix.eigenvalues_conjTranspose_mul_self_nonneg Y i
  have hsum_sq :
      (∑ i, Real.sqrt (μ i)) ^ 2 ≤ (Fintype.card ι : ℝ) * ∑ i, μ i := by
    calc
      (∑ i, Real.sqrt (μ i)) ^ 2 ≤
          (Fintype.card ι : ℝ) * ∑ i, (Real.sqrt (μ i)) ^ 2 := by
            simpa using
              sq_sum_le_card_mul_sum_sq
                (s := (Finset.univ : Finset ι))
                (f := fun i => Real.sqrt (μ i))
      _ = (Fintype.card ι : ℝ) * ∑ i, μ i := by
            refine congrArg ((Fintype.card ι : ℝ) * ·) ?_
            refine Finset.sum_congr rfl ?_
            intro i hi
            exact Real.sq_sqrt (hμ_nonneg i)
  have hnorm_sq : hsNormOp Y ^ 2 = ∑ i, μ i := by
    calc
      hsNormOp Y ^ 2 = Complex.re (Matrix.trace (Yᴴ * Y)) := by
        exact hsNorm_sq_eq_re_trace_conjTranspose_mul_self Y
      _ = ∑ i, μ i := by
        rw [(Matrix.isHermitian_conjTranspose_mul_self Y).trace_eq_sum_eigenvalues]
        simp [μ]
  have hrhs_sq :
      (Real.sqrt (Fintype.card ι : ℝ) * hsNormOp Y) ^ 2 =
        (Fintype.card ι : ℝ) * ∑ i, μ i := by
    calc
      (Real.sqrt (Fintype.card ι : ℝ) * hsNormOp Y) ^ 2
        = (Real.sqrt (Fintype.card ι : ℝ)) ^ 2 * (hsNormOp Y) ^ 2 := by
            ring
      _ = (Fintype.card ι : ℝ) * ∑ i, μ i := by
            rw [Real.sq_sqrt (by positivity), hnorm_sq]
  have hsqineq :
      (∑ i, Real.sqrt (μ i)) ^ 2 ≤ (Real.sqrt (Fintype.card ι : ℝ) * hsNormOp Y) ^ 2 := by
    rw [hrhs_sq]
    exact hsum_sq
  have hleft : 0 ≤ ∑ i, Real.sqrt (μ i) := by
    exact Finset.sum_nonneg (fun i _ => Real.sqrt_nonneg _)
  have hright : 0 ≤ Real.sqrt (Fintype.card ι : ℝ) * hsNormOp Y := by
    exact mul_nonneg (Real.sqrt_nonneg _) (norm_nonneg _)
  have hle_abs : ∑ i, Real.sqrt (μ i) ≤ |Real.sqrt (Fintype.card ι : ℝ) * hsNormOp Y| := by
    simpa [abs_of_nonneg hleft] using (sq_le_sq.mp hsqineq)
  calc
    traceNormOp Y = ∑ i, Real.sqrt (μ i) := by
      rfl
    _ ≤ |Real.sqrt (Fintype.card ι : ℝ) * hsNormOp Y| := hle_abs
    _ = Real.sqrt (Fintype.card ι : ℝ) * hsNormOp Y := abs_of_nonneg hright

/-- Lemma 3: partial transpose preserves the Hilbert--Schmidt norm. -/
theorem lemma3
    {d k : Type u} [Fintype d] [DecidableEq d] [Fintype k] [DecidableEq k]
    (X : Matrix (d × k) (d × k) ℂ) :
    hsNormOp (partialTransposeMap d k X) = hsNormOp X := by
  change ‖partialTransposeMap d k X‖ = ‖X‖
  let e : (d × k) × (d × k) ≃ (d × k) × (d × k) :=
    { toFun := fun p => ((p.2.1, p.1.2), (p.1.1, p.2.2))
      invFun := fun p => ((p.2.1, p.1.2), (p.1.1, p.2.2))
      left_inv := by
        intro p
        aesop
      right_inv := by
        intro p
        aesop }
  have hEq :
      (∑ p : (d × k) × (d × k), ‖X (e p).1 (e p).2‖ ^ (2 : ℝ)) =
        ∑ p : (d × k) × (d × k), ‖X p.1 p.2‖ ^ (2 : ℝ) := by
    exact Equiv.sum_comp e (g := fun p => ‖X p.1 p.2‖ ^ (2 : ℝ))
  calc
    ‖partialTransposeMap d k X‖
      = (∑ p : (d × k) × (d × k), ‖X (e p).1 (e p).2‖ ^ (2 : ℝ)) ^ (1 / 2 : ℝ) := by
          simp [partialTransposeMap, Matrix.frobenius_norm_def, e, Fintype.sum_prod_type]
    _ = (∑ p : (d × k) × (d × k), ‖X p.1 p.2‖ ^ (2 : ℝ)) ^ (1 / 2 : ℝ) := by
          rw [hEq]
    _ = ‖X‖ := by
          simp [Matrix.frobenius_norm_def, Fintype.sum_prod_type]

axiom diamond_le_of_pointwise
    {d : Type u} [Fintype d] [DecidableEq d] [Nonempty d]
    (Φ : Channel d) (C : ℝ) :
    (∀ ρ : Matrix d d ℂ, IsDensityState ρ → traceNormOp (Φ ρ) ≤ C) →
      diamondNorm Φ ≤ C

axiom traceNorm_apply_le_diamond
    {d : Type u} [Fintype d] [DecidableEq d]
    (Φ : Channel d) (ρ : Matrix d d ℂ) (hρ : IsDensityState ρ) :
    traceNormOp (Φ ρ) ≤ diamondNorm Φ

axiom lemma_transpose_diamond
    (d : Type u) [Fintype d] [DecidableEq d] [Nonempty d] :
    diamondOp (transposeMap d) = (Fintype.card d : ℝ)

/-- Positive semidefinite matrices have trace norm equal to the real trace. -/
theorem traceNormOp_posSemidef_eq_trace
    {d : Type u} [Fintype d] [DecidableEq d]
    {A : Matrix d d ℂ} (hA : A.PosSemidef) :
    traceNormOp A = Complex.re (Matrix.trace A) := by
  calc
    traceNormOp A = ∑ i, |hA.isHermitian.eigenvalues i| := by
      simpa using traceNormOp_hermitian_eq_sum_abs_eigenvalues hA.isHermitian
    _ = ∑ i, hA.isHermitian.eigenvalues i := by
      refine Finset.sum_congr rfl ?_
      intro i hi
      exact abs_of_nonneg (hA.eigenvalues_nonneg i)
    _ = Complex.re (Matrix.trace A) := by
      rw [hA.isHermitian.trace_eq_sum_eigenvalues]
      simp

/-- Density states have concrete trace norm `1`. -/
theorem traceNormOp_density_eq_one
    {d : Type u} [Fintype d] [DecidableEq d]
    {ρ : Matrix d d ℂ} (hρ : IsDensityState ρ) :
    traceNormOp ρ = 1 := by
  rw [traceNormOp_posSemidef_eq_trace hρ.1, hρ.2]
  simp

/-- The concrete trace distance between density states is at most `2`. -/
theorem traceNormOp_sub_density_le_two
    {d : Type u} [Fintype d] [DecidableEq d]
    {ρ σ : Matrix d d ℂ} (hρ : IsDensityState ρ) (hσ : IsDensityState σ) :
    traceNormOp (ρ - σ) ≤ 2 := by
  let X : Matrix d d ℂ := ρ - σ
  have hX : Matrix.IsHermitian X := hρ.1.isHermitian.sub hσ.1.isHermitian
  let U : Matrix d d ℂ := hX.eigenvectorUnitary
  let Ustar : Matrix d d ℂ := star hX.eigenvectorUnitary
  let D : Matrix d d ℂ := Matrix.diagonal (fun i => ((hX.eigenvalues i : ℝ) : ℂ))
  let P : Matrix d d ℂ := Ustar * ρ * U
  let Q : Matrix d d ℂ := Ustar * σ * U
  have hU_right : U * Ustar = 1 := by
    exact (Matrix.mem_unitaryGroup_iff).1 hX.eigenvectorUnitary.property
  have hP_pos : P.PosSemidef := by
    simpa [P, U, Ustar, Matrix.mul_assoc] using hρ.1.conjTranspose_mul_mul_same U
  have hQ_pos : Q.PosSemidef := by
    simpa [Q, U, Ustar, Matrix.mul_assoc] using hσ.1.conjTranspose_mul_mul_same U
  have hP_trace : Matrix.trace P = 1 := by
    calc
      Matrix.trace P = Matrix.trace ((U * Ustar) * ρ) := by
        dsimp [P]
        rw [Matrix.trace_mul_cycle Ustar ρ U, Matrix.mul_assoc]
      _ = Matrix.trace ρ := by
        rw [hU_right, one_mul]
      _ = 1 := hρ.2
  have hQ_trace : Matrix.trace Q = 1 := by
    calc
      Matrix.trace Q = Matrix.trace ((U * Ustar) * σ) := by
        dsimp [Q]
        rw [Matrix.trace_mul_cycle Ustar σ U, Matrix.mul_assoc]
      _ = Matrix.trace σ := by
        rw [hU_right, one_mul]
      _ = 1 := hσ.2
  have hdiag :
      P - Q = D := by
    simpa [X, U, Ustar, D, P, Q, Unitary.conjStarAlgAut_apply, Matrix.mul_assoc,
      Matrix.mul_sub, Matrix.sub_mul] using hX.conjStarAlgAut_star_eigenvectorUnitary
  have hbound :
      ∀ i : d, |hX.eigenvalues i| ≤ Complex.re (P i i) + Complex.re (Q i i) := by
    intro i
    have hPiC : 0 ≤ P i i := hP_pos.diag_nonneg
    have hQiC : 0 ≤ Q i i := hQ_pos.diag_nonneg
    have hPi : 0 ≤ Complex.re (P i i) := by
      exact (RCLike.nonneg_iff.mp hPiC).1
    have hQi : 0 ≤ Complex.re (Q i i) := by
      exact (RCLike.nonneg_iff.mp hQiC).1
    have hpoint :
        Complex.re (P i i) - Complex.re (Q i i) = hX.eigenvalues i := by
      have hpointC := congrArg (fun M : Matrix d d ℂ => M i i) hdiag
      simpa [D] using congrArg Complex.re hpointC
    calc
      |hX.eigenvalues i| = |Complex.re (P i i) - Complex.re (Q i i)| := by
        rw [← hpoint]
      _ = |Complex.re (P i i) + (-Complex.re (Q i i))| := by
        rw [sub_eq_add_neg]
      _ ≤ |Complex.re (P i i)| + |-Complex.re (Q i i)| := abs_add_le _ _
      _ = Complex.re (P i i) + Complex.re (Q i i) := by
        rw [abs_of_nonneg hPi, abs_neg, abs_of_nonneg hQi]
  calc
    traceNormOp X = ∑ i, |hX.eigenvalues i| := by
      simpa [X] using traceNormOp_hermitian_eq_sum_abs_eigenvalues hX
    _ ≤ ∑ i, (Complex.re (P i i) + Complex.re (Q i i)) := by
      exact Finset.sum_le_sum (fun i hi => hbound i)
    _ = (∑ i, Complex.re (P i i)) + ∑ i, Complex.re (Q i i) := by
      rw [Finset.sum_add_distrib]
    _ = Complex.re (Matrix.trace P) + Complex.re (Matrix.trace Q) := by
      simp [Matrix.trace]
    _ = 2 := by
      rw [hP_trace, hQ_trace]
      norm_num

/-- The concrete trace norm depends only on `Xᴴ * X`. -/
theorem traceNormOp_eq_of_conjTranspose_mul_self_eq
    {d : Type u} [Fintype d] [DecidableEq d]
    {A B : Matrix d d ℂ} (hAB : Aᴴ * A = Bᴴ * B) :
    traceNormOp A = traceNormOp B := by
  dsimp [traceNormOp]
  have hEig :
      (Matrix.isHermitian_conjTranspose_mul_self A).eigenvalues =
        (Matrix.isHermitian_conjTranspose_mul_self B).eigenvalues := by
    apply
      (Matrix.IsHermitian.eigenvalues_eq_eigenvalues_iff
        (Matrix.isHermitian_conjTranspose_mul_self A)
        (Matrix.isHermitian_conjTranspose_mul_self B)).2
    exact congrArg Matrix.charpoly hAB
  rw [hEig]

set_option linter.flexible false in
set_option linter.unusedSimpArgs false in
set_option linter.unnecessarySimpa false in
theorem tensorWithIdentity_adMap_eq
    {d k : Type u} [Fintype d] [DecidableEq d] [Fintype k] [DecidableEq k]
    (U : Matrix d d ℂ) (X : Matrix (d × k) (d × k) ℂ) :
    tensorWithIdentity d k (adMap d U) X =
      (U ⊗ₖ (1 : Matrix k k ℂ)) * X * ((U ⊗ₖ (1 : Matrix k k ℂ))ᴴ) := by
  ext i j
  rcases i with ⟨a, b⟩
  rcases j with ⟨c, e⟩
  have hLHS :
      (tensorWithIdentity d k (adMap d U) X) (a, b) (c, e) =
        ∑ y : d, ∑ x : d, U a x * (X (x, b) (y, e) * star (U c y)) := by
    simp [tensorWithIdentity, adMap, Matrix.mul_apply, mul_assoc]
    simp_rw [Finset.mul_sum]
    rw [Finset.sum_comm]
  have hRHS :
      (((U ⊗ₖ (1 : Matrix k k ℂ)) * X * ((U ⊗ₖ (1 : Matrix k k ℂ))ᴴ)) (a, b) (c, e)) =
        ∑ y : d, ∑ x : d, U a x * (X (x, b) (y, e) * star (U c y)) := by
    simp_rw [Matrix.mul_apply, Matrix.kroneckerMap_apply, Matrix.one_apply,
      Matrix.conjTranspose_apply, Fintype.sum_prod_type]
    rw [Finset.sum_comm]
    rw [Finset.sum_eq_single e]
    · simp [Matrix.one_apply, mul_assoc]
      simp_rw [Finset.sum_mul]
      simpa [mul_assoc, mul_left_comm, mul_comm] using
        (Finset.sum_comm
          (s := (Finset.univ : Finset d))
          (t := (Finset.univ : Finset d))
          (f := fun x y => U a y * (X (y, b) (x, e) * star (U c x))))
    · intro f _ hfe
      have hef : e ≠ f := by simpa [eq_comm] using hfe
      simp [hef]
    · intro hee
      simp at hee
  rw [hLHS, hRHS]

/-- Amplified unitary conjugation preserves density states. -/
theorem tensorWithIdentity_adMap_isDensityState
    {d k : Type u} [Fintype d] [DecidableEq d] [Fintype k] [DecidableEq k]
    (U : Matrix d d ℂ) (hU : Uᴴ * U = 1)
    {ρ : Matrix (d × k) (d × k) ℂ} (hρ : IsDensityState ρ) :
    IsDensityState (tensorWithIdentity d k (adMap d U) ρ) := by
  let K : Matrix (d × k) (d × k) ℂ := U ⊗ₖ (1 : Matrix k k ℂ)
  have hK : Kᴴ * K = 1 := by
    dsimp [K]
    calc
      (U ⊗ₖ (1 : Matrix k k ℂ))ᴴ * (U ⊗ₖ (1 : Matrix k k ℂ))
          = (Uᴴ * U) ⊗ₖ ((1 : Matrix k k ℂ)ᴴ * (1 : Matrix k k ℂ)) := by
              rw [Matrix.conjTranspose_kronecker, Matrix.mul_kronecker_mul]
      _ = (1 : Matrix d d ℂ) ⊗ₖ (1 : Matrix k k ℂ) := by
        simp [hU]
      _ = 1 := by
        simp only [Matrix.one_kronecker_one]
  rw [tensorWithIdentity_adMap_eq (d := d) (k := k) (U := U) (X := ρ)]
  refine ⟨?_, ?_⟩
  · simpa [K, Matrix.mul_assoc] using hρ.1.mul_mul_conjTranspose_same K
  · calc
      Matrix.trace (K * ρ * Kᴴ) = Matrix.trace (Kᴴ * K * ρ) := by
        rw [Matrix.trace_mul_cycle K ρ Kᴴ]
      _ = Matrix.trace ρ := by
        rw [hK, one_mul]
      _ = 1 := hρ.2

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

/-- Tensoring a trace-annihilating map with the identity yields zero partial trace. -/
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

/-- Tensoring a trace-annihilating map with the identity yields a traceless output. -/
theorem tensorWithIdentity_trace_zero
    {d k : Type u} [Fintype d] [DecidableEq d] [Fintype k] [DecidableEq k]
    (Ψ : Channel d) (hT : IsTraceAnnihilating Ψ)
    (Z : Matrix (d × k) (d × k) ℂ) :
    Matrix.trace (tensorWithIdentity d k Ψ Z) = 0 := by
  rw [trace_eq_trace_partialTraceLeft]
  simpa using
    congrArg Matrix.trace (partialTraceLeft_tensor_zero (d := d) (k := k) Ψ hT Z)

/-- Tensoring a Hermiticity-preserving map with the identity preserves Hermiticity on states. -/
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

/-- Paper Lemma 4. -/
theorem lemma4
    {d : Type u} [Fintype d] [DecidableEq d]
    (T : Channel d) (hT : IsQuantumChannel T)
    (Z : Matrix (d × d) (d × d) ℂ) :
    partialTraceLeft d d (tensorWithIdentity d d (idMinus T) Z) = 0 := by
  exact partialTraceLeft_tensor_zero (d := d) (k := d)
    (Ψ := idMinus T) (idMinus_isTraceAnnihilating T hT) Z

/-- Tracelessness of the tensor-amplified output. -/
theorem lemma4_density_trace
    {d : Type u} [Fintype d] [DecidableEq d]
    (T : Channel d) (hT : IsQuantumChannel T)
    (ρ : Matrix (d × d) (d × d) ℂ) (_hρ : IsDensityState ρ) :
    Matrix.trace (tensorWithIdentity d d (idMinus T) ρ) = 0 := by
  exact tensorWithIdentity_trace_zero (d := d) (k := d)
    (Ψ := idMinus T) (idMinus_isTraceAnnihilating T hT) ρ

/-- Hermiticity of the tensor-amplified output. -/
theorem lemma4_density_hermitian
    {d : Type u} [Fintype d] [DecidableEq d]
    (T : Channel d) (hT : IsQuantumChannel T)
    (ρ : Matrix (d × d) (d × d) ℂ) (hρ : IsDensityState ρ) :
    Matrix.IsHermitian (tensorWithIdentity d d (idMinus T) ρ) := by
  exact tensorWithIdentity_hermitian (d := d) (k := d)
    (Ψ := idMinus T) (idMinus_isHermiticityPreserving T hT) ρ hρ

/-- Paper Remark 1: the general Hermiticity-preserving, trace-annihilating bound. -/
theorem remark1
    {d : Type u} [Fintype d] [DecidableEq d] [Nonempty d]
    (Ψ : Channel d) (hH : IsHermiticityPreserving Ψ) (hT : IsTraceAnnihilating Ψ) :
    diamondOp ((transposeMap d).comp Ψ) ≤
      (1 / Real.sqrt 2) * diamondOp (transposeMap d) * diamondOp Ψ := by
  change diamondNorm (tensorWithIdentity d d ((transposeMap d).comp Ψ)) ≤
      (1 / Real.sqrt 2) * diamondOp (transposeMap d) * diamondOp Ψ
  rw [tensorWithIdentity_comp_transpose (d := d) (k := d) (Φ := Ψ)]
  let Ψ' : Channel (d × d) :=
    (partialTransposeMap d d).comp (tensorWithIdentity d d Ψ)
  refine diamond_le_of_pointwise Ψ'
    ((1 / Real.sqrt 2) * diamondOp (transposeMap d) * diamondOp Ψ) ?_
  intro ρ hρ
  let Mρ : Matrix (d × d) (d × d) ℂ := tensorWithIdentity d d Ψ ρ
  have hTrace : Matrix.trace Mρ = 0 := by
    simpa [Mρ] using tensorWithIdentity_trace_zero (d := d) (k := d) Ψ hT ρ
  have hHerm : Matrix.IsHermitian Mρ := by
    simpa [Mρ] using tensorWithIdentity_hermitian (d := d) (k := d) Ψ hH ρ hρ
  have hbound2 : hsNormOp (partialTransposeMap d d Mρ) = hsNormOp Mρ := by
    simpa [Mρ] using lemma3 (d := d) (k := d) Mρ
  have hbound1 :
      traceNormOp (Ψ' ρ) ≤ Real.sqrt (Fintype.card (d × d) : ℝ) * hsNormOp Mρ := by
    have htmp :
        traceNormOp (partialTransposeMap d d Mρ) ≤
          Real.sqrt (Fintype.card (d × d) : ℝ) * hsNormOp (partialTransposeMap d d Mρ) := by
      simpa using lemma2 (Y := partialTransposeMap d d Mρ)
    simpa [Ψ', LinearMap.comp_apply, Mρ, hbound2] using htmp
  have hlemma1 : hsNormOp Mρ ≤ (1 / Real.sqrt 2) * traceNormOp Mρ := by
    simpa [Mρ] using lemma1 (X := Mρ) hHerm hTrace
  have htraceBound : traceNormOp Mρ ≤ diamondOp Ψ := by
    simpa [Mρ, diamondOp] using
      traceNorm_apply_le_diamond
        (d := d × d) (Φ := tensorWithIdentity d d Ψ) (ρ := ρ) hρ
  have hhs : hsNormOp Mρ ≤ (1 / Real.sqrt 2) * diamondOp Ψ := by
    calc
      hsNormOp Mρ ≤ (1 / Real.sqrt 2) * traceNormOp Mρ := hlemma1
      _ ≤ (1 / Real.sqrt 2) * diamondOp Ψ := by
        exact mul_le_mul_of_nonneg_left htraceBound (by positivity)
  have hfinal1 :
      traceNormOp (Ψ' ρ) ≤
        Real.sqrt (Fintype.card (d × d) : ℝ) * ((1 / Real.sqrt 2) * diamondOp Ψ) := by
    exact le_trans hbound1 (mul_le_mul_of_nonneg_left hhs (Real.sqrt_nonneg _))
  have hsqrt : Real.sqrt (Fintype.card (d × d) : ℝ) = diamondOp (transposeMap d) := by
    rw [lemma_transpose_diamond (d := d)]
    have hcard : (Fintype.card (d × d) : ℝ) = (Fintype.card d : ℝ) ^ (2 : ℕ) := by
      simp [Fintype.card_prod, Nat.cast_mul, pow_two]
    rw [hcard, Real.sqrt_sq_eq_abs]
    have hnn : 0 ≤ (Fintype.card d : ℝ) := by
      positivity
    simp [abs_of_nonneg hnn]
  calc
    traceNormOp (Ψ' ρ) ≤
        Real.sqrt (Fintype.card (d × d) : ℝ) * ((1 / Real.sqrt 2) * diamondOp Ψ) := hfinal1
    _ = (1 / Real.sqrt 2) * diamondOp (transposeMap d) * diamondOp Ψ := by
      rw [hsqrt]
      ring

end
end Diamond
