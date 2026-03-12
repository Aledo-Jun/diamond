import Diamond.Setups

open scoped BigOperators
open scoped ComplexOrder
open scoped Kronecker
open scoped MatrixOrder
open scoped Matrix.Norms.Frobenius
open Matrix

namespace Diamond

universe u

noncomputable section

theorem hsNorm_sq_eq_re_trace_conjTranspose_mul_self
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

section

set_option linter.unnecessarySimpa false

theorem hermitian_re_trace_conjTranspose_mul_self_eq_sum_sq_eigenvalues
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

end

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
  dsimp [traceNormOp, traceNorm]
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
  dsimp [traceNormOp, traceNorm]
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
  dsimp [traceNormOp, traceNorm]
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
    (X : Matrix d d ℂ) (hHerm : Matrix.IsHermitian X) (hTrace : Matrix.trace X = 0) :
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

/-- Positive semidefinite matrices have trace norm equal to the real trace. -/
private theorem traceNormOp_posSemidef_eq_trace
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
private theorem traceNormOp_density_eq_one
    {d : Type u} [Fintype d] [DecidableEq d]
    {ρ : Matrix d d ℂ} (hρ : IsDensityState ρ) :
    traceNormOp ρ = 1 := by
  rw [traceNormOp_posSemidef_eq_trace hρ.1, hρ.2]
  simp

/-- The concrete trace distance between density states is at most `2`. -/
private theorem traceNormOp_sub_density_le_two
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
private theorem traceNormOp_eq_of_conjTranspose_mul_self_eq
    {d : Type u} [Fintype d] [DecidableEq d]
    {A B : Matrix d d ℂ} (hAB : Aᴴ * A = Bᴴ * B) :
    traceNormOp A = traceNormOp B := by
  dsimp [traceNormOp, traceNorm]
  have hEig :
      (Matrix.isHermitian_conjTranspose_mul_self A).eigenvalues =
        (Matrix.isHermitian_conjTranspose_mul_self B).eigenvalues := by
    apply
      (Matrix.IsHermitian.eigenvalues_eq_eigenvalues_iff
        (Matrix.isHermitian_conjTranspose_mul_self A)
        (Matrix.isHermitian_conjTranspose_mul_self B)).2
    exact congrArg Matrix.charpoly hAB
  rw [hEig]

end
end Diamond
