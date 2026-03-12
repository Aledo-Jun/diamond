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

/-- The Hilbert--Schmidt square in terms of the trace of `Xᴴ * X`. -/
private theorem hsNorm_sq_eq_re_trace_conjTranspose_mul_self
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

/-- Lemma 2: `‖Y‖₁ ≤ √N ‖Y‖₂` on an `N`-dimensional space. -/
theorem lemma2
    {ι : Type u} [Fintype ι] [DecidableEq ι]
    (Y : Matrix ι ι ℂ) :
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

end
end Diamond
