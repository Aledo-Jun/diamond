import Diamond.Setups
import Diamond.Lemma1
import Diamond.Lemma2
import Diamond.Lemma3
import Diamond.Lemma4

open scoped BigOperators
open scoped ComplexOrder
open scoped Kronecker
open scoped MatrixOrder
open scoped Matrix.Norms.Frobenius
open Matrix

namespace Diamond

universe u
noncomputable section

theorem theorem1
    {d : Type u} [Fintype d] [DecidableEq d] [Nonempty d]
    (T : Channel d) (hT : IsQuantumChannel T) :
    diamondOp ((transposeMap d).comp (idMinus T)) ≤
      (1 / Real.sqrt 2) * diamondOp (transposeMap d) * diamondOp (idMinus T) := by
  change diamondNormAt (d := d) (k := d) ((transposeMap d).comp (idMinus T)) ≤
      (1 / Real.sqrt 2) * diamondOp (transposeMap d) * diamondOp (idMinus T)
  refine diamond_le_of_pointwise (d := d) (k := d) ((transposeMap d).comp (idMinus T))
    ((1 / Real.sqrt 2) * diamondOp (transposeMap d) * diamondOp (idMinus T)) ?_
  intro ρ hρ
  let Mρ : Matrix (d × d) (d × d) ℂ := tensorWithIdentity d d (idMinus T) ρ
  have hrewrite :
      tensorWithIdentity d d ((transposeMap d).comp (idMinus T)) ρ =
        partialTransposeMap d d Mρ := by
    simpa [Mρ, LinearMap.comp_apply] using
      congrArg (fun Ψ : Channel (d × d) => Ψ ρ)
        (tensorWithIdentity_comp_transpose (d := d) (k := d) (Φ := idMinus T))
  have hTrace : Matrix.trace Mρ = 0 := by
    simpa [Mρ] using
      tensorWithIdentity_trace_zero (d := d) (k := d)
        (idMinus T) (idMinus_isTraceAnnihilating T hT) ρ
  have hHerm : Matrix.IsHermitian Mρ := by
    simpa [Mρ] using
      tensorWithIdentity_hermitian (d := d) (k := d)
        (Ψ := idMinus T) (idMinus_isHermiticityPreserving T hT) ρ hρ
  have hlemma3 : hsNormOp (partialTransposeMap d d Mρ) = hsNormOp Mρ := by
    simpa [Mρ] using lemma3 (d := d) (k := d) Mρ
  have hlemma2 :
      traceNormOp (tensorWithIdentity d d ((transposeMap d).comp (idMinus T)) ρ) ≤
        Real.sqrt (Fintype.card (d × d) : ℝ) * hsNormOp Mρ := by
    have htmp :
        traceNormOp (partialTransposeMap d d Mρ) ≤
          Real.sqrt (Fintype.card (d × d) : ℝ) * hsNormOp (partialTransposeMap d d Mρ) := by
      simpa using lemma2 (Y := partialTransposeMap d d Mρ)
    rw [hrewrite]
    simpa [hlemma3] using htmp
  have hlemma1 : hsNormOp Mρ ≤ (1 / Real.sqrt 2) * traceNormOp Mρ := by
    simpa [Mρ] using lemma1 (X := Mρ) hHerm hTrace
  have htraceBound : traceNormOp Mρ ≤ diamondOp (idMinus T) := by
    simpa [Mρ, diamondOp] using
      traceNorm_apply_le_diamond
        (d := d) (k := d) (Φ := idMinus T) (ρ := ρ) hρ
  have hhs : hsNormOp Mρ ≤ (1 / Real.sqrt 2) * diamondOp (idMinus T) := by
    calc
      hsNormOp Mρ ≤ (1 / Real.sqrt 2) * traceNormOp Mρ := hlemma1
      _ ≤ (1 / Real.sqrt 2) * diamondOp (idMinus T) := by
        exact mul_le_mul_of_nonneg_left htraceBound (by positivity)
  have hfinal1 :
      traceNormOp (tensorWithIdentity d d ((transposeMap d).comp (idMinus T)) ρ) ≤
        Real.sqrt (Fintype.card (d × d) : ℝ) * ((1 / Real.sqrt 2) * diamondOp (idMinus T)) := by
    exact le_trans hlemma2 (mul_le_mul_of_nonneg_left hhs (Real.sqrt_nonneg _))
  have hsqrt : Real.sqrt (Fintype.card (d × d) : ℝ) = diamondOp (transposeMap d) := by
    rw [lemma_transpose_diamond (d := d)]
    have hcard : (Fintype.card (d × d) : ℝ) = (Fintype.card d : ℝ) ^ (2 : ℕ) := by
      simp [Fintype.card_prod, Nat.cast_mul, pow_two]
    rw [hcard, Real.sqrt_sq_eq_abs]
    have hnn : 0 ≤ (Fintype.card d : ℝ) := by
      positivity
    simp [abs_of_nonneg hnn]
  calc
    traceNormOp (tensorWithIdentity d d ((transposeMap d).comp (idMinus T)) ρ) ≤
        Real.sqrt (Fintype.card (d × d) : ℝ) *
          ((1 / Real.sqrt 2) * diamondOp (idMinus T)) := hfinal1
    _ = (1 / Real.sqrt 2) * diamondOp (transposeMap d) * diamondOp (idMinus T) := by
      rw [hsqrt]
      ring

end
end Diamond
