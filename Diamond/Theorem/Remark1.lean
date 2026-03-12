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

/-- Paper Remark 1: the general Hermiticity-preserving, trace-annihilating bound. -/
theorem remark1
    {d : Type u} [Fintype d] [DecidableEq d] [Nonempty d]
    (Ψ : Channel d) (hH : IsHermiticityPreserving Ψ) (hT : IsTraceAnnihilating Ψ) :
    diamondOp ((transposeMap d).comp Ψ) ≤
      (1 / Real.sqrt 2) * diamondOp (transposeMap d) * diamondOp Ψ := by
  change diamondNormAt (d := d) (k := d) ((transposeMap d).comp Ψ) ≤
      (1 / Real.sqrt 2) * diamondOp (transposeMap d) * diamondOp Ψ
  refine diamond_le_of_pointwise (d := d) (Φ := (transposeMap d).comp Ψ)
    ((1 / Real.sqrt 2) * diamondOp (transposeMap d) * diamondOp Ψ) ?_
  intro ρ
  let Mρ : Matrix (d × d) (d × d) ℂ := tensorWithIdentity d d Ψ ρ.1
  have hrewrite :
      tensorWithIdentity d d ((transposeMap d).comp Ψ) ρ.1 =
        partialTransposeMap d d Mρ := by
    simpa [Mρ, LinearMap.comp_apply] using
      congrArg (fun Φ : Channel (d × d) => Φ ρ.1)
        (tensorWithIdentity_comp_transpose (d := d) (k := d) (Φ := Ψ))
  have hTrace : Matrix.trace Mρ = 0 := by
    simpa [Mρ] using tensorWithIdentity_trace_zero (d := d) (k := d) Ψ hT ρ.1
  have hHerm : Matrix.IsHermitian Mρ := by
    simpa [Mρ] using tensorWithIdentity_hermitian (d := d) (k := d) Ψ hH ρ.1 ρ.2
  have hbound2 : hsNormOp (partialTransposeMap d d Mρ) = hsNormOp Mρ := by
    simpa [Mρ] using lemma3 (d := d) (k := d) Mρ
  have hbound1 :
      traceNormOp (tensorWithIdentity d d ((transposeMap d).comp Ψ) ρ.1) ≤
        Real.sqrt (Fintype.card (d × d) : ℝ) * hsNormOp Mρ := by
    have htmp :
        traceNormOp (partialTransposeMap d d Mρ) ≤
          Real.sqrt (Fintype.card (d × d) : ℝ) * hsNormOp (partialTransposeMap d d Mρ) := by
      simpa using lemma2 (Y := partialTransposeMap d d Mρ)
    rw [hrewrite]
    simpa [hbound2] using htmp
  have hlemma1 : hsNormOp Mρ ≤ (1 / Real.sqrt 2) * traceNormOp Mρ := by
    simpa [Mρ] using lemma1 (X := Mρ) hHerm hTrace
  have htraceBound : traceNormOp Mρ ≤ diamondOp Ψ := by
    simpa [Mρ, diamondOp] using
      traceNorm_apply_le_diamond
        (d := d) (k := d) (Φ := Ψ) (ρ := ρ)
  have hhs : hsNormOp Mρ ≤ (1 / Real.sqrt 2) * diamondOp Ψ := by
    calc
      hsNormOp Mρ ≤ (1 / Real.sqrt 2) * traceNormOp Mρ := hlemma1
      _ ≤ (1 / Real.sqrt 2) * diamondOp Ψ := by
        exact mul_le_mul_of_nonneg_left htraceBound (by positivity)
  have hfinal1 :
      traceNormOp (tensorWithIdentity d d ((transposeMap d).comp Ψ) ρ.1) ≤
        Real.sqrt (Fintype.card (d × d) : ℝ) * ((1 / Real.sqrt 2) * diamondOp Ψ) := by
    exact le_trans hbound1 (mul_le_mul_of_nonneg_left hhs (Real.sqrt_nonneg _))
  have hsqrt : Real.sqrt (Fintype.card (d × d) : ℝ) = diamondOp (transposeMap d) := by
    symm
    exact lemma_transpose_diamond (d := d)
  calc
    traceNormOp (tensorWithIdentity d d ((transposeMap d).comp Ψ) ρ.1) ≤
        Real.sqrt (Fintype.card (d × d) : ℝ) * ((1 / Real.sqrt 2) * diamondOp Ψ) := hfinal1
    _ = (1 / Real.sqrt 2) * diamondOp (transposeMap d) * diamondOp Ψ := by
      rw [hsqrt]
      ring

end
end Diamond
