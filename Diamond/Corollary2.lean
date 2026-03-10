import Diamond.Setups
import Diamond.Theorem1
import Diamond.Corollary1

open scoped BigOperators
open scoped ComplexOrder
open scoped Kronecker
open scoped MatrixOrder
open scoped Matrix.Norms.Frobenius
open Matrix

namespace Diamond

universe u
noncomputable section

structure Corollary2Witness
    {d msg : Type u} [Fintype d] [DecidableEq d] [Fintype msg] [DecidableEq msg]
    (T : Channel d) (m : ℕ) (ε : ℝ) where
  effective : Channel msg
  effective_quantum : IsQuantumChannel effective
  transpose_triangle :
    diamondOp (transposeMap msg) ≤
      diamondOp ((transposeMap msg).comp effective) +
        diamondOp ((transposeMap msg).comp (idMinus effective))
  transpose_code_bound :
    diamondOp ((transposeMap msg).comp effective) ≤
      (diamondOp ((transposeMap d).comp T)) ^ m
  error_eq : diamondOp (idMinus effective) = 2 * ε

/-- The linear estimate underlying Paper Corollary 2. -/
theorem corollary2_linear_bound
    {d msg : Type u} [Fintype d] [DecidableEq d] [Nonempty d]
    [Fintype msg] [DecidableEq msg] [Nonempty msg]
    (T : Channel d) (m : ℕ) (ε : ℝ)
    (hcode : Corollary2Witness (d := d) (msg := msg) T m ε) :
    (1 - Real.sqrt 2 * ε) * (Fintype.card msg : ℝ) ≤
      (diamondOp ((transposeMap d).comp T)) ^ m := by
  have hrem := theorem1 hcode.effective hcode.effective_quantum
  have hsqrt2_ne : Real.sqrt 2 ≠ 0 := by positivity
  have herror_bound :
      diamondOp ((transposeMap msg).comp (idMinus hcode.effective)) ≤
        Real.sqrt 2 * (Fintype.card msg : ℝ) * ε := by
    calc
      diamondOp ((transposeMap msg).comp (idMinus hcode.effective)) ≤
          (1 / Real.sqrt 2) * diamondOp (transposeMap msg) * diamondOp (idMinus hcode.effective) :=
        hrem
      _ = (1 / Real.sqrt 2) * (Fintype.card msg : ℝ) * (2 * ε) := by
        rw [lemma_transpose_diamond (d := msg), hcode.error_eq]
      _ = Real.sqrt 2 * (Fintype.card msg : ℝ) * ε := by
        have hsqrt2 : 2 / Real.sqrt 2 = Real.sqrt 2 := by
          apply (div_eq_iff hsqrt2_ne).2
          nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 2 by positivity)]
        calc
          (1 / Real.sqrt 2) * (Fintype.card msg : ℝ) * (2 * ε)
              = ((2 / Real.sqrt 2) * (Fintype.card msg : ℝ)) * ε := by ring
          _ = (Real.sqrt 2 * (Fintype.card msg : ℝ)) * ε := by rw [hsqrt2]
          _ = Real.sqrt 2 * (Fintype.card msg : ℝ) * ε := by ring
  have htri := hcode.transpose_triangle
  rw [lemma_transpose_diamond (d := msg)] at htri
  have hlinear :
      (1 - Real.sqrt 2 * ε) * (Fintype.card msg : ℝ) ≤
        diamondOp ((transposeMap msg).comp hcode.effective) := by
    nlinarith [htri, herror_bound]
  calc
    (1 - Real.sqrt 2 * ε) * (Fintype.card msg : ℝ) ≤
        diamondOp ((transposeMap msg).comp hcode.effective) := hlinear
    _ ≤ (diamondOp ((transposeMap d).comp T)) ^ m := hcode.transpose_code_bound

/-- Paper Corollary 2. -/
theorem corollary2
    {d msg : Type u} [Fintype d] [DecidableEq d] [Nonempty d]
    [Fintype msg] [DecidableEq msg] [Nonempty msg]
    (T : Channel d) (m : ℕ) (ε : ℝ)
    (hcode : Corollary2Witness (d := d) (msg := msg) T m ε)
    (hm : 0 < m) (hε : ε < 1 / Real.sqrt 2) :
    Real.logb 2 (Fintype.card msg : ℝ) / (m : ℝ) ≤
      Real.logb 2 (diamondOp ((transposeMap d).comp T)) +
        (1 / (m : ℝ)) * Real.logb 2 (1 / (1 - Real.sqrt 2 * ε)) := by
  let msgDim : ℝ := Fintype.card msg
  let delta : ℝ := 1 - Real.sqrt 2 * ε
  let bound : ℝ := diamondOp ((transposeMap d).comp T)
  have hlinear : delta * msgDim ≤ bound ^ m := by
    simpa [delta, msgDim, bound] using corollary2_linear_bound T m ε hcode
  have hm_real : 0 < (m : ℝ) := by exact_mod_cast hm
  have hmsgDim_pos : 0 < msgDim := by
    have hcard_pos : 0 < Fintype.card msg := Fintype.card_pos_iff.mpr inferInstance
    simpa [msgDim] using (show (0 : ℝ) < (Fintype.card msg : ℝ) from by exact_mod_cast hcard_pos)
  have hdelta_pos : 0 < delta := by
    have hdelta_pos' : 0 < 1 - Real.sqrt 2 * ε := by
      have hsqrt2_pos : 0 < Real.sqrt 2 := by positivity
      have hsqrt2_ne : Real.sqrt 2 ≠ 0 := by positivity
      have hmul : Real.sqrt 2 * ε < 1 := by
        calc
          Real.sqrt 2 * ε < Real.sqrt 2 * (1 / Real.sqrt 2) := by
            exact mul_lt_mul_of_pos_left hε hsqrt2_pos
          _ = 1 := by
            field_simp [hsqrt2_ne]
      nlinarith
    simpa [delta] using hdelta_pos'
  have hlog :
      Real.logb 2 (delta * msgDim) ≤ Real.logb 2 (bound ^ m) := by
    exact Real.logb_le_logb_of_le (b := 2) (by norm_num) (mul_pos hdelta_pos hmsgDim_pos) hlinear
  have hlog' :
      Real.logb 2 delta + Real.logb 2 msgDim ≤ (m : ℝ) * Real.logb 2 bound := by
    simpa [delta, msgDim, bound, Real.logb_mul (ne_of_gt hdelta_pos) (ne_of_gt hmsgDim_pos),
      Real.logb_pow] using hlog
  have hmain :
      Real.logb 2 msgDim ≤
        (m : ℝ) * Real.logb 2 bound + Real.logb 2 (1 / delta) := by
    have htmp : Real.logb 2 msgDim ≤ (m : ℝ) * Real.logb 2 bound - Real.logb 2 delta := by
      linarith
    calc
      Real.logb 2 msgDim ≤ (m : ℝ) * Real.logb 2 bound - Real.logb 2 delta := htmp
      _ = (m : ℝ) * Real.logb 2 bound + Real.logb 2 (1 / delta) := by
        have hlog_inv : -Real.logb 2 delta = Real.logb 2 (1 / delta) := by
          rw [one_div]
          exact (Real.logb_inv 2 delta).symm
        rw [sub_eq_add_neg]
        rw [hlog_inv]
  refine (div_le_iff₀ hm_real).2 ?_
  have hm_ne : (m : ℝ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hm
  calc
    Real.logb 2 msgDim ≤ (m : ℝ) * Real.logb 2 bound + Real.logb 2 (1 / delta) := hmain
    _ = (Real.logb 2 bound + (1 / (m : ℝ)) * Real.logb 2 (1 / delta)) * (m : ℝ) := by
      field_simp [hm_ne]
    _ = (Real.logb 2 (diamondOp ((transposeMap d).comp T)) +
          (1 / (m : ℝ)) * Real.logb 2 (1 / (1 - Real.sqrt 2 * ε))) * (m : ℝ) := by
      simp [delta, bound]

end
end Diamond
