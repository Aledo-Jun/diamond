import Diamond.HolevoWerner.Basic

open scoped BigOperators
open scoped ComplexOrder
open scoped Kronecker
open scoped MatrixOrder
open scoped Matrix.Norms.Frobenius
open Matrix

namespace Diamond

universe u

noncomputable section

/-- Generic replacement step for the Holevo-Werner converse: if the transposed error term
is bounded by `c * dim(msg) * ε`, then the usual finite-error argument gives the corresponding
linear bound with coefficient `c`. -/
theorem holevo_werner_linear_bound_of_error_term
    {phys msg : Type u}
    [Fintype phys] [DecidableEq phys]
    [Fintype msg] [DecidableEq msg] [Nonempty msg]
    (T : Channel phys) (m : ℕ)
    (encoder : Superoperator msg phys)
    (decoder : Superoperator phys msg)
    (tensorPower : Channel phys)
    (ε c : ℝ)
    (htranspose_triangle :
      diamondOp (transposeMap msg) ≤
        diamondOp
          ((transposeMap msg).comp (effectiveChannel encoder decoder tensorPower)) +
            diamondOp
              ((transposeMap msg).comp
                (idMinus (effectiveChannel encoder decoder tensorPower))))
    (htranspose_code_bound :
      diamondOp
          ((transposeMap msg).comp (effectiveChannel encoder decoder tensorPower)) ≤
        (diamondOp ((transposeMap phys).comp T)) ^ m)
    (herror_term :
      diamondOp
          ((transposeMap msg).comp
            (idMinus (effectiveChannel encoder decoder tensorPower))) ≤
        c * (Fintype.card msg : ℝ) * ε) :
    (1 - c * ε) * (Fintype.card msg : ℝ) ≤
      (diamondOp ((transposeMap phys).comp T)) ^ m := by
  let effective := effectiveChannel encoder decoder tensorPower
  have hcard : (Fintype.card (msg × msg) : ℝ) = (Fintype.card msg : ℝ) ^ (2 : ℕ) := by
    simp [Fintype.card_prod, Nat.cast_mul, pow_two]
  have hsqrt_msg : Real.sqrt (Fintype.card (msg × msg) : ℝ) = (Fintype.card msg : ℝ) := by
    calc
      Real.sqrt (Fintype.card (msg × msg) : ℝ)
          = Real.sqrt ((Fintype.card msg : ℝ) ^ (2 : ℕ)) := by
            rw [hcard]
      _ = Fintype.card msg := by
            rw [Real.sqrt_sq_eq_abs]
            have hnn : 0 ≤ (Fintype.card msg : ℝ) := by positivity
            simp [abs_of_nonneg hnn]
  rw [transpose_diamond_exact (d := msg)] at htranspose_triangle
  rw [hsqrt_msg] at htranspose_triangle
  have hlinear :
      (1 - c * ε) * (Fintype.card msg : ℝ) ≤
        diamondOp ((transposeMap msg).comp effective) := by
    nlinarith [htranspose_triangle, herror_term]
  calc
    (1 - c * ε) * (Fintype.card msg : ℝ) ≤
        diamondOp ((transposeMap msg).comp effective) := hlinear
    _ ≤ (diamondOp ((transposeMap phys).comp T)) ^ m := htranspose_code_bound

/-- Parametrized Holevo-Werner replacement theorem: if the transposed error term satisfies
`‖Θ ∘ Ψ‖ ≤ α ‖Θ‖ ‖Ψ‖`, then the finite-error converse uses the coefficient `2 * α`. -/
theorem holevo_werner_linear_bound_of_submultiplicative_constant
    {phys msg : Type u}
    [Fintype phys] [DecidableEq phys]
    [Fintype msg] [DecidableEq msg] [Nonempty msg]
    (T : Channel phys) (m : ℕ)
    (encoder : Superoperator msg phys)
    (decoder : Superoperator phys msg)
    (tensorPower : Channel phys)
    (ε α : ℝ)
    (htranspose_triangle :
      diamondOp (transposeMap msg) ≤
        diamondOp
          ((transposeMap msg).comp (effectiveChannel encoder decoder tensorPower)) +
            diamondOp
              ((transposeMap msg).comp
                (idMinus (effectiveChannel encoder decoder tensorPower))))
    (htranspose_code_bound :
      diamondOp
          ((transposeMap msg).comp (effectiveChannel encoder decoder tensorPower)) ≤
        (diamondOp ((transposeMap phys).comp T)) ^ m)
    (hsubmult :
      diamondOp
          ((transposeMap msg).comp
            (idMinus (effectiveChannel encoder decoder tensorPower))) ≤
        α * diamondOp (transposeMap msg) *
          diamondOp (idMinus (effectiveChannel encoder decoder tensorPower)))
    (herror :
      ε =
        (1 / 2 : ℝ) *
          diamondOp (idMinus (effectiveChannel encoder decoder tensorPower))) :
    (1 - (2 * α) * ε) * (Fintype.card msg : ℝ) ≤
      (diamondOp ((transposeMap phys).comp T)) ^ m := by
  let effective := effectiveChannel encoder decoder tensorPower
  have herror_eq : diamondOp (idMinus effective) = 2 * ε := by
    nlinarith [herror]
  have hcard : (Fintype.card (msg × msg) : ℝ) = (Fintype.card msg : ℝ) ^ (2 : ℕ) := by
    simp [Fintype.card_prod, Nat.cast_mul, pow_two]
  have hsqrt_msg : Real.sqrt (Fintype.card (msg × msg) : ℝ) = (Fintype.card msg : ℝ) := by
    calc
      Real.sqrt (Fintype.card (msg × msg) : ℝ)
          = Real.sqrt ((Fintype.card msg : ℝ) ^ (2 : ℕ)) := by
            rw [hcard]
      _ = Fintype.card msg := by
            rw [Real.sqrt_sq_eq_abs]
            have hnn : 0 ≤ (Fintype.card msg : ℝ) := by positivity
            simp [abs_of_nonneg hnn]
  have herror_term :
      diamondOp ((transposeMap msg).comp (idMinus effective)) ≤
        (2 * α) * (Fintype.card msg : ℝ) * ε := by
    calc
      diamondOp ((transposeMap msg).comp (idMinus effective)) ≤
          α * diamondOp (transposeMap msg) * diamondOp (idMinus effective) := hsubmult
      _ = α * Real.sqrt (Fintype.card (msg × msg) : ℝ) * (2 * ε) := by
            rw [transpose_diamond_exact (d := msg), herror_eq]
      _ = α * (Fintype.card msg : ℝ) * (2 * ε) := by
            rw [hsqrt_msg]
      _ = (2 * α) * (Fintype.card msg : ℝ) * ε := by
            ring
  simpa [mul_assoc, mul_left_comm, mul_comm] using
    holevo_werner_linear_bound_of_error_term
      T m encoder decoder tensorPower ε (2 * α)
      htranspose_triangle htranspose_code_bound herror_term

/-- Logarithmic form of the generic replacement-constant Holevo-Werner converse. -/
theorem holevo_werner_bound_of_linear_bound
    {phys msg : Type u}
    [Fintype phys] [DecidableEq phys]
    [Fintype msg] [Nonempty msg]
    (T : Channel phys) (m : ℕ)
    (ε c : ℝ)
    (hlinear :
      (1 - c * ε) * (Fintype.card msg : ℝ) ≤
        (diamondOp ((transposeMap phys).comp T)) ^ m)
    (hm : 0 < m) (hε : ε < 1 / c) (hc : 0 < c) :
    Real.logb 2 (Fintype.card msg : ℝ) / (m : ℝ) ≤
      Real.logb 2 (diamondOp ((transposeMap phys).comp T)) +
        (1 / (m : ℝ)) * Real.logb 2 (1 / (1 - c * ε)) := by
  let msgDim : ℝ := Fintype.card msg
  let delta : ℝ := 1 - c * ε
  let bound : ℝ := diamondOp ((transposeMap phys).comp T)
  have hm_real : 0 < (m : ℝ) := by exact_mod_cast hm
  have hmsgDim_pos : 0 < msgDim := by
    have hcard_pos : 0 < Fintype.card msg := Fintype.card_pos_iff.mpr inferInstance
    simpa [msgDim] using
      (show (0 : ℝ) < (Fintype.card msg : ℝ) from by exact_mod_cast hcard_pos)
  have hdelta_pos : 0 < delta := by
    have hmul : c * ε < 1 := by
      calc
        c * ε < c * (1 / c) := by exact mul_lt_mul_of_pos_left hε hc
        _ = 1 := by
              field_simp [ne_of_gt hc]
    nlinarith
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
            rw [sub_eq_add_neg, hlog_inv]
  refine (div_le_iff₀ hm_real).2 ?_
  have hm_ne : (m : ℝ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hm
  calc
    Real.logb 2 msgDim ≤ (m : ℝ) * Real.logb 2 bound + Real.logb 2 (1 / delta) := hmain
    _ = (Real.logb 2 bound + (1 / (m : ℝ)) * Real.logb 2 (1 / delta)) * (m : ℝ) := by
          field_simp [hm_ne]
    _ = (Real.logb 2 (diamondOp ((transposeMap phys).comp T)) +
          (1 / (m : ℝ)) * Real.logb 2 (1 / (1 - c * ε))) * (m : ℝ) := by
          simp [delta, bound]

end
end Diamond
