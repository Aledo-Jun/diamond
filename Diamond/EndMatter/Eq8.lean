import Diamond.Setups
import Diamond.StandardFacts
import Diamond.Theorem.Theorem1
import Diamond.EndMatter.Eq7

open scoped BigOperators
open scoped ComplexOrder
open scoped Kronecker
open scoped MatrixOrder
open scoped Matrix.Norms.Frobenius
open Matrix

namespace Diamond

universe u

noncomputable section

/-- Paper Eq. (8): the unitary channel `Ad_{U_d}` sits at diamond distance `2`
    from the identity. -/
theorem theorem_eq8 (d : ℕ) [Fact (1 < d)] :
    diamondOp (idMinus (adMap (Fin d) (Ud d))) = 2 := by
  exact unitary_channel_diamond_distance_eq_two_of_trace_zero
    (U := Ud d) (hU := ud_conjTranspose_mul_self d) (htrace := trace_Ud_eq_zero d)

/-- The finite-dimensional bounds from Theorem 1, Eq. (7), and Eq. (8)
    force any dimension-independent constant to be at least `2 / π`. -/
theorem alpha_lower_bound :
    (2 : ℝ) / Real.pi ≤ (1 : ℝ) / Real.sqrt 2 := by
  apply asymptotic_cotangent_lower_bound
  intro d hd
  have hd_gt_one : 1 < d := lt_of_lt_of_le Nat.one_lt_two hd
  letI : Fact (1 < d) := ⟨hd_gt_one⟩
  have hd_pos : 0 < d := lt_trans Nat.zero_lt_one hd_gt_one
  letI : Nonempty (Fin d) := ⟨⟨0, hd_pos⟩⟩
  have hU : (Ud d)ᴴ * Ud d = 1 := ud_conjTranspose_mul_self d
  have hchan : IsQuantumChannel (adMap (Fin d) (Ud d)) :=
    adMap_isQuantumChannel (d := Fin d) (U := Ud d) hU
  have htheta : diamondOp (transposeMap (Fin d)) = (d : ℝ) := by
    rw [transpose_diamond_exact (d := Fin d)]
    simp [Fintype.card_prod, Nat.cast_mul]
  have hmain :
      2 * Real.cot (Real.pi / (2 * (d : ℝ))) ≤
        (1 / Real.sqrt 2) * (d : ℝ) * 2 := by
    calc
      2 * Real.cot (Real.pi / (2 * (d : ℝ))) ≤ diamondOp (Lambda d) := theorem_eq7 d
      _ ≤ (1 / Real.sqrt 2) * diamondOp (transposeMap (Fin d)) *
            diamondOp (idMinus (adMap (Fin d) (Ud d))) := by
              simpa [Lambda] using theorem1 (d := Fin d) (T := adMap (Fin d) (Ud d)) hchan
      _ = (1 / Real.sqrt 2) * (d : ℝ) * 2 := by
            rw [htheta, theorem_eq8 d]
  have hcot :
      Real.cot (Real.pi / (2 * (d : ℝ))) ≤ (1 / Real.sqrt 2) * (d : ℝ) := by
    nlinarith
  have hd_posR : 0 < (d : ℝ) := by
    exact_mod_cast hd_pos
  exact (div_le_iff₀ hd_posR).2 <| by
    simpa [div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using hcot

end
end Diamond
