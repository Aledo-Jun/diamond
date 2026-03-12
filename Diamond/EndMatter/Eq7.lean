import Diamond.Setups
import Diamond.StandardFacts
import Diamond.Theorem.Lemma1
import Diamond.PositiveGap.Lemma6

open scoped BigOperators
open scoped ComplexOrder
open scoped Kronecker
open scoped MatrixOrder
open scoped Matrix.Norms.Frobenius
open Matrix

namespace Diamond

universe u
noncomputable section

/-- The maximally entangled vector used in the lower bound for Eq. (7). -/
def omegaVec (d : ℕ) : Fin d × Fin d → ℂ :=
  fun ij => if ij.1 = ij.2 then (Real.sqrt d : ℂ)⁻¹ else 0

/-- The corresponding rank-one density operator `|Ω_d⟩⟨Ω_d|`. -/
def phiState (d : ℕ) : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ :=
  Matrix.vecMulVec (omegaVec d) (star (omegaVec d))

theorem inv_sqrt_mul_inv_sqrt (d : ℕ) [Fact (1 < d)] :
    ((Real.sqrt d : ℂ)⁻¹) * ((Real.sqrt d : ℂ)⁻¹) = (d : ℂ)⁻¹ := by
  have hd_pos_nat : 0 < d := lt_trans Nat.zero_lt_one ‹Fact (1 < d)›.out
  have hd_pos : (0 : ℝ) < d := by
    exact_mod_cast hd_pos_nat
  have hsqrt_neR : (Real.sqrt d : ℝ) ≠ 0 := by
    exact (Real.sqrt_ne_zero').2 hd_pos
  have hsqrt_ne : (Real.sqrt d : ℂ) ≠ 0 := by
    exact_mod_cast hsqrt_neR
  calc
    ((Real.sqrt d : ℂ)⁻¹) * ((Real.sqrt d : ℂ)⁻¹)
        = ((Real.sqrt d : ℂ) ^ 2)⁻¹ := by
          field_simp [hsqrt_ne]
    _ = (d : ℂ)⁻¹ := by
      congr 1
      exact_mod_cast Real.sq_sqrt (show 0 ≤ (d : ℝ) by positivity)

theorem phiState_trace (d : ℕ) [Fact (1 < d)] :
    Matrix.trace (phiState d) = 1 := by
  rw [phiState, Matrix.trace_vecMulVec, dotProduct, Fintype.sum_prod_type]
  simp [omegaVec, inv_sqrt_mul_inv_sqrt]

theorem phiState_isDensityState (d : ℕ) [Fact (1 < d)] :
    IsDensityState (phiState d) := by
  refine ⟨?_, phiState_trace d⟩
  simpa [phiState] using Matrix.posSemidef_vecMulVec_self_star (omegaVec d)

/-- Entrywise formula for the maximally entangled state. -/
theorem phiState_apply (d : ℕ) [Fact (1 < d)] (a b c e : Fin d) :
    phiState d (c, b) (a, e) = if c = b ∧ a = e then (d : ℂ)⁻¹ else 0 := by
  rw [phiState, Matrix.vecMulVec_apply]
  by_cases hcb : c = b
  · by_cases hae : a = e
    · simp only [omegaVec, hcb, hae, if_true, Pi.star_apply]
      simpa using inv_sqrt_mul_inv_sqrt d
    · simp [omegaVec, hcb, hae]
  · by_cases hae : a = e
    · simp [omegaVec, hcb, hae]
    · simp [omegaVec, hcb, hae]

/-- The transposed maximally entangled state is the normalized swap operator. -/
theorem transpose_phiState_eq_swap (d : ℕ) [Fact (1 < d)] :
    tensorWithIdentity (Fin d) (Fin d) (transposeMap (Fin d)) (phiState d) =
      (d : ℂ)⁻¹ • swapMatrix d := by
  ext i j
  rcases i with ⟨a, b⟩
  rcases j with ⟨c, e⟩
  simp [tensorWithIdentity, transposeMap, swapMatrix, phiState_apply, eq_comm, and_comm]

theorem swapMatrix_mul_phase_apply (d : ℕ) [Fact (1 < d)] (a b c e : Fin d) :
    (swapMatrix d * ((Ud d)ᵀ ⊗ₖ star (Ud d))) (a, b) (c, e) =
      if b = c ∧ a = e then Ud d b b * star (Ud d e e) else 0 := by
  classical
  rw [Matrix.mul_apply]
  rw [Finset.sum_eq_single (b, a)]
  · by_cases hae : a = e
    · simp [swapMatrix, Ud, Matrix.diagonal_apply, hae, and_comm]
    · have hea : ¬ e = a := by
        simpa [eq_comm] using hae
      simp [swapMatrix, Ud, Matrix.diagonal_apply, hae, hea, and_comm]
  · intro x _ hne
    have hswap : ¬ (a = x.2 ∧ b = x.1) := by
      intro hx
      apply hne
      ext <;> simp [hx.1, hx.2]
    simp [swapMatrix, hswap]
  · intro hba
    simp at hba

/-- Explicit formula for `((Θ ∘ Ad_U) ⊗ id) (Φ_d)`. -/
theorem transpose_ad_phiState_eq_swap_mul_phase (d : ℕ) [Fact (1 < d)] :
    tensorWithIdentity
        (Fin d)
        (Fin d)
        ((transposeMap (Fin d)).comp (adMap (Fin d) (Ud d)))
        (phiState d) =
      (d : ℂ)⁻¹ • (swapMatrix d * ((Ud d)ᵀ ⊗ₖ star (Ud d))) := by
  ext i j
  rcases i with ⟨a, b⟩
  rcases j with ⟨c, e⟩
  have hEntry :
      tensorWithIdentity
          (Fin d)
          (Fin d)
          ((transposeMap (Fin d)).comp (adMap (Fin d) (Ud d)))
          (phiState d)
          (a, b)
          (c, e) =
        if b = c ∧ a = e then
          (d : ℂ)⁻¹ * Ud d b b * star (Ud d e e)
        else 0 := by
      by_cases h : b = c ∧ a = e
      · rcases h with ⟨hbc, hae⟩
        simp [tensorWithIdentity, transposeMap, adMap, LinearMap.comp_apply, Matrix.mul_apply,
          phiState_apply, Ud, Matrix.diagonal_apply, hbc, hae, mul_comm, mul_left_comm,
          mul_assoc]
      · have hcases : ¬ c = b ∨ ¬ a = e := by
          by_cases hcb : c = b
          · right
            intro hae
            apply h
            exact ⟨hcb.symm, hae⟩
          · left
            exact hcb
        rcases hcases with hcb | hae
        · have hbc : ¬ b = c := by
            simpa [eq_comm] using hcb
          simp [tensorWithIdentity, transposeMap, adMap, LinearMap.comp_apply,
            Matrix.mul_apply, phiState_apply, Ud, Matrix.diagonal_apply, hcb, hbc]
        · have hea : ¬ e = a := by
            simpa [eq_comm] using hae
          simp [tensorWithIdentity, transposeMap, adMap, LinearMap.comp_apply,
            Matrix.mul_apply, phiState_apply, Ud, Matrix.diagonal_apply, hae]
  calc
    tensorWithIdentity
        (Fin d)
        (Fin d)
        ((transposeMap (Fin d)).comp (adMap (Fin d) (Ud d)))
        (phiState d)
        (a, b)
        (c, e)
      = if b = c ∧ a = e then
          (d : ℂ)⁻¹ * Ud d b b * star (Ud d e e)
        else 0 := hEntry
    _ = ((d : ℂ)⁻¹ • (swapMatrix d * ((Ud d)ᵀ ⊗ₖ star (Ud d)))) (a, b) (c, e) := by
      simp [swapMatrix_mul_phase_apply, and_comm, mul_assoc]

/-- Explicit formula for `((Λ_d ⊗ id) (Φ_d))` in matrix form. -/
theorem lambda_phiState_eq (d : ℕ) [Fact (1 < d)] :
    tensorWithIdentity (Fin d) (Fin d) (Lambda d) (phiState d) =
      (d : ℂ)⁻¹ •
        (swapMatrix d - swapMatrix d * ((Ud d)ᵀ ⊗ₖ star (Ud d))) := by
  calc
    tensorWithIdentity (Fin d) (Fin d) (Lambda d) (phiState d)
      =
        tensorWithIdentity (Fin d) (Fin d) (transposeMap (Fin d)) (phiState d) -
          tensorWithIdentity
            (Fin d)
            (Fin d)
            ((transposeMap (Fin d)).comp (adMap (Fin d) (Ud d)))
            (phiState d) := by
              ext i j
              simp [Lambda, idMinus, tensorWithIdentity, transposeMap, adMap,
                LinearMap.comp_apply]
    _ =
        (d : ℂ)⁻¹ • swapMatrix d -
          (d : ℂ)⁻¹ • (swapMatrix d * ((Ud d)ᵀ ⊗ₖ star (Ud d))) := by
            rw [transpose_phiState_eq_swap, transpose_ad_phiState_eq_swap_mul_phase]
    _ =
        (d : ℂ)⁻¹ •
          (swapMatrix d - swapMatrix d * ((Ud d)ᵀ ⊗ₖ star (Ud d))) := by
            simp [smul_sub]

/-- The witness-state reduction for the lower bound in Eq. (7). -/
theorem theorem_eq7_witness_bound (d : ℕ) [Fact (1 < d)] :
    traceNormOp
        ((tensorWithIdentity (Fin d) (Fin d) (Lambda d)) (phiState d)) ≤
      diamondOp (Lambda d) := by
  simpa [diamondOp] using
    traceNorm_apply_le_diamond (d := Fin d) (k := Fin d)
      (Φ := Lambda d)
      (ρ := ⟨phiState d, phiState_isDensityState d⟩)

theorem theorem_eq7_witness_bound_explicit (d : ℕ) [Fact (1 < d)] :
    traceNormOp
        ((d : ℂ)⁻¹ •
          (swapMatrix d - swapMatrix d * ((Ud d)ᵀ ⊗ₖ star (Ud d)))) ≤
      diamondOp (Lambda d) := by
  simpa [lambda_phiState_eq] using theorem_eq7_witness_bound d

/-- The phase diagonal satisfies the expected addition law on `Fin d`. -/
theorem ud_add_eq_mul (d : ℕ) [Fact (1 < d)] (a b : Fin d) :
    Ud d (a + b) (a + b) = Ud d a a * Ud d b b := by
  have hd_pos : 0 < d := lt_trans Nat.zero_lt_one ‹Fact (1 < d)›.out
  have hd_ne : (d : ℂ) ≠ 0 := by
    exact_mod_cast hd_pos.ne'
  let q : ℕ := ((a : ℕ) + (b : ℕ)) / d
  let A : ℂ := (2 * Real.pi * Complex.I * (a : ℂ)) / (d : ℂ)
  let B : ℂ := (2 * Real.pi * Complex.I * (b : ℂ)) / (d : ℂ)
  let Q : ℂ := (q : ℂ) * (2 * Real.pi * Complex.I)
  have hcast :
      (((a + b : Fin d) : ℕ) : ℂ) = (a : ℂ) + (b : ℂ) - (d : ℂ) * (q : ℂ) := by
    have hnat : ((a + b : Fin d) : ℕ) = (a : ℕ) + (b : ℕ) - d * q := by
      simp [Fin.val_add, Nat.mod_eq_sub_mul_div, q]
    have hle : d * q ≤ (a : ℕ) + (b : ℕ) := by
      dsimp [q]
      exact Nat.mul_div_le _ _
    calc
      (((a + b : Fin d) : ℕ) : ℂ)
          = (((a : ℕ) + (b : ℕ) - d * q : ℕ) : ℂ) := by
              exact congrArg (fun n : ℕ => (n : ℂ)) hnat
      _ = (a : ℂ) + (b : ℂ) - (d : ℂ) * (q : ℂ) := by
            norm_num [Nat.cast_sub hle, Nat.cast_add, Nat.cast_mul]
  have hexp :
      (2 * Real.pi * Complex.I * (((a + b : Fin d) : ℕ) : ℂ)) / (d : ℂ) = A + B - Q := by
    rw [hcast]
    dsimp [A, B, Q]
    field_simp [hd_ne]
  have hperiod : Complex.exp (-Q) = 1 := by
    dsimp [Q]
    have h :
        -(↑q * (2 * Real.pi * Complex.I)) =
          (((-(q : ℤ)) : ℂ) * (2 * Real.pi * Complex.I)) := by
      norm_num
    rw [h]
    simpa using (Complex.exp_int_mul_two_pi_mul_I (-(q : ℤ)))
  unfold Ud
  simp only [Matrix.diagonal_apply_eq]
  rw [hexp, sub_eq_add_neg, Complex.exp_add, Complex.exp_add, hperiod]
  simp [A, B, mul_assoc]

/-- The phase diagonal has unit-modulus entries. -/
theorem ud_mul_star_self (d : ℕ) [Fact (1 < d)] (b : Fin d) :
    Ud d b b * star (Ud d b b) = 1 := by
  have hd_pos : 0 < d := lt_trans Nat.zero_lt_one ‹Fact (1 < d)›.out
  have hd_ne : (d : ℂ) ≠ 0 := by
    exact_mod_cast hd_pos.ne'
  have hrew :
      Ud d b b = Complex.exp ((((2 * Real.pi * (b : ℝ)) / d : ℝ) : ℂ) * Complex.I) := by
    simp [Ud]
    congr 1
    field_simp [hd_ne]
  rw [hrew]
  change Complex.exp (↑((2 * Real.pi * ↑b) / d) * Complex.I) *
      (starRingEnd ℂ) (Complex.exp (↑((2 * Real.pi * ↑b) / d) * Complex.I)) = 1
  rw [Complex.mul_conj, Complex.normSq_eq_norm_sq, Complex.norm_exp_ofReal_mul_I]
  norm_num

theorem ud_conjTranspose_mul_self (d : ℕ) [Fact (1 < d)] :
    (Ud d)ᴴ * Ud d = 1 := by
  unfold Ud
  rw [Matrix.diagonal_conjTranspose, Matrix.diagonal_mul_diagonal]
  ext i j
  by_cases hij : i = j
  · subst hij
    simpa [Ud, Matrix.diagonal_apply_eq, mul_comm] using (ud_mul_star_self d i)
  · simp [hij]

/-- Translating indices by `b` removes the compensating phase `star (Ud_d(b,b))`. -/
theorem ud_add_mul_star_eq (d : ℕ) [Fact (1 < d)] (a b : Fin d) :
    Ud d (a + b) (a + b) * star (Ud d b b) = Ud d a a := by
  rw [ud_add_eq_mul, mul_assoc, ud_mul_star_self, mul_one]

/-- Right-multiplying by a diagonal matrix keeps only the swapped diagonal entry. -/
theorem swapMatrix_mul_diagonal_apply
    (d : ℕ) (f : Fin d × Fin d → ℂ) (a b c e : Fin d) :
    (swapMatrix d * Matrix.diagonal f) (a, b) (c, e) =
      if b = c ∧ a = e then f (c, e) else 0 := by
  rw [Matrix.mul_apply]
  rw [Finset.sum_eq_single (b, a)]
  · by_cases h : b = c ∧ a = e
    · rcases h with ⟨hbc, hae⟩
      simp [swapMatrix, hbc, hae]
    · have hcases : ¬ b = c ∨ ¬ a = e := by
        by_cases hbc : b = c
        · right
          intro hae
          apply h
          exact ⟨hbc, hae⟩
        · left
          exact hbc
      rcases hcases with hbc | hae
      · simp [swapMatrix, hbc]
      · have hea : ¬ e = a := by
          simpa [eq_comm] using hae
        simp [swapMatrix, hae]
  · intro x _ hne
    have hswap : ¬ (a = x.2 ∧ b = x.1) := by
      intro hx
      apply hne
      ext <;> simp [hx.1, hx.2]
    simp [swapMatrix, hswap]
  · intro hba
    simp at hba

/-- The explicit witness is a swap times a diagonal matrix. -/
theorem explicit_witness_eq_swap_diagonal (d : ℕ) [Fact (1 < d)] :
    ((d : ℂ)⁻¹ •
      (swapMatrix d - swapMatrix d * ((Ud d)ᵀ ⊗ₖ star (Ud d)))) =
    swapMatrix d * Matrix.diagonal (fun ab =>
      (d : ℂ)⁻¹ * (1 - Ud d ab.1 ab.1 * star (Ud d ab.2 ab.2))) := by
  ext i j
  rcases i with ⟨a, b⟩
  rcases j with ⟨c, e⟩
  by_cases h : b = c ∧ a = e
  · rcases h with ⟨hbc, hae⟩
    subst hbc
    subst hae
    have hswap : swapMatrix d (a, b) (b, a) = 1 := by
      simp [swapMatrix]
    have hphase :
        (swapMatrix d * ((Ud d)ᵀ ⊗ₖ star (Ud d))) (a, b) (b, a) =
          Ud d b b * star (Ud d a a) := by
      simpa using swapMatrix_mul_phase_apply d a b b a
    have hdiag :
        (swapMatrix d *
            Matrix.diagonal (fun ab : Fin d × Fin d =>
              (d : ℂ)⁻¹ * (1 - Ud d ab.1 ab.1 * star (Ud d ab.2 ab.2))))
            (a, b) (b, a) =
          (d : ℂ)⁻¹ * (1 - Ud d b b * star (Ud d a a)) := by
      simpa using
        swapMatrix_mul_diagonal_apply d
          (fun ab : Fin d × Fin d =>
            (d : ℂ)⁻¹ * (1 - Ud d ab.1 ab.1 * star (Ud d ab.2 ab.2)))
          a b b a
    rw [hdiag]
    simp [hswap, hphase, sub_eq_add_neg]
  · have hcases : ¬ b = c ∨ ¬ a = e := by
      by_cases hbc : b = c
      · right
        intro hae
        apply h
        exact ⟨hbc, hae⟩
      · left
        exact hbc
    rcases hcases with hbc | hae
    · have hcb : ¬ c = b := by
        simpa [eq_comm] using hbc
      have hswap : swapMatrix d (a, b) (c, e) = 0 := by
        simp [swapMatrix, hbc]
      have hphase :
          (swapMatrix d * ((Ud d)ᵀ ⊗ₖ star (Ud d))) (a, b) (c, e) = 0 := by
        simpa [hbc] using swapMatrix_mul_phase_apply d a b c e
      have hdiag :
          (swapMatrix d *
              Matrix.diagonal (fun ab : Fin d × Fin d =>
                (d : ℂ)⁻¹ * (1 - Ud d ab.1 ab.1 * star (Ud d ab.2 ab.2))))
              (a, b) (c, e) = 0 := by
        simpa [hbc] using
          swapMatrix_mul_diagonal_apply d
            (fun ab : Fin d × Fin d =>
              (d : ℂ)⁻¹ * (1 - Ud d ab.1 ab.1 * star (Ud d ab.2 ab.2)))
            a b c e
      rw [hdiag]
      simp [Matrix.sub_apply, hswap, hphase]
    · have hea : ¬ e = a := by
        simpa [eq_comm] using hae
      have hswap : swapMatrix d (a, b) (c, e) = 0 := by
        simp [swapMatrix, hae]
      have hphase :
          (swapMatrix d * ((Ud d)ᵀ ⊗ₖ star (Ud d))) (a, b) (c, e) = 0 := by
        simpa [hae] using swapMatrix_mul_phase_apply d a b c e
      have hdiag :
          (swapMatrix d *
              Matrix.diagonal (fun ab : Fin d × Fin d =>
                (d : ℂ)⁻¹ * (1 - Ud d ab.1 ab.1 * star (Ud d ab.2 ab.2))))
              (a, b) (c, e) = 0 := by
        simpa [hae] using
          swapMatrix_mul_diagonal_apply d
            (fun ab : Fin d × Fin d =>
              (d : ℂ)⁻¹ * (1 - Ud d ab.1 ab.1 * star (Ud d ab.2 ab.2)))
            a b c e
      rw [hdiag]
      simp [Matrix.sub_apply, hswap, hphase]

/-- The witness trace norm collapses to the one-dimensional phase sum. -/
theorem explicit_witness_traceNorm_eq_sum (d : ℕ) [Fact (1 < d)] :
    traceNormOp
      ((d : ℂ)⁻¹ •
        (swapMatrix d - swapMatrix d * ((Ud d)ᵀ ⊗ₖ star (Ud d)))) =
      ∑ k : Fin d, ‖1 - Ud d k k‖ := by
  let f : Fin d × Fin d → ℂ := fun ab =>
    (d : ℂ)⁻¹ * (1 - Ud d ab.1 ab.1 * star (Ud d ab.2 ab.2))
  rw [explicit_witness_eq_swap_diagonal]
  rw [traceNormOp_mul_left_isometry (U := swapMatrix d) (X := Matrix.diagonal f)
    (hU := swapMatrix_conjTranspose_mul_self d)]
  rw [traceNormOp_diagonal]
  have hd_pos : 0 < d := lt_trans Nat.zero_lt_one ‹Fact (1 < d)›.out
  have hd_neR : (d : ℝ) ≠ 0 := by
    exact_mod_cast hd_pos.ne'
  have hscalar : ‖((d : ℂ)⁻¹)‖ = (d : ℝ)⁻¹ := by
    rw [norm_inv, Complex.norm_natCast]
  calc
    ∑ i, ‖f i‖
      = ∑ i : Fin d × Fin d, ‖((d : ℂ)⁻¹) * (1 - Ud d i.1 i.1 * star (Ud d i.2 i.2))‖ := by
          rfl
    _ = ∑ i : Fin d × Fin d, ‖((d : ℂ)⁻¹)‖ * ‖1 - Ud d i.1 i.1 * star (Ud d i.2 i.2)‖ := by
          refine Finset.sum_congr rfl ?_
          intro i hi
          rw [norm_mul]
    _ = ‖((d : ℂ)⁻¹)‖ * ∑ i : Fin d × Fin d, ‖1 - Ud d i.1 i.1 * star (Ud d i.2 i.2)‖ := by
          rw [← Finset.mul_sum]
    _ = (d : ℝ)⁻¹ * ∑ i : Fin d × Fin d, ‖1 - Ud d i.1 i.1 * star (Ud d i.2 i.2)‖ := by
          rw [hscalar]
    _ = (d : ℝ)⁻¹ * ((d : ℝ) * ∑ k : Fin d, ‖1 - Ud d k k‖) := by
          congr 1
          calc
            ∑ i : Fin d × Fin d, ‖1 - Ud d i.1 i.1 * star (Ud d i.2 i.2)‖
              = ∑ a : Fin d, ∑ b : Fin d, ‖1 - Ud d a a * star (Ud d b b)‖ := by
                  simp [Fintype.sum_prod_type]
            _ = ∑ b : Fin d, ∑ a : Fin d, ‖1 - Ud d a a * star (Ud d b b)‖ := by
                  simpa using
                    (Finset.sum_comm
                      (s := (Finset.univ : Finset (Fin d)))
                      (t := (Finset.univ : Finset (Fin d)))
                      (f := fun a b => ‖1 - Ud d a a * star (Ud d b b)‖))
            _ = ∑ b : Fin d, ∑ a : Fin d, ‖1 - Ud d a a‖ := by
                  refine Finset.sum_congr rfl ?_
                  intro b hb
                  have hinner :
                      ∑ k : Fin d, ‖1 - Ud d k k * star (Ud d b b)‖ =
                        ∑ a : Fin d, ‖1 - Ud d a a‖ := by
                    exact (Fintype.sum_bijective (fun a => a + b)
                      (AddGroup.addRight_bijective b)
                      (fun a => ‖1 - Ud d a a‖)
                      (fun k => ‖1 - Ud d k k * star (Ud d b b)‖)
                      (fun a => by
                        change ‖1 - Ud d a a‖ =
                          ‖1 - Ud d (a + b) (a + b) * star (Ud d b b)‖
                        rw [ud_add_mul_star_eq])).symm
                  exact hinner
            _ = (d : ℝ) * ∑ a : Fin d, ‖1 - Ud d a a‖ := by
                  rw [Fin.sum_const, nsmul_eq_mul]
    _ = ∑ k : Fin d, ‖1 - Ud d k k‖ := by
          rw [← mul_assoc, inv_mul_cancel₀ hd_neR, one_mul]

/-- Each phase difference contributes the corresponding sine term. -/
theorem norm_one_sub_ud_eq_sin (d : ℕ) [Fact (1 < d)] (k : Fin d) :
    ‖1 - Ud d k k‖ = 2 * Real.sin (Real.pi * (k : ℝ) / d) := by
  have hd_pos : 0 < d := lt_trans Nat.zero_lt_one ‹Fact (1 < d)›.out
  have hnorm := Complex.norm_exp_I_mul_ofReal_sub_one ((2 * Real.pi * (k : ℝ)) / d)
  have hsin_nonneg : 0 ≤ Real.sin (Real.pi * (k : ℝ) / d) := by
    apply Real.sin_nonneg_of_nonneg_of_le_pi
    · positivity
    · have hk_lt : (k : ℝ) < d := by
        exact_mod_cast k.is_lt
      have hk_le : (k : ℝ) ≤ d := le_of_lt hk_lt
      have hd_posR : (0 : ℝ) < d := by
        exact_mod_cast hd_pos
      have hdiv_le : (k : ℝ) / d ≤ 1 := by
        rw [div_le_iff₀ hd_posR]
        linarith
      have harg_le : Real.pi * (k : ℝ) / d ≤ Real.pi := by
        have htmp : Real.pi * ((k : ℝ) / d) ≤ Real.pi := by
          nlinarith [Real.pi_pos, hdiv_le]
        simpa [div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using htmp
      exact harg_le
  calc
    ‖1 - Ud d k k‖ = ‖Ud d k k - 1‖ := by
      rw [norm_sub_rev]
    _ = ‖2 * Real.sin (((2 * Real.pi * (k : ℝ)) / d) / 2)‖ := by
      simpa [Ud, div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using hnorm
    _ = ‖2 * Real.sin (Real.pi * (k : ℝ) / d)‖ := by
      congr 2
      have hd_ne : (d : ℝ) ≠ 0 := by
        exact_mod_cast hd_pos.ne'
      field_simp [hd_ne]
    _ = 2 * Real.sin (Real.pi * (k : ℝ) / d) := by
      rw [Real.norm_eq_abs, abs_of_nonneg]
      exact mul_nonneg (by positivity) hsin_nonneg

/-- Telescoping evaluation of the shifted finite sine sum. -/
theorem shifted_sine_sum_eq_cot (d : ℕ) [Fact (1 < d)] :
    (∑ k ∈ Finset.range (d - 1), Real.sin (Real.pi * (k + 1) / d)) =
      Real.cot (Real.pi / (2 * d)) := by
  have hd_pos : 0 < d := lt_trans Nat.zero_lt_one ‹Fact (1 < d)›.out
  have hd_ne : (d : ℝ) ≠ 0 := by
    exact_mod_cast hd_pos.ne'
  let g : ℕ → ℝ := fun k => Real.cos (Real.pi * (2 * k + 1) / (2 * d))
  have htel :
      (2 * Real.sin (Real.pi / (2 * d))) *
        (∑ k ∈ Finset.range (d - 1), Real.sin (Real.pi * (k + 1) / d)) =
      ∑ k ∈ Finset.range (d - 1), (g k - g (k + 1)) := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl ?_
    intro k hk
    dsimp [g]
    have h := Real.two_mul_sin_mul_sin (Real.pi / (2 * d)) (Real.pi * (k + 1) / d)
    have harg1 :
        Real.pi / (2 * d) - Real.pi * (k + 1) / d =
          -(Real.pi * (2 * k + 1) / (2 * d)) := by
      field_simp [hd_ne]
      ring
    have harg2 :
        Real.pi / (2 * d) + Real.pi * (k + 1) / d =
          Real.pi * (2 * ↑(k + 1) + 1) / (2 * d) := by
      field_simp [hd_ne]
      norm_num [Nat.cast_add, Nat.cast_mul]
      ring
    calc
      2 * Real.sin (Real.pi / (2 * d)) * Real.sin (Real.pi * (k + 1) / d)
        = Real.cos (Real.pi / (2 * d) - Real.pi * (k + 1) / d) -
            Real.cos (Real.pi / (2 * d) + Real.pi * (k + 1) / d) := h
      _ = Real.cos (Real.pi * (2 * k + 1) / (2 * d)) -
            Real.cos (Real.pi * (2 * ↑(k + 1) + 1) / (2 * d)) := by
            rw [harg1, Real.cos_neg, harg2]
  have hsum :
      ∑ k ∈ Finset.range (d - 1), (g k - g (k + 1)) = g 0 - g (d - 1) := by
    simpa using (Finset.sum_range_sub' g (d - 1))
  have hend : g 0 - g (d - 1) = 2 * Real.cos (Real.pi / (2 * d)) := by
    dsimp [g]
    have h0 : Real.pi * (2 * (0 : ℕ) + 1) / (2 * d) = Real.pi / (2 * d) := by
      ring
    have hd_le : 1 ≤ d := Nat.succ_le_of_lt hd_pos
    have harg : Real.pi * (2 * ↑(d - 1) + 1) / (2 * d) = Real.pi - Real.pi / (2 * d) := by
      field_simp [hd_ne]
      norm_num [Nat.cast_sub hd_le, Nat.cast_mul, Nat.cast_add]
      ring
    rw [h0, harg, Real.cos_pi_sub]
    ring
  have hsin_pos : 0 < Real.sin (Real.pi / (2 * d)) := by
    apply Real.sin_pos_of_pos_of_lt_pi
    · positivity
    · have hd_gt_one : (1 : ℝ) < d := by
        exact_mod_cast ‹Fact (1 < d)›.out
      have htwo_d_gt_one : (1 : ℝ) < 2 * d := by
        nlinarith
      have hpos : (0 : ℝ) < 2 * d := by
        positivity
      rw [div_lt_iff₀ hpos]
      nlinarith [Real.pi_pos, htwo_d_gt_one]
  have hmain :
      (2 * Real.sin (Real.pi / (2 * d))) *
        (∑ k ∈ Finset.range (d - 1), Real.sin (Real.pi * (k + 1) / d)) =
      2 * Real.cos (Real.pi / (2 * d)) := by
    rw [htel, hsum, hend]
  rw [Real.cot_eq_cos_div_sin]
  apply (eq_div_iff hsin_pos.ne').2
  nlinarith [hmain]

/-- The one-dimensional phase sum evaluates to the cotangent expression in Eq. (7). -/
theorem norm_one_sub_ud_sum_eq_cot (d : ℕ) [Fact (1 < d)] :
    (∑ k : Fin d, ‖1 - Ud d k k‖) = 2 * Real.cot (Real.pi / (2 * d)) := by
  calc
    (∑ k : Fin d, ‖1 - Ud d k k‖)
      = ∑ k : Fin d, 2 * Real.sin (Real.pi * (k : ℝ) / d) := by
          refine Finset.sum_congr rfl ?_
          intro k hk
          exact norm_one_sub_ud_eq_sin d k
    _ = ∑ k ∈ Finset.range d, 2 * Real.sin (Real.pi * k / d) := by
          simpa using (Fin.sum_univ_eq_sum_range (fun k => 2 * Real.sin (Real.pi * k / d)) d)
    _ = 2 * Real.cot (Real.pi / (2 * d)) := by
          have hd_pos : 0 < d := lt_trans Nat.zero_lt_one ‹Fact (1 < d)›.out
          have hd_eq : d = (d - 1) + 1 := by
            simpa [Nat.succ_eq_add_one, Nat.add_comm] using
              (Nat.succ_pred_eq_of_pos hd_pos).symm
          have hd_eqR : (((d - 1 : ℕ) : ℝ) + 1) = d := by
            exact_mod_cast hd_eq.symm
          rw [hd_eq, Finset.sum_range_succ']
          simp only [Nat.cast_add, Nat.cast_one, CharP.cast_eq_zero, mul_zero, zero_div,
            Real.sin_zero, add_zero]
          rw [hd_eqR]
          have hs2 :
              2 * (∑ k ∈ Finset.range (d - 1), Real.sin (Real.pi * (k + 1) / d)) =
                2 * Real.cot (Real.pi / (2 * d)) := by
            nlinarith [shifted_sine_sum_eq_cot d]
          simpa [Finset.mul_sum] using hs2

/-- Exact trace-norm value of the Eq. (7) witness. -/
theorem explicit_witness_traceNorm_eq (d : ℕ) [Fact (1 < d)] :
    traceNormOp
      ((d : ℂ)⁻¹ •
        (swapMatrix d - swapMatrix d * ((Ud d)ᵀ ⊗ₖ star (Ud d)))) =
      2 * Real.cot (Real.pi / (2 * d)) := by
  rw [explicit_witness_traceNorm_eq_sum, norm_one_sub_ud_sum_eq_cot]

/-- Paper Eq. (7): lower bound on `‖Λ_d‖⋄`. -/
theorem theorem_eq7 (d : ℕ) [Fact (1 < d)] :
    2 * Real.cot (Real.pi / (2 * (d : ℝ))) ≤ diamondOp (Lambda d) := by
  calc
    2 * Real.cot (Real.pi / (2 * (d : ℝ)))
      = traceNormOp
          ((d : ℂ)⁻¹ •
            (swapMatrix d - swapMatrix d * ((Ud d)ᵀ ⊗ₖ star (Ud d)))) := by
              symm
              exact explicit_witness_traceNorm_eq d
    _ ≤ diamondOp (Lambda d) := theorem_eq7_witness_bound_explicit d

end
end Diamond
