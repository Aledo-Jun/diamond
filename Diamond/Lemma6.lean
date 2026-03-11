import Diamond.Setups

open scoped BigOperators
open scoped ComplexOrder
open scoped Kronecker
open scoped MatrixOrder
open scoped Matrix.Norms.Frobenius
open Matrix

namespace Diamond

noncomputable section

/-- Paper Definition 2: the swap operator `F`. -/
def swapMatrix (d : ℕ) : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ :=
  fun i j => if i.1 = j.2 ∧ i.2 = j.1 then 1 else 0

theorem swapMatrix_mul_self (d : ℕ) :
    swapMatrix d * swapMatrix d = 1 := by
  ext i j
  rw [Matrix.mul_apply]
  rw [Finset.sum_eq_single (i.2, i.1)]
  · by_cases hij : i = j
    · subst hij
      simp [swapMatrix]
    · have hneq : ¬ (i.2 = j.2 ∧ i.1 = j.1) := by
        intro h
        apply hij
        cases i with
        | mk a b =>
          cases j with
          | mk c e =>
            simp only [Prod.mk.injEq] at h ⊢
            exact ⟨h.2, h.1⟩
      simp [swapMatrix, hneq, hij]
  · intro x _ hx
    have hzero : ¬ (i.1 = x.2 ∧ i.2 = x.1) := by
      intro h
      apply hx
      ext <;> simp [h.1, h.2]
    simp [swapMatrix, hzero]
  · intro hi
    simp at hi

theorem swapMatrix_conjTranspose (d : ℕ) :
    (swapMatrix d)ᴴ = swapMatrix d := by
  ext i j
  by_cases h : i.1 = j.2 ∧ i.2 = j.1
  · rcases h with ⟨h1, h2⟩
    have h' : j.1 = i.2 ∧ j.2 = i.1 := ⟨h2.symm, h1.symm⟩
    change
      star (if j.1 = i.2 ∧ j.2 = i.1 then (1 : ℂ) else 0) =
        if i.1 = j.2 ∧ i.2 = j.1 then (1 : ℂ) else 0
    simp only [if_pos h', if_pos (And.intro h1 h2), star_one]
  · have h' : ¬ (j.1 = i.2 ∧ j.2 = i.1) := by
      intro hji
      apply h
      exact ⟨hji.2.symm, hji.1.symm⟩
    change
      star (if j.1 = i.2 ∧ j.2 = i.1 then (1 : ℂ) else 0) =
        if i.1 = j.2 ∧ i.2 = j.1 then (1 : ℂ) else 0
    simp only [if_neg h', if_neg h, star_zero]

theorem swapMatrix_conjTranspose_mul_self (d : ℕ) :
    (swapMatrix d)ᴴ * swapMatrix d = 1 := by
  rw [swapMatrix_conjTranspose, swapMatrix_mul_self]

-- Paper: Lemma 6
theorem lemma6 (d : ℕ)
    (X Y : Matrix (Fin d) (Fin d) ℂ) :
    swapMatrix d * (X ⊗ₖ Y) = (Y ⊗ₖ X) * swapMatrix d := by
  ext i j
  rcases i with ⟨a, b⟩
  rcases j with ⟨c, e⟩
  have hleft :
      (swapMatrix d * (X ⊗ₖ Y)) (a, b) (c, e) = X b c * Y a e := by
    rw [Matrix.mul_apply]
    rw [Finset.sum_eq_single (b, a)]
    · simp [swapMatrix, Matrix.kroneckerMap_apply]
    · intro x _ hx
      have hzero : ¬ (a = x.2 ∧ b = x.1) := by
        intro h
        apply hx
        ext <;> simp [h.1, h.2]
      simp [swapMatrix, Matrix.kroneckerMap_apply, hzero]
    · intro hba
      simp at hba
  have hright :
      ((Y ⊗ₖ X) * swapMatrix d) (a, b) (c, e) = Y a e * X b c := by
    rw [Matrix.mul_apply]
    rw [Finset.sum_eq_single (e, c)]
    · simp [swapMatrix, Matrix.kroneckerMap_apply]
    · intro x _ hx
      have hzero : ¬ (x.1 = e ∧ x.2 = c) := by
        intro h
        apply hx
        ext <;> simp [h.1, h.2]
      simp [swapMatrix, Matrix.kroneckerMap_apply, hzero]
    · intro hec
      simp at hec
  rw [hleft, hright, mul_comm]

end

end Diamond
