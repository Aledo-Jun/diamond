import Diamond.Lemma5
import Diamond.Lemma6

open scoped BigOperators
open scoped ComplexOrder
open scoped Kronecker
open scoped MatrixOrder
open scoped Matrix.Norms.Frobenius
open Matrix

namespace Diamond

noncomputable section

theorem oneKronecker_mul_swap_apply (d : ℕ)
    (A : Matrix (Fin d) (Fin d) ℂ) (a b c e : Fin d) :
    (((1 : Matrix (Fin d) (Fin d) ℂ) ⊗ₖ A) * swapMatrix d) (a, b) (c, e) =
      if a = e then A b c else 0 := by
  rw [Matrix.mul_apply]
  rw [Finset.sum_eq_single (e, c)]
  · simp [swapMatrix, Matrix.kroneckerMap_apply, Matrix.one_apply]
  · intro x _ hx
    have hzero : ¬ (x.1 = e ∧ x.2 = c) := by
      intro h
      apply hx
      ext <;> simp [h.1, h.2]
    simp [swapMatrix, Matrix.kroneckerMap_apply, Matrix.one_apply, hzero]
  · intro hec
    simp at hec

-- Paper: Lemma 7
theorem lemma7 (d : ℕ)
    (A B : Matrix (Fin d) (Fin d) ℂ) :
    tensorWithIdentity
        (Fin d)
        (Fin d)
        (transposeMap (Fin d))
        (Matrix.vecMulVec (vecKet d A) (star (vecKet d B))) =
      (((1 : Matrix (Fin d) (Fin d) ℂ) ⊗ₖ Aᵀ) * swapMatrix d) *
        ((1 : Matrix (Fin d) (Fin d) ℂ) ⊗ₖ B.map star) := by
  ext i j
  rcases i with ⟨p, i⟩
  rcases j with ⟨q, j⟩
  have hleft :
      tensorWithIdentity
          (Fin d)
          (Fin d)
          (transposeMap (Fin d))
          (Matrix.vecMulVec (vecKet d A) (star (vecKet d B)))
          (p, i)
          (q, j) =
        A q i * star (B p j) := by
    simp [tensorWithIdentity, transposeMap, Matrix.vecMulVec_apply, vecKet]
  have hright :
      ((((1 : Matrix (Fin d) (Fin d) ℂ) ⊗ₖ Aᵀ) * swapMatrix d) *
          ((1 : Matrix (Fin d) (Fin d) ℂ) ⊗ₖ B.map star))
          (p, i)
          (q, j) =
        A q i * star (B p j) := by
    rw [Matrix.mul_apply]
    rw [Finset.sum_eq_single (q, p)]
    · simp [oneKronecker_mul_swap_apply, Matrix.kroneckerMap_apply]
    · intro x _ hx
      by_cases hx1 : x.1 = q
      · by_cases hx2 : x.2 = p
        · apply (hx <| by ext <;> simp [hx1, hx2]).elim
        · have hleftzero :
              (((1 : Matrix (Fin d) (Fin d) ℂ) ⊗ₖ Aᵀ) * swapMatrix d) (p, i) x = 0 := by
            rw [oneKronecker_mul_swap_apply]
            simp [show ¬ p = x.2 by simpa [eq_comm] using hx2]
          simp [hleftzero, Matrix.kroneckerMap_apply, Matrix.one_apply, hx1]
      · have hrightzero :
            (((1 : Matrix (Fin d) (Fin d) ℂ) ⊗ₖ B.map star) x (q, j)) = 0 := by
          simp [Matrix.kroneckerMap_apply, hx1]
        rw [hrightzero]
        simp
    · intro hqp
      simp at hqp
  rw [hleft, hright]

end

end Diamond
