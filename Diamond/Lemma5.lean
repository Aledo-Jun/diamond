import Diamond.Setups

open scoped BigOperators
open scoped ComplexOrder
open scoped Kronecker
open scoped MatrixOrder
open scoped Matrix.Norms.Frobenius
open Matrix

namespace Diamond

noncomputable section

/-- Paper Definition 1: column-major vectorization with tensor indices ordered as in the paper. -/
def vecKet (d : ℕ) (A : Matrix (Fin d) (Fin d) ℂ) : Fin d × Fin d → ℂ :=
  Matrix.vec Aᵀ

@[simp]
theorem vecKet_apply (d : ℕ) (A : Matrix (Fin d) (Fin d) ℂ) (i j : Fin d) :
    vecKet d A (i, j) = A i j := by
  rfl

-- Paper: Lemma 5
theorem lemma5 (d : ℕ)
    (M A N : Matrix (Fin d) (Fin d) ℂ) :
    (M ⊗ₖ N) *ᵥ vecKet d A = vecKet d (M * A * Nᵀ) := by
  change (M ⊗ₖ N) *ᵥ Matrix.vec Aᵀ = Matrix.vec ((M * A * Nᵀ)ᵀ)
  rw [Matrix.kronecker_mulVec_vec]
  simp [Matrix.transpose_mul, Matrix.mul_assoc]

end

end Diamond
