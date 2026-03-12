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

/-- Lemma 3: partial transpose preserves the Hilbert--Schmidt norm. -/
theorem lemma3
    {d k : Type u} [Fintype d] [DecidableEq d] [Fintype k] [DecidableEq k]
    (X : Matrix (d × k) (d × k) ℂ) :
    hsNormOp (partialTransposeMap d k X) = hsNormOp X := by
  change ‖partialTransposeMap d k X‖ = ‖X‖
  let e : (d × k) × (d × k) ≃ (d × k) × (d × k) :=
    { toFun := fun p => ((p.2.1, p.1.2), (p.1.1, p.2.2))
      invFun := fun p => ((p.2.1, p.1.2), (p.1.1, p.2.2))
      left_inv := by
        intro p
        aesop
      right_inv := by
        intro p
        aesop }
  have hEq :
      (∑ p : (d × k) × (d × k), ‖X (e p).1 (e p).2‖ ^ (2 : ℝ)) =
        ∑ p : (d × k) × (d × k), ‖X p.1 p.2‖ ^ (2 : ℝ) := by
    exact Equiv.sum_comp e (g := fun p => ‖X p.1 p.2‖ ^ (2 : ℝ))
  calc
    ‖partialTransposeMap d k X‖
      = (∑ p : (d × k) × (d × k), ‖X (e p).1 (e p).2‖ ^ (2 : ℝ)) ^ (1 / 2 : ℝ) := by
          simp [partialTransposeMap, Matrix.frobenius_norm_def, e, Fintype.sum_prod_type]
    _ = (∑ p : (d × k) × (d × k), ‖X p.1 p.2‖ ^ (2 : ℝ)) ^ (1 / 2 : ℝ) := by
          rw [hEq]
    _ = ‖X‖ := by
          simp [Matrix.frobenius_norm_def, Fintype.sum_prod_type]

end
end Diamond
