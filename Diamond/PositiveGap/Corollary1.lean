import Diamond.Setups
import Diamond.PositiveGap.Lemma4

open scoped BigOperators
open scoped ComplexOrder
open scoped Kronecker
open scoped MatrixOrder
open scoped Matrix.Norms.Frobenius
open Matrix

namespace Diamond

universe u
noncomputable section

/-- Paper Corollary 1. -/
theorem corollary1
    {d : Type u} [Fintype d] [DecidableEq d]
    (T : Channel d) (hT : IsQuantumChannel T)
    (ρ : Matrix (d × d) (d × d) ℂ) :
    partialTraceLeft d d (tensorWithIdentity d d (idMinus T) ρ) = 0 := by
  ext i j
  calc
    partialTraceLeft d d (tensorWithIdentity d d (idMinus T) ρ) i j
      = partialTraceLeft d d ρ i j -
          partialTraceLeft d d (tensorWithIdentity d d T ρ) i j := by
            simp [partialTraceLeft, tensorWithIdentity, idMinus, Finset.sum_sub_distrib]
    _ = 0 := by
          rw [lemma4 T hT ρ]
          ring

end
end Diamond
