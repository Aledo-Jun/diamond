import Diamond.Setups
import Diamond.StandardFacts

open scoped BigOperators
open scoped ComplexOrder
open scoped Kronecker
open scoped MatrixOrder
open scoped Matrix.Norms.Frobenius
open Matrix

namespace Diamond

universe u

noncomputable section

section

set_option linter.unnecessarySimpa false

/-- Paper Lemma 4: partial trace on the left is unchanged by tensoring with a quantum channel. -/
theorem lemma4
    {d : Type u} [Fintype d] [DecidableEq d]
    (T : Channel d) (hT : IsQuantumChannel T)
    {k : Type u} [Fintype k] [DecidableEq k]
    (Z : Matrix (d × k) (d × k) ℂ) :
    partialTraceLeft d k (tensorWithIdentity d k T Z) = partialTraceLeft d k Z := by
  ext i j
  let A : Matrix d d ℂ := fun a b => Z (a, i) (b, j)
  calc
    partialTraceLeft d k (tensorWithIdentity d k T Z) i j = Matrix.trace (T A) := by
      simp [partialTraceLeft, tensorWithIdentity, A, Matrix.trace]
    _ = Matrix.trace A := hT.trace_preserving A
    _ = partialTraceLeft d k Z i j := by
      simp [A, partialTraceLeft, Matrix.trace]

end

end
end Diamond
