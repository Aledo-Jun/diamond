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
  obtain ⟨r, E, hmap, hcomplete⟩ := quantumChannel_has_kraus (T := T) hT
  ext i j
  let A : Matrix d d ℂ := fun a b => Z (a, i) (b, j)
  calc
    partialTraceLeft d k (tensorWithIdentity d k T Z) i j = Matrix.trace (T A) := by
      simp [partialTraceLeft, tensorWithIdentity, A, Matrix.trace]
    _ = Matrix.trace (∑ n : Fin r, E n * A * (E n)ᴴ) := by
      simp [hmap]
    _ = ∑ n : Fin r, Matrix.trace (E n * A * (E n)ᴴ) := by
      simpa using (Matrix.trace_sum (s := (Finset.univ : Finset (Fin r)))
        (f := fun n => E n * A * (E n)ᴴ))
    _ = ∑ n : Fin r, Matrix.trace (A * ((E n)ᴴ * E n)) := by
      refine Finset.sum_congr rfl ?_
      intro n hn
      calc
        Matrix.trace (E n * A * (E n)ᴴ)
            = Matrix.trace (((E n)ᴴ * E n) * A) := by
              simpa [Matrix.mul_assoc] using (Matrix.trace_mul_cycle (E n) A (E n)ᴴ)
        _ = Matrix.trace (A * ((E n)ᴴ * E n)) := by
              simpa [Matrix.mul_assoc] using (Matrix.trace_mul_comm ((E n)ᴴ * E n) A)
    _ = Matrix.trace (∑ n : Fin r, A * ((E n)ᴴ * E n)) := by
      simpa using
        (Matrix.trace_sum (s := (Finset.univ : Finset (Fin r))
          )
          (f := fun n => A * ((E n)ᴴ * E n))).symm
    _ = Matrix.trace (A * (∑ n : Fin r, (E n)ᴴ * E n)) := by
      simp [Matrix.mul_sum]
    _ = Matrix.trace (A * 1) := by
      rw [hcomplete]
    _ = partialTraceLeft d k Z i j := by
      simp [A, partialTraceLeft, Matrix.trace]

end

end
end Diamond
