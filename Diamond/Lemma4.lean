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

/-- Trace equals the trace of the left partial trace. -/
theorem trace_eq_trace_partialTraceLeft
    {d k : Type u} [Fintype d] [DecidableEq d] [Fintype k] [DecidableEq k]
    (X : Matrix (d × k) (d × k) ℂ) :
    Matrix.trace X = Matrix.trace (partialTraceLeft d k X) := by
  calc
    Matrix.trace X = ∑ a : d, ∑ i : k, X (a, i) (a, i) := by
      simp [Matrix.trace, Fintype.sum_prod_type]
    _ = ∑ i : k, ∑ a : d, X (a, i) (a, i) := by
      simpa using
        (Finset.sum_comm
          (s := (Finset.univ : Finset d))
          (t := (Finset.univ : Finset k))
          (f := fun a i => X (a, i) (a, i)))
    _ = Matrix.trace (partialTraceLeft d k X) := by
      simp [partialTraceLeft, Matrix.trace]

/-- Tensoring a trace-annihilating map with the identity yields zero partial trace. -/
theorem partialTraceLeft_tensor_zero
    {d k : Type u} [Fintype d] [DecidableEq d] [Fintype k] [DecidableEq k]
    (Ψ : Channel d) (hT : IsTraceAnnihilating Ψ)
    (Z : Matrix (d × k) (d × k) ℂ) :
    partialTraceLeft d k (tensorWithIdentity d k Ψ Z) = 0 := by
  ext i j
  have htrace :
      Matrix.trace (Ψ (fun a b : d => Z (a, i) (b, j))) = 0 :=
    hT _
  simpa [partialTraceLeft, tensorWithIdentity, Matrix.trace] using htrace

/-- Tensoring a trace-annihilating map with the identity yields a traceless output. -/
theorem tensorWithIdentity_trace_zero
    {d k : Type u} [Fintype d] [DecidableEq d] [Fintype k] [DecidableEq k]
    (Ψ : Channel d) (hT : IsTraceAnnihilating Ψ)
    (Z : Matrix (d × k) (d × k) ℂ) :
    Matrix.trace (tensorWithIdentity d k Ψ Z) = 0 := by
  rw [trace_eq_trace_partialTraceLeft]
  simpa using
    congrArg Matrix.trace (partialTraceLeft_tensor_zero (d := d) (k := k) Ψ hT Z)

/-- Tensoring a Hermiticity-preserving map with the identity preserves Hermiticity on states. -/
theorem tensorWithIdentity_hermitian
    {d k : Type u} [Fintype d] [DecidableEq d] [Fintype k] [DecidableEq k]
    (Ψ : Channel d) (hH : IsHermiticityPreserving Ψ)
    (ρ : Matrix (d × k) (d × k) ℂ) (hρ : IsDensityState ρ) :
    Matrix.IsHermitian (tensorWithIdentity d k Ψ ρ) := by
  change (tensorWithIdentity d k Ψ ρ)ᴴ = tensorWithIdentity d k Ψ ρ
  ext p q
  let A : Matrix d d ℂ := fun i j => ρ (i, p.2) (j, q.2)
  have hρh : Matrix.IsHermitian ρ := hρ.1.isHermitian
  have hA : Aᴴ = fun i j : d => ρ (i, q.2) (j, p.2) := by
    ext i j
    simpa [A, Matrix.conjTranspose_apply] using
      congrArg (fun M => M (i, q.2) (j, p.2)) hρh.eq
  have hcomm := hH A
  have hpoint : Ψ Aᴴ q.1 p.1 = star (Ψ A p.1 q.1) := by
    simpa [Matrix.conjTranspose_apply] using congrArg (fun M => M q.1 p.1) hcomm
  have hpoint' : star (Ψ Aᴴ q.1 p.1) = Ψ A p.1 q.1 := by
    simpa using congrArg star hpoint
  simpa [A, hA, tensorWithIdentity, Matrix.conjTranspose_apply] using hpoint'

/-- Paper Lemma 4. -/
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

/-- Tracelessness of the tensor-amplified output. -/
theorem lemma4_density_trace
    {d : Type u} [Fintype d] [DecidableEq d]
    (T : Channel d) (hT : IsQuantumChannel T)
    (ρ : Matrix (d × d) (d × d) ℂ) (_hρ : IsDensityState ρ) :
    Matrix.trace (tensorWithIdentity d d (idMinus T) ρ) = 0 := by
  rw [trace_eq_trace_partialTraceLeft]
  calc
    Matrix.trace (partialTraceLeft d d (tensorWithIdentity d d (idMinus T) ρ))
      = Matrix.trace (0 : Matrix d d ℂ) := by
          congr 1
          ext i j
          calc
            partialTraceLeft d d (tensorWithIdentity d d (idMinus T) ρ) i j
              = partialTraceLeft d d ρ i j -
                  partialTraceLeft d d (tensorWithIdentity d d T ρ) i j := by
                    simp [partialTraceLeft, tensorWithIdentity, idMinus, Finset.sum_sub_distrib]
            _ = 0 := by
                    rw [lemma4 T hT ρ]
                    ring
    _ = 0 := by simp

/-- Hermiticity of the tensor-amplified output. -/
theorem lemma4_density_hermitian
    {d : Type u} [Fintype d] [DecidableEq d]
    (T : Channel d) (hT : IsQuantumChannel T)
    (ρ : Matrix (d × d) (d × d) ℂ) (hρ : IsDensityState ρ) :
    Matrix.IsHermitian (tensorWithIdentity d d (idMinus T) ρ) := by
  exact tensorWithIdentity_hermitian (d := d) (k := d)
    (Ψ := idMinus T) (idMinus_isHermiticityPreserving T hT) ρ hρ

end
end Diamond
