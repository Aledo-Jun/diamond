import Mathlib
import Mathlib.Tactic
import Mathlib.LinearAlgebra.Matrix.Vec

open scoped BigOperators
open scoped Kronecker
open Matrix

namespace Diamond

universe u

noncomputable section

-- Paper: Setup and notation
/-- Matrix representation of linear operators on a finite-dimensional `d`-index space. -/
abbrev Operator (d : Type u) [Fintype d] [DecidableEq d] := Matrix d d ℂ

/-- Linear map acting on operators. -/
abbrev Channel (d : Type u) [Fintype d] [DecidableEq d] :=
  Operator d →ₗ[ℂ] Operator d

/-- Abstract trace norm symbol used by the document (`‖·‖₁`). -/
axiom traceNorm
    {m n : Type u} [Fintype m] [DecidableEq m] [Fintype n] [DecidableEq n]
    (X : Matrix m n ℂ) : ℝ

/-- Abstract Hilbert–Schmidt norm symbol used by the document (`‖·‖₂`). -/
axiom hsNorm
    {m n : Type u} [Fintype m] [DecidableEq m] [Fintype n] [DecidableEq n]
    (X : Matrix m n ℂ) : ℝ

/-- Abstract diamond norm symbol for linear maps (`‖·‖⋄`). -/
axiom diamondNorm
    {d : Type u} [Fintype d] [DecidableEq d] (Φ : Channel d) : ℝ

abbrev traceNormOp
    {m n : Type u} [Fintype m] [DecidableEq m] [Fintype n] [DecidableEq n]
    (X : Matrix m n ℂ) : ℝ := traceNorm X

abbrev hsNormOp
    {m n : Type u} [Fintype m] [DecidableEq m] [Fintype n] [DecidableEq n]
    (X : Matrix m n ℂ) : ℝ := hsNorm X

abbrev diamondOp
    {d : Type u} [Fintype d] [DecidableEq d] (Φ : Channel d) : ℝ := diamondNorm Φ

axiom IsDensityState {d : Type u} [Fintype d] [DecidableEq d] (ρ : Matrix d d ℂ) : Prop
axiom IsQuantumChannel {d : Type u} [Fintype d] [DecidableEq d] (Φ : Channel d) : Prop
axiom IsHermiticityPreserving {d : Type u} [Fintype d] [DecidableEq d]
    (Φ : Channel d) : Prop
axiom IsTraceAnnihilating {d : Type u} [Fintype d] [DecidableEq d]
    (Φ : Channel d) : Prop

/-- ### Primitive map constructors for the abstract interface. -/
axiom transposeMap (d : Type u) [Fintype d] [DecidableEq d] : Channel d
axiom tensorWithIdentity
    (d k : Type u) [Fintype d] [DecidableEq d] [Fintype k] [DecidableEq k]
    (Φ : Channel d) : Channel (d × k)
axiom partialTransposeMap
    (d k : Type u) [Fintype d] [DecidableEq d] [Fintype k] [DecidableEq k]
    : Channel (d × k)
axiom tensorWithIdentity_diamond
    {d k : Type u} [Fintype d] [DecidableEq d] [Fintype k] [DecidableEq k]
    (Φ : Channel d) : diamondOp (tensorWithIdentity d k Φ) = diamondOp Φ
axiom partialTraceLeft
    (d k : Type u) [Fintype d] [DecidableEq d] [Fintype k] [DecidableEq k]
    (X : Matrix (d × k) (d × k) ℂ) : Matrix k k ℂ
axiom adMap (d : Type u) [Fintype d] [DecidableEq d]
    (U : Matrix d d ℂ) : Channel d

axiom Ud (d : ℕ) [Fact (1 < d)] : Matrix (Fin d) (Fin d) ℂ

def idMinus
    {d : Type u} [Fintype d] [DecidableEq d] (Φ : Channel d) : Channel d :=
  {
    toFun := fun X => X - Φ X
    map_add' := by
      intro X Y
      ext i j
      simp [sub_eq_add_neg, add_assoc, add_left_comm, add_comm, map_add]
    map_smul' := by
      intro c X
      ext i j
      simp [sub_eq_add_neg, mul_add, smul_eq_mul]
  }

def Lambda (d : ℕ) [Fact (1 < d)] : Channel (Fin d) :=
  (transposeMap (Fin d)).comp (idMinus (adMap (Fin d) (Ud d)))

/-- ### Axioms matching the paper’s analytic ingredients. -/
axiom trNorm_nonneg
    {m n : Type u} [Fintype m] [DecidableEq m] [Fintype n] [DecidableEq n]
    (X : Matrix m n ℂ) : 0 ≤ traceNormOp X

axiom hsNorm_nonneg
    {m n : Type u} [Fintype m] [DecidableEq m] [Fintype n] [DecidableEq n]
    (X : Matrix m n ℂ) : 0 ≤ hsNormOp X

/-- Paper Lemma 1. -/
axiom lemma1
    {d : Type u} [Fintype d] [DecidableEq d]
    (X : Matrix d d ℂ) (hX : Matrix.IsHermitian X) (ht : Matrix.trace X = 0) :
    hsNormOp X ≤ (1 / Real.sqrt 2) * traceNormOp X

/-- Paper Lemma 2. -/
-- Paper: Lemma 2.
axiom lemma2
    {ι : Type u} [Fintype ι] [DecidableEq ι]
    (X : Matrix ι ι ℂ) :
    traceNormOp X ≤ Real.sqrt (Fintype.card ι : ℝ) * hsNormOp X

/-- Paper Lemma 3 (`HS`-norm invariance under partial transpose). -/
-- Paper: Lemma 3.
axiom lemma3
    {d k : Type u} [Fintype d] [DecidableEq d] [Fintype k] [DecidableEq k]
    (X : Matrix (d × k) (d × k) ℂ) :
    hsNormOp (partialTransposeMap d k X) = hsNormOp X

/-- Paper statement `‖Θ‖⋄ = d`. -/
-- Paper: `‖Θ‖⋄ = d`.
axiom lemma_transpose_diamond
    (d : Type u) [Fintype d] [DecidableEq d] :
    diamondOp (transposeMap d) = (Fintype.card d : ℝ)

/-- Pointwise-to-supremum transfer for the chosen `diamondNorm` abstraction. -/
-- Paper: pointwise-to-supremum transfer.
axiom diamond_le_of_pointwise
    {d : Type u} [Fintype d] [DecidableEq d] (Φ : Channel d)
    (C : ℝ) : (∀ ρ : Matrix d d ℂ, IsDensityState ρ → traceNormOp (Φ ρ) ≤ C) →
    diamondOp Φ ≤ C

/-- Basic pointwise bound used in the norm chain. -/
-- Paper: diamond norm pointwise bound.
axiom traceNorm_apply_le_diamond
    {d : Type u} [Fintype d] [DecidableEq d] (Φ : Channel d) (ρ : Matrix d d ℂ) :
    traceNormOp (Φ ρ) ≤ diamondOp Φ

/-- Paper Corollary 1 input for the trace argument. -/
-- Paper: Lemma 4.
axiom lemma4
    {d : Type u} [Fintype d] [DecidableEq d]
    (T : Channel d) (hT : IsQuantumChannel T)
    (Z : Matrix (d × d) (d × d) ℂ) :
    partialTraceLeft d d (tensorWithIdentity d d (idMinus T) Z) = 0

/-- Paper Lemma 4 (trace-vanishing input under channel tensoring). -/
-- Paper: Corollary 1 helper (`trace`).
axiom lemma4_density_trace
    {d : Type u} [Fintype d] [DecidableEq d]
    (T : Channel d) (hT : IsQuantumChannel T)
    (ρ : Matrix (d × d) (d × d) ℂ) (hρ : IsDensityState ρ) :
    Matrix.trace (tensorWithIdentity d d (idMinus T) ρ) = 0

/-- Paper Lemma 4 (Hermitian input for the pointwise bound). -/
-- Paper: Corollary 1 helper (Hermitian).
axiom lemma4_density_hermitian
    {d : Type u} [Fintype d] [DecidableEq d]
    (T : Channel d) (hT : IsQuantumChannel T)
    (ρ : Matrix (d × d) (d × d) ℂ) (hρ : IsDensityState ρ) :
    Matrix.IsHermitian (tensorWithIdentity d d (idMinus T) ρ)

/-- Paper Lemma 5 (vectorization identity). -/
theorem lemma5
    {m n : Type u} [Fintype m] [DecidableEq m] [Fintype n] [DecidableEq n]
    (M : Matrix m m ℂ) (X : Matrix m n ℂ) (N : Matrix n n ℂ) :
    (N ⊗ₖ M) *ᵥ Matrix.vec X = Matrix.vec (M * X * Nᵀ) := by
  simpa using Matrix.kronecker_mulVec_vec M X N

/-- Paper Lemma 6 (swap of Kronecker factors). -/
theorem lemma6
    {m : Type u} [Fintype m] [DecidableEq m]
    (M : Matrix m m ℂ) (N : Matrix m m ℂ) :
    (M ⊗ₖ N) * ((Equiv.prodComm (α := m) (β := m)).toPEquiv.toMatrix : Matrix (m × m) (m × m) ℂ) =
      ((Equiv.prodComm (α := m) (β := m)).toPEquiv.toMatrix : Matrix (m × m) (m × m) ℂ) * (N ⊗ₖ M) := by
  let σ : (m × m) ≃ (m × m) := Equiv.prodComm (α := m) (β := m)
  let P : Matrix (m × m) (m × m) ℂ := (σ.toPEquiv.toMatrix : Matrix (m × m) (m × m) ℂ)
  have hL : (M ⊗ₖ N) * P = (M ⊗ₖ N).submatrix id (σ.symm) := by
    simpa [P, σ] using
      (PEquiv.mul_toMatrix_toPEquiv (M := (M ⊗ₖ N)) (f := σ))
  have hR : P * (N ⊗ₖ M) = (N ⊗ₖ M).submatrix σ id := by
    simpa [P, σ] using
      (PEquiv.toMatrix_toPEquiv_mul (f := σ) (M := (N ⊗ₖ M)))
  rw [hL, hR]
  ext i j
  rcases i with ⟨i₁, i₂⟩
  rcases j with ⟨j₁, j₂⟩
  simp [σ, Matrix.submatrix_apply, Matrix.kroneckerMap_apply, mul_comm]

/-- Paper Lemma 7 (partial transpose on rank-one vectorized operator). -/
-- Paper: Lemma 7.
axiom lemma7
    {m : Type u} [Fintype m] [DecidableEq m]
    (A B : Matrix m m ℂ) :
    partialTransposeMap m m (Matrix.vecMulVec (Matrix.vec A) (Matrix.vec B)) =
      ((1 : Matrix m m ℂ) ⊗ₖ Aᵀ) *
        ((Equiv.prodComm (α := m) (β := m)).toPEquiv.toMatrix : Matrix (m × m) (m × m) ℂ) *
          ((1 : Matrix m m ℂ) ⊗ₖ Bᴴ)

/-- Paper Theorem 1. -/
theorem theorem1
    {d : Type u} [Fintype d] [DecidableEq d]
    (T : Channel d) (hT : IsQuantumChannel T) :
    diamondOp ((partialTransposeMap d d).comp (tensorWithIdentity d d (idMinus T))) ≤
      (1 / Real.sqrt 2) * diamondOp (transposeMap d) * diamondOp (idMinus T) := by
  let Ψ : Channel (d × d) := (partialTransposeMap d d).comp (tensorWithIdentity d d (idMinus T))
  refine diamond_le_of_pointwise Ψ ((1 / Real.sqrt 2) * diamondOp (transposeMap d) * diamondOp (idMinus T)) ?_
  intro ρ hρ
  let Mρ : Matrix (d × d) (d × d) ℂ := tensorWithIdentity d d (idMinus T) ρ
  have hTrace : Matrix.trace Mρ = 0 := by
    simpa [Mρ] using lemma4_density_trace (d := d) T hT ρ hρ
  have hHerm : Matrix.IsHermitian Mρ := by
    simpa [Mρ] using lemma4_density_hermitian (d := d) T hT ρ hρ
  have hbound2 : hsNormOp (partialTransposeMap d d Mρ) = hsNormOp Mρ :=
    lemma3 (d := d) (k := d) Mρ
  have hbound1 :
      traceNormOp (Ψ ρ) ≤ Real.sqrt (Fintype.card (d × d) : ℝ) * hsNormOp Mρ := by
    simpa [Ψ, LinearMap.comp_apply, Mρ, hbound2] using
      (lemma2 (ι := d × d) (X := partialTransposeMap d d Mρ))
  have hlemma1 : hsNormOp Mρ ≤ (1 / Real.sqrt 2) * traceNormOp Mρ :=
    lemma1 Mρ hHerm hTrace
  have htraceBound : traceNormOp Mρ ≤ diamondOp (tensorWithIdentity d d (idMinus T)) := by
    simpa [Mρ] using
      (traceNorm_apply_le_diamond (d := d × d) (Φ := tensorWithIdentity d d (idMinus T)) (ρ := ρ))
  have hhs : hsNormOp Mρ ≤ (1 / Real.sqrt 2) * diamondOp (tensorWithIdentity d d (idMinus T)) := by
    calc
      hsNormOp Mρ ≤ (1 / Real.sqrt 2) * traceNormOp Mρ := hlemma1
      _ ≤ (1 / Real.sqrt 2) * diamondOp (tensorWithIdentity d d (idMinus T)) := by
        exact mul_le_mul_of_nonneg_left htraceBound (by positivity)
  have hfinal1 : traceNormOp (Ψ ρ) ≤
      Real.sqrt (Fintype.card (d × d) : ℝ) *
        ((1 / Real.sqrt 2) * diamondOp (tensorWithIdentity d d (idMinus T))) := by
    exact le_trans hbound1 (mul_le_mul_of_nonneg_left hhs (Real.sqrt_nonneg _))
  have hsqrt : Real.sqrt (Fintype.card (d × d) : ℝ) = diamondOp (transposeMap d) := by
    rw [lemma_transpose_diamond (d := d)]
    have hcard : (Fintype.card (d × d) : ℝ) = (Fintype.card d : ℝ) * (Fintype.card d : ℝ) := by
      simp [Fintype.card_prod, Nat.cast_mul]
    rw [hcard]
    have hsquare : (Fintype.card d : ℝ) * (Fintype.card d : ℝ) = (Fintype.card d : ℝ) ^ 2 := by
      ring
    rw [hsquare, Real.sqrt_sq_eq_abs, abs_of_nonneg (Nat.cast_nonneg _)]
  have hfinal2 : traceNormOp (Ψ ρ) ≤
      (1 / Real.sqrt 2) * diamondOp (transposeMap d) * diamondOp (tensorWithIdentity d d (idMinus T)) := by
    calc
      traceNormOp (Ψ ρ) ≤ Real.sqrt (Fintype.card (d × d) : ℝ) *
          ((1 / Real.sqrt 2) * diamondOp (tensorWithIdentity d d (idMinus T))) := hfinal1
      _ = (1 / Real.sqrt 2) * diamondOp (transposeMap d) * diamondOp (tensorWithIdentity d d (idMinus T)) := by
        rw [hsqrt, mul_assoc]
        ring_nf
  have htensor : diamondOp (tensorWithIdentity d d (idMinus T)) = diamondOp (idMinus T) := by
    exact tensorWithIdentity_diamond (d := d) (k := d) (Φ := idMinus T)
  have hfinal3 : traceNormOp (Ψ ρ) ≤
      (1 / Real.sqrt 2) * diamondOp (transposeMap d) * diamondOp (idMinus T) := by
    simpa [htensor, mul_assoc, mul_left_comm, mul_comm] using hfinal2
  exact hfinal3

/-- Paper Remark 1 (general Hermiticity-preserving, trace-annihilating bound). -/
axiom remark1
    {d : Type u} [Fintype d] [DecidableEq d]
    (Ψ : Channel d) (hH : IsHermiticityPreserving Ψ) (hT : IsTraceAnnihilating Ψ) :
    diamondOp ((partialTransposeMap d d).comp (tensorWithIdentity d d Ψ)) ≤
      (1 / Real.sqrt 2) * diamondOp (transposeMap d) * diamondOp Ψ

/-- Paper Corollary 1 is obtained directly by taking `Φ = 1 - T`. -/
theorem corollary1
    {d : Type u} [Fintype d] [DecidableEq d]
    (T : Channel d) (hT : IsQuantumChannel T)
    (ρ : Matrix (d × d) (d × d) ℂ) :
    partialTraceLeft d d (tensorWithIdentity d d (idMinus T) ρ) = 0 :=
  lemma4 (d := d) T hT ρ

/-- Paper Eq. (7): lower bound on `‖Λ_d‖⋄`. -/
axiom theorem_eq7 (d : ℕ) [Fact (1 < d)] :
    2 * Real.cot (Real.pi / (2 * (d : ℝ))) ≤ diamondOp (Lambda d)

/-- Paper Eq. (8): unitary channel gap. -/
axiom theorem_eq8 (d : ℕ) [Fact (1 < d)] :
    diamondOp (idMinus (adMap (Fin d) (Ud d))) = 2

/-- Paper Corollary 2 (finite-error Holevo–Werner bound). -/
axiom corollary2
    {d : Type u} [Fintype d] [DecidableEq d] (T : Channel d) (m : ℕ) (msgDim : ℕ) (ε : ℝ) :
    ε < 1 / Real.sqrt 2 →
    Real.logb 2 (msgDim : ℝ) ≤
      Real.logb 2 (diamondOp ((transposeMap d).comp T)) +
        (1 / (m : ℝ)) * Real.logb 2 (1 / (1 - Real.sqrt 2 * ε))

end

end Diamond
