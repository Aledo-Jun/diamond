import Mathlib
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.LinearAlgebra.Matrix.Hermitian
import Mathlib.Analysis.Matrix.Normed
import Mathlib.LinearAlgebra.Eigenspace.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Real.Sqrt
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Multiset.Basic

open scoped BigOperators
open scoped ComplexOrder
open scoped Kronecker
open scoped MatrixOrder
open scoped Matrix.Norms.Frobenius
open Matrix

namespace Diamond

universe u

noncomputable section

abbrev Operator (d : Type u) [Fintype d] [DecidableEq d] := Matrix d d ℂ

abbrev Channel (d : Type u) [Fintype d] [DecidableEq d] :=
  Operator d →ₗ[ℂ] Operator d

/-- Hilbert--Schmidt norm, realized by the Frobenius norm. -/
def hsNorm
    {m n : Type u} [Fintype m] [DecidableEq m] [Fintype n] [DecidableEq n]
    (X : Matrix m n ℂ) : ℝ :=
  ‖X‖

/-- Trace norm, realized as the sum of the singular values. -/
def traceNormOp
    {d : Type u} [Fintype d] [DecidableEq d] (X : Matrix d d ℂ) : ℝ :=
  ∑ i, Real.sqrt ((Matrix.isHermitian_conjTranspose_mul_self X).eigenvalues i)

abbrev hsNormOp
    {m n : Type u} [Fintype m] [DecidableEq m] [Fintype n] [DecidableEq n]
    (X : Matrix m n ℂ) : ℝ :=
  hsNorm X

def IsDensityState
    {d : Type u} [Fintype d] [DecidableEq d] (ρ : Matrix d d ℂ) : Prop :=
  Matrix.PosSemidef ρ ∧ Matrix.trace ρ = 1

abbrev DensityState (d : Type u) [Fintype d] [DecidableEq d] :=
  {ρ : Matrix d d ℂ // IsDensityState ρ}

def IsHermiticityPreserving
    {d : Type u} [Fintype d] [DecidableEq d] (Φ : Channel d) : Prop :=
  ∀ X, Φ Xᴴ = (Φ X)ᴴ

structure IsQuantumChannel
    {d : Type u} [Fintype d] [DecidableEq d] (T : Channel d) where
  krausRank : ℕ
  kraus : Fin krausRank → Matrix d d ℂ
  map_eq : ∀ X, T X = ∑ i, kraus i * X * (kraus i)ᴴ
  kraus_complete : ∑ i, (kraus i)ᴴ * kraus i = 1
  trace_preserving : ∀ X, Matrix.trace (T X) = Matrix.trace X
  hermiticity_preserving : IsHermiticityPreserving T

def IsTraceAnnihilating
    {d : Type u} [Fintype d] [DecidableEq d] (Φ : Channel d) : Prop :=
  ∀ X, Matrix.trace (Φ X) = 0

/-- Transposition. -/
def transposeMap (d : Type u) [Fintype d] [DecidableEq d] : Channel d where
  toFun := fun X => Xᵀ
  map_add' := by
    intro X Y
    ext i j
    simp
  map_smul' := by
    intro c X
    ext i j
    simp

/-- Tensor a map on the left factor with the identity on the right factor. -/
def tensorWithIdentity
    (d k : Type u) [Fintype d] [DecidableEq d] [Fintype k] [DecidableEq k]
    (Φ : Channel d) : Channel (d × k) where
  toFun := fun X i j =>
    Φ (fun p q : d => X (p, i.2) (q, j.2)) i.1 j.1
  map_add' := by
    intro X Y
    ext i j
    let X' : Operator d := fun p q => X (p, i.2) (q, j.2)
    let Y' : Operator d := fun p q => Y (p, i.2) (q, j.2)
    change (Φ (X' + Y')) i.1 j.1 = (Φ X' + Φ Y') i.1 j.1
    rw [map_add]
  map_smul' := by
    intro c X
    ext i j
    let X' : Operator d := fun p q => X (p, i.2) (q, j.2)
    change (Φ (c • X')) i.1 j.1 = (c • Φ X') i.1 j.1
    rw [map_smul]

/-- Partial transpose on the left tensor factor. -/
def partialTransposeMap
    (d k : Type u) [Fintype d] [DecidableEq d] [Fintype k] [DecidableEq k] :
    Channel (d × k) where
  toFun := fun X i j => X (j.1, i.2) (i.1, j.2)
  map_add' := by
    intro X Y
    ext i j
    simp
  map_smul' := by
    intro c X
    ext i j
    simp

/-- Diamond norm in the paper's form: `sup_k sup_ρ ‖(Φ ⊗ id_k)(ρ)‖₁`. -/
def diamondNorm
    {d : Type u} [Fintype d] [DecidableEq d] (Φ : Channel d) : ℝ :=
  sSup {r : ℝ | ∃ n : ℕ, ∃ ρ : DensityState (d × ULift (Fin n)),
    r = traceNormOp (tensorWithIdentity d (ULift (Fin n)) Φ ρ.1)}

/-- Fixed-ancilla stabilization of `Φ`, used for the standard `k = d` reduction. -/
def diamondNormAt
    {d k : Type u} [Fintype d] [DecidableEq d] [Fintype k] [DecidableEq k]
    (Φ : Channel d) : ℝ :=
  sSup {r : ℝ | ∃ ρ : DensityState (d × k),
    r = traceNormOp (tensorWithIdentity d k Φ ρ.1)}

/-- Same-size stabilization.
It agrees with the full diamond norm by the standard restriction to `k = d`. -/
abbrev diamondOp
    {d : Type u} [Fintype d] [DecidableEq d] (Φ : Channel d) : ℝ :=
  diamondNormAt (d := d) (k := d) Φ

/-- Partial trace over the left factor. -/
def partialTraceLeft
    (d k : Type u) [Fintype d] [DecidableEq d] [Fintype k] [DecidableEq k]
    (X : Matrix (d × k) (d × k) ℂ) : Matrix k k ℂ :=
  fun i j => ∑ a, X (a, i) (a, j)

/-- The map `X ↦ X - Φ X`. -/
def idMinus
    {d : Type u} [Fintype d] [DecidableEq d] (Φ : Channel d) : Channel d where
  toFun := fun X => X - Φ X
  map_add' := by
    intro X Y
    ext i j
    simp [map_add, sub_eq_add_neg, add_assoc, add_left_comm, add_comm]
  map_smul' := by
    intro c X
    ext i j
    simp [map_smul, sub_eq_add_neg, mul_add]

/-- Unitary conjugation. -/
def adMap (d : Type u) [Fintype d] [DecidableEq d]
    (U : Matrix d d ℂ) : Channel d where
  toFun := fun X => U * X * Uᴴ
  map_add' := by
    intro X Y
    simp [Matrix.mul_add, Matrix.add_mul, Matrix.mul_assoc]
  map_smul' := by
    intro c X
    simp [Matrix.mul_assoc]

/-- The phase unitary used in the lower-bound example. -/
def Ud (d : ℕ) [Fact (1 < d)] : Matrix (Fin d) (Fin d) ℂ :=
  Matrix.diagonal fun i =>
    Complex.exp ((2 * Real.pi * Complex.I * (i : ℂ)) / (d : ℂ))

def Lambda (d : ℕ) [Fact (1 < d)] : Channel (Fin d) :=
  (transposeMap (Fin d)).comp (idMinus (adMap (Fin d) (Ud d)))

end
end Diamond
