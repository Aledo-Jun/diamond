import Diamond.HolevoWerner.ReplaceArgument

open scoped BigOperators
open scoped ComplexOrder
open scoped Kronecker
open scoped MatrixOrder
open scoped Matrix.Norms.Frobenius
open Matrix

namespace Diamond

universe u

noncomputable section

/-- Original finite-error Holevo-Werner linear converse, isolated as the `α = 1`
instance of the generic replacement theorem. -/
theorem holevo_werner_linear_bound
    {phys msg : Type u}
    [Fintype phys] [DecidableEq phys]
    [Fintype msg] [DecidableEq msg] [Nonempty msg]
    (T : Channel phys) (m : ℕ)
    (encoder : Superoperator msg phys)
    (decoder : Superoperator phys msg)
    (tensorPower : Channel phys)
    (ε : ℝ)
    (htranspose_triangle :
      diamondOp (transposeMap msg) ≤
        diamondOp
          ((transposeMap msg).comp (effectiveChannel encoder decoder tensorPower)) +
            diamondOp
              ((transposeMap msg).comp
                (idMinus (effectiveChannel encoder decoder tensorPower))))
    (htranspose_code_bound :
      diamondOp
          ((transposeMap msg).comp (effectiveChannel encoder decoder tensorPower)) ≤
        (diamondOp ((transposeMap phys).comp T)) ^ m)
    (hsubmult :
      diamondOp
          ((transposeMap msg).comp
            (idMinus (effectiveChannel encoder decoder tensorPower))) ≤
        diamondOp (transposeMap msg) *
          diamondOp (idMinus (effectiveChannel encoder decoder tensorPower)))
    (herror :
      ε =
        (1 / 2 : ℝ) *
          diamondOp (idMinus (effectiveChannel encoder decoder tensorPower))) :
    (1 - 2 * ε) * (Fintype.card msg : ℝ) ≤
      (diamondOp ((transposeMap phys).comp T)) ^ m := by
  have hsubmult' :
      diamondOp
          ((transposeMap msg).comp
            (idMinus (effectiveChannel encoder decoder tensorPower))) ≤
        1 * diamondOp (transposeMap msg) *
          diamondOp (idMinus (effectiveChannel encoder decoder tensorPower)) := by
    simpa using hsubmult
  simpa using
    holevo_werner_linear_bound_of_submultiplicative_constant
      T m encoder decoder tensorPower ε 1
      htranspose_triangle htranspose_code_bound hsubmult' herror

/-- Original finite-error Holevo-Werner converse in logarithmic form. -/
theorem holevo_werner_bound
    {phys msg : Type u}
    [Fintype phys] [DecidableEq phys]
    [Fintype msg] [DecidableEq msg] [Nonempty msg]
    (T : Channel phys) (m : ℕ)
    (encoder : Superoperator msg phys)
    (decoder : Superoperator phys msg)
    (tensorPower : Channel phys)
    (ε : ℝ)
    (htranspose_triangle :
      diamondOp (transposeMap msg) ≤
        diamondOp
          ((transposeMap msg).comp (effectiveChannel encoder decoder tensorPower)) +
            diamondOp
              ((transposeMap msg).comp
                (idMinus (effectiveChannel encoder decoder tensorPower))))
    (htranspose_code_bound :
      diamondOp
          ((transposeMap msg).comp (effectiveChannel encoder decoder tensorPower)) ≤
        (diamondOp ((transposeMap phys).comp T)) ^ m)
    (hsubmult :
      diamondOp
          ((transposeMap msg).comp
            (idMinus (effectiveChannel encoder decoder tensorPower))) ≤
        diamondOp (transposeMap msg) *
          diamondOp (idMinus (effectiveChannel encoder decoder tensorPower)))
    (herror :
      ε =
        (1 / 2 : ℝ) *
          diamondOp (idMinus (effectiveChannel encoder decoder tensorPower)))
    (hm : 0 < m) (hε : ε < 1 / 2) :
    Real.logb 2 (Fintype.card msg : ℝ) / (m : ℝ) ≤
      Real.logb 2 (diamondOp ((transposeMap phys).comp T)) +
        (1 / (m : ℝ)) * Real.logb 2 (1 / (1 - 2 * ε)) := by
  have hlinear :
      (1 - 2 * ε) * (Fintype.card msg : ℝ) ≤
        (diamondOp ((transposeMap phys).comp T)) ^ m := by
    exact holevo_werner_linear_bound T m encoder decoder tensorPower ε
      htranspose_triangle htranspose_code_bound hsubmult herror
  exact holevo_werner_bound_of_linear_bound T m ε 2 hlinear hm hε (by norm_num)

/-- Improved finite-error Holevo-Werner linear converse, obtained by replacing the
generic submultiplicativity step with Theorem 1 / Remark 1. -/
theorem improved_holevo_werner_linear_bound
    {phys msg : Type u}
    [Fintype phys] [DecidableEq phys]
    [Fintype msg] [DecidableEq msg] [Nonempty msg]
    (T : Channel phys) (m : ℕ)
    (encoder : Superoperator msg phys)
    (decoder : Superoperator phys msg)
    (tensorPower : Channel phys)
    (ε : ℝ)
    (heffective :
      IsQuantumChannel (effectiveChannel encoder decoder tensorPower))
    (htranspose_triangle :
      diamondOp (transposeMap msg) ≤
        diamondOp
          ((transposeMap msg).comp (effectiveChannel encoder decoder tensorPower)) +
            diamondOp
              ((transposeMap msg).comp
                (idMinus (effectiveChannel encoder decoder tensorPower))))
    (htranspose_code_bound :
      diamondOp
          ((transposeMap msg).comp (effectiveChannel encoder decoder tensorPower)) ≤
        (diamondOp ((transposeMap phys).comp T)) ^ m)
    (herror :
      ε =
        (1 / 2 : ℝ) *
          diamondOp (idMinus (effectiveChannel encoder decoder tensorPower))) :
    (1 - Real.sqrt 2 * ε) * (Fintype.card msg : ℝ) ≤
      (diamondOp ((transposeMap phys).comp T)) ^ m := by
  let effective := effectiveChannel encoder decoder tensorPower
  have hsubmult :
      diamondOp
          ((transposeMap msg).comp
            (idMinus effective)) ≤
        (1 / Real.sqrt 2) * diamondOp (transposeMap msg) *
          diamondOp (idMinus effective) := by
    exact remark1 (d := msg) (Ψ := idMinus effective)
      (idMinus_isHermiticityPreserving effective heffective)
      (idMinus_isTraceAnnihilating effective heffective)
  have hlin :
      (1 - (2 * (1 / Real.sqrt 2)) * ε) * (Fintype.card msg : ℝ) ≤
        (diamondOp ((transposeMap phys).comp T)) ^ m := by
    exact holevo_werner_linear_bound_of_submultiplicative_constant
      T m encoder decoder tensorPower ε (1 / Real.sqrt 2)
      htranspose_triangle htranspose_code_bound hsubmult herror
  have hconst : 2 * (1 / Real.sqrt 2) = Real.sqrt 2 := by
    have hsqrt2_ne : Real.sqrt 2 ≠ 0 := by positivity
    calc
      2 * (1 / Real.sqrt 2) = 2 / Real.sqrt 2 := by ring
      _ = Real.sqrt 2 := by
        apply (div_eq_iff hsqrt2_ne).2
        nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 2 by positivity)]
  rw [hconst] at hlin
  simpa [mul_assoc, mul_left_comm, mul_comm] using hlin

/-- Improved finite-error Holevo-Werner converse in logarithmic form. -/
theorem improved_holevo_werner_bound
    {phys msg : Type u}
    [Fintype phys] [DecidableEq phys]
    [Fintype msg] [DecidableEq msg] [Nonempty msg]
    (T : Channel phys) (m : ℕ)
    (encoder : Superoperator msg phys)
    (decoder : Superoperator phys msg)
    (tensorPower : Channel phys)
    (ε : ℝ)
    (heffective :
      IsQuantumChannel (effectiveChannel encoder decoder tensorPower))
    (htranspose_triangle :
      diamondOp (transposeMap msg) ≤
        diamondOp
          ((transposeMap msg).comp (effectiveChannel encoder decoder tensorPower)) +
            diamondOp
              ((transposeMap msg).comp
                (idMinus (effectiveChannel encoder decoder tensorPower))))
    (htranspose_code_bound :
      diamondOp
          ((transposeMap msg).comp (effectiveChannel encoder decoder tensorPower)) ≤
        (diamondOp ((transposeMap phys).comp T)) ^ m)
    (herror :
      ε =
        (1 / 2 : ℝ) *
          diamondOp (idMinus (effectiveChannel encoder decoder tensorPower)))
    (hm : 0 < m) (hε : ε < 1 / Real.sqrt 2) :
    Real.logb 2 (Fintype.card msg : ℝ) / (m : ℝ) ≤
      Real.logb 2 (diamondOp ((transposeMap phys).comp T)) +
        (1 / (m : ℝ)) * Real.logb 2 (1 / (1 - Real.sqrt 2 * ε)) := by
  have hlinear :
      (1 - Real.sqrt 2 * ε) * (Fintype.card msg : ℝ) ≤
        (diamondOp ((transposeMap phys).comp T)) ^ m := by
    exact improved_holevo_werner_linear_bound T m encoder decoder tensorPower ε
      heffective htranspose_triangle htranspose_code_bound herror
  exact holevo_werner_bound_of_linear_bound
    T m ε (Real.sqrt 2) hlinear hm hε (by positivity)

end
end Diamond
