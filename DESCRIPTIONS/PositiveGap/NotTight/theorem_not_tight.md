# theorem_not_tight

## Source location

- Original Lean file: `Diamond/PositiveGap/NotTight.lean`
- Declaration name: `theorem_not_tight`
- Declaration kind: `theorem`

## Why this declaration exists

This is the finite-dimensional strictness result showing the constant from Theorem 1 is never actually attained by a nonzero channel difference.

 In the file `PositiveGap/NotTight.lean`, it contributes to the finite-dimensional non-tightness argument and the equality-case analysis behind it. Later proofs call this result by name, so documenting it makes the larger argument readable as a mathematical chain rather than as opaque proof script.

## Original code

```lean
/-- The strictness theorem for Theorem 1 in finite dimensions, proved from the paper's
    maximizer and Uhlmann/rank-bound background inputs. -/
theorem theorem_not_tight
    {d : Type u} [Fintype d] [DecidableEq d] [Nonempty d]
    (T : Channel d) (hT : IsQuantumChannel T) (hΦ : idMinus T ≠ 0) :
    diamondOp ((transposeMap d).comp (idMinus T))
      < (1 / Real.sqrt 2) * diamondOp (transposeMap d) * diamondOp (idMinus T) := by
  refine lt_of_le_of_ne (theorem1 T hT) ?_
  intro hEq
  let Φ : Channel d := idMinus T
  let LΦ : Channel d := (transposeMap d).comp Φ
  obtain ⟨ρ, hYmax, hXnonzero⟩ := exists_maximizing_state T hT hΦ
  let X : Matrix (d × d) (d × d) ℂ := tensorWithIdentity d d Φ ρ.1
  let Y : Matrix (d × d) (d × d) ℂ := partialTransposeMap d d X
  have hrewrite : tensorWithIdentity d d LΦ ρ.1 = Y := by
    simpa [LΦ, Φ, X, Y, LinearMap.comp_apply] using
      congrArg (fun Ψ : Channel (d × d) => Ψ ρ.1)
        (tensorWithIdentity_comp_transpose (d := d) (k := d) (Φ := Φ))
  have hYmax : traceNormOp Y = diamondOp LΦ := by
    simpa [Y, hrewrite] using hYmax
  have hTraceX : Matrix.trace X = 0 := by
    simpa [X, Φ] using
      tensorWithIdentity_trace_zero (d := d) (k := d)
        (idMinus T) (idMinus_isTraceAnnihilating T hT) ρ.1
  have hHermX : Matrix.IsHermitian X := by
    simpa [X, Φ] using
      tensorWithIdentity_hermitian (d := d) (k := d)
        (Ψ := idMinus T) (idMinus_isHermiticityPreserving T hT) ρ.1 ρ.2
  have hPartialTraceX : partialTraceLeft d d X = 0 := by
    simpa [X, Φ] using corollary1 T hT ρ.1
  have hYnonzero : Y ≠ 0 := by
    exact partialTranspose_ne_zero_of_ne_zero (d := d) (k := d) hXnonzero
  have hYle :
      traceNormOp Y ≤ Real.sqrt (Fintype.card (d × d) : ℝ) * hsNormOp X := by
    have htmp :
        traceNormOp Y ≤ Real.sqrt (Fintype.card (d × d) : ℝ) * hsNormOp Y := by
      simpa [Y] using lemma2 (Y := Y)
    have hpt : hsNormOp Y = hsNormOp X := by
      simpa [X, Y] using lemma3 (d := d) (k := d) X
    simpa [hpt] using htmp
  have hXle : hsNormOp X ≤ (1 / Real.sqrt 2) * traceNormOp X := by
    simpa [X] using lemma1 (X := X) hHermX hTraceX
  have hRle : traceNormOp X ≤ diamondOp Φ := by
    simpa [X, Φ, diamondOp] using
      traceNorm_apply_le_diamond (d := d) (k := d) (Φ := Φ) (ρ := ρ)
  have hYtarget :
      traceNormOp Y =
        Real.sqrt (Fintype.card (d × d) : ℝ) * ((1 / Real.sqrt 2) * diamondOp Φ) := by
    calc
      traceNormOp Y = diamondOp LΦ := hYmax
      _ = (1 / Real.sqrt 2) * diamondOp (transposeMap d) * diamondOp Φ := by
        simpa [LΦ, Φ] using hEq
      _ = Real.sqrt (Fintype.card (d × d) : ℝ) * ((1 / Real.sqrt 2) * diamondOp Φ) := by
        rw [lemma_transpose_diamond (d := d)]
        ring
  have hYeq : traceNormOp Y = Real.sqrt (Fintype.card (d × d) : ℝ) * hsNormOp X := by
    apply le_antisymm hYle
    calc
      Real.sqrt (Fintype.card (d × d) : ℝ) * hsNormOp X
          ≤ Real.sqrt (Fintype.card (d × d) : ℝ) * ((1 / Real.sqrt 2) * diamondOp Φ) := by
            apply mul_le_mul_of_nonneg_left
            · exact le_trans hXle (mul_le_mul_of_nonneg_left hRle (by positivity))
            · exact Real.sqrt_nonneg _
      _ = traceNormOp Y := by
        symm
        exact hYtarget
  have hsqrt_pos : 0 < Real.sqrt (Fintype.card (d × d) : ℝ) := by
    positivity
  have hhs_eq : hsNormOp X = (1 / Real.sqrt 2) * diamondOp Φ := by
    nlinarith [hYeq, hYtarget, hsqrt_pos]
  have htrace_ge : diamondOp Φ ≤ traceNormOp X := by
    have hscaled : (1 / Real.sqrt 2) * diamondOp Φ ≤ (1 / Real.sqrt 2) * traceNormOp X := by
      simpa [hhs_eq] using hXle
    have hfac : 0 < (1 / Real.sqrt 2 : ℝ) := by positivity
    exact le_of_mul_le_mul_left hscaled hfac
  have htrace_eq : traceNormOp X = diamondOp Φ := by
    exact le_antisymm hRle htrace_ge
  have hlemma1eq : hsNormOp X = (1 / Real.sqrt 2) * traceNormOp X := by
    calc
      hsNormOp X = (1 / Real.sqrt 2) * diamondOp Φ := hhs_eq
      _ = (1 / Real.sqrt 2) * traceNormOp X := by rw [htrace_eq]
  have hlemma2eq :
      traceNormOp Y = Real.sqrt (Fintype.card (d × d) : ℝ) * hsNormOp Y := by
    have hpt : hsNormOp Y = hsNormOp X := by
      simpa [X, Y] using lemma3 (d := d) (k := d) X
    simpa [hpt] using hYeq
  have hrankX : X.rank = 2 :=
    lemma1_eq_imp_rank_two hHermX hTraceX hXnonzero hlemma1eq
  have hrankY : Y.rank = Fintype.card (d × d) :=
    lemma2_eq_imp_full_rank (d := d) (Y := Y) hYnonzero hlemma2eq
  have hupper : Y.rank ≤ Fintype.card (d × d) - Fintype.card d := by
    simpa [X, Y] using
      partialTranspose_rank_upper_bound (d := d) hXnonzero hHermX hTraceX hPartialTraceX hrankX
  have hd_pos : 0 < Fintype.card d := Fintype.card_pos_iff.mpr inferInstance
  have hlt : Fintype.card (d × d) - Fintype.card d < Fintype.card (d × d) := by
    exact Nat.sub_lt (by positivity) hd_pos
  have : Fintype.card (d × d) < Fintype.card (d × d) := by
    simpa [hrankY] using lt_of_le_of_lt hupper hlt
  exact (lt_irrefl _ this).elim
```

## Block-by-block explanation

The explanation below follows the declaration block by block. Each block groups a coherent piece of the definition or proof, so the mathematical structure is easier to see than in a strictly line-oriented reading.

1. Code:
```lean
/-- The strictness theorem for Theorem 1 in finite dimensions, proved from the paper's
```
This is a Lean docstring. It is a human-written comment that tells readers what the declaration is meant to express before the formal code begins.

2. Code:
```lean
    maximizer and Uhlmann/rank-bound background inputs. -/
```
This line is one local step in the declaration. It either refines the formula being defined or advances the proof by a small algebraic or logical move.

3. Code:
```lean
theorem theorem_not_tight
```
This line starts the `theorem_not_tight` declaration. Because it begins with `theorem`, Lean now knows what kind of named object is being introduced.

4. Code:
```lean
    {d : Type u} [Fintype d] [DecidableEq d] [Nonempty d]
```
This line is one local step in the declaration. It either refines the formula being defined or advances the proof by a small algebraic or logical move.  A bracket such as `[Fintype d]` tells Lean that the index set `d` is finite, so sums over all indices make sense.  A bracket such as `[DecidableEq d]` tells Lean that it can decide whether two indices are equal.

5. Code:
```lean
    (T : Channel d) (hT : IsQuantumChannel T) (hΦ : idMinus T ≠ 0) :
```
This line is one local step in the declaration. It either refines the formula being defined or advances the proof by a small algebraic or logical move.  `Channel d` is an abbreviation for a complex-linear map from operators on `d` to operators on `d`.

6. Code:
```lean
    diamondOp ((transposeMap d).comp (idMinus T))
```
This line is one local step in the declaration. It either refines the formula being defined or advances the proof by a small algebraic or logical move.  `comp` means composition of maps: one map is applied after another.

7. Code:
```lean
      < (1 / Real.sqrt 2) * diamondOp (transposeMap d) * diamondOp (idMinus T) := by
```
This line says that a proof script begins here. Everything indented underneath is a sequence of instructions that Lean will check step by step.

8. Code:
```lean
  refine lt_of_le_of_ne (theorem1 T hT) ?_
```
This line is a more controlled version of `apply`. It sets up the proof with a partly specified argument and leaves smaller goals to solve next.

9. Code:
```lean
  intro hEq
```
This line introduces the variable or hypothesis named here into the proof context. In ordinary mathematical prose, it is the same as saying “let” or “assume”.

10. Code:
```lean
  let Φ : Channel d := idMinus T
```
This line gives a temporary name to an expression. Doing that makes later lines shorter and easier to read.  `Channel d` is an abbreviation for a complex-linear map from operators on `d` to operators on `d`.

11. Code:
```lean
  let LΦ : Channel d := (transposeMap d).comp Φ
```
This line gives a temporary name to an expression. Doing that makes later lines shorter and easier to read.  `Channel d` is an abbreviation for a complex-linear map from operators on `d` to operators on `d`.  `comp` means composition of maps: one map is applied after another.

12. Code:
```lean
  obtain ⟨ρ, hYmax, hXnonzero⟩ := exists_maximizing_state T hT hΦ
```
This line unpacks an existential statement or tuple into named pieces.

13. Code:
```lean
  let X : Matrix (d × d) (d × d) ℂ := tensorWithIdentity d d Φ ρ.1
```
This line gives a temporary name to an expression. Doing that makes later lines shorter and easier to read.  `Matrix d d ℂ` means a square matrix with complex entries; the index type `d` tells Lean which rows and columns exist.

14. Code:
```lean
  let Y : Matrix (d × d) (d × d) ℂ := partialTransposeMap d d X
```
This line gives a temporary name to an expression. Doing that makes later lines shorter and easier to read.  `Matrix d d ℂ` means a square matrix with complex entries; the index type `d` tells Lean which rows and columns exist.

15. Code:
```lean
  have hrewrite : tensorWithIdentity d d LΦ ρ.1 = Y := by
```
This line says that a proof script begins here. Everything indented underneath is a sequence of instructions that Lean will check step by step.

16. Code:
```lean
    simpa [LΦ, Φ, X, Y, LinearMap.comp_apply] using
```
This line simplifies the goal using definitions and known equalities. `simpa` means that, after simplification, the desired statement matches a theorem Lean already has.  `comp` means composition of maps: one map is applied after another.  `LinearMap.comp` is composition of linear maps.

17. Code:
```lean
      congrArg (fun Ψ : Channel (d × d) => Ψ ρ.1)
```
This line applies the same function to both sides of a known equality, producing a new equality better suited to the current goal.

18. Code:
```lean
        (tensorWithIdentity_comp_transpose (d := d) (k := d) (Φ := Φ))
```
This line is one local step in the declaration. It either refines the formula being defined or advances the proof by a small algebraic or logical move.

19. Code:
```lean
  have hYmax : traceNormOp Y = diamondOp LΦ := by
```
This line says that a proof script begins here. Everything indented underneath is a sequence of instructions that Lean will check step by step.

20. Code:
```lean
    simpa [Y, hrewrite] using hYmax
```
This line simplifies the goal using definitions and known equalities. `simpa` means that, after simplification, the desired statement matches a theorem Lean already has.

21. Code:
```lean
  have hTraceX : Matrix.trace X = 0 := by
```
This line says that a proof script begins here. Everything indented underneath is a sequence of instructions that Lean will check step by step.

22. Code:
```lean
    simpa [X, Φ] using
```
This line simplifies the goal using definitions and known equalities. `simpa` means that, after simplification, the desired statement matches a theorem Lean already has.

23. Code:
```lean
      tensorWithIdentity_trace_zero (d := d) (k := d)
```
This line is one local step in the declaration. It either refines the formula being defined or advances the proof by a small algebraic or logical move.

24. Code:
```lean
        (idMinus T) (idMinus_isTraceAnnihilating T hT) ρ.1
```
This line is one local step in the declaration. It either refines the formula being defined or advances the proof by a small algebraic or logical move.

25. Code:
```lean
  have hHermX : Matrix.IsHermitian X := by
```
This line says that a proof script begins here. Everything indented underneath is a sequence of instructions that Lean will check step by step.

26. Code:
```lean
    simpa [X, Φ] using
```
This line simplifies the goal using definitions and known equalities. `simpa` means that, after simplification, the desired statement matches a theorem Lean already has.

27. Code:
```lean
      tensorWithIdentity_hermitian (d := d) (k := d)
```
This line is one local step in the declaration. It either refines the formula being defined or advances the proof by a small algebraic or logical move.

28. Code:
```lean
        (Ψ := idMinus T) (idMinus_isHermiticityPreserving T hT) ρ.1 ρ.2
```
This line is one local step in the declaration. It either refines the formula being defined or advances the proof by a small algebraic or logical move.

29. Code:
```lean
  have hPartialTraceX : partialTraceLeft d d X = 0 := by
```
This line says that a proof script begins here. Everything indented underneath is a sequence of instructions that Lean will check step by step.

30. Code:
```lean
    simpa [X, Φ] using corollary1 T hT ρ.1
```
This line simplifies the goal using definitions and known equalities. `simpa` means that, after simplification, the desired statement matches a theorem Lean already has.

31. Code:
```lean
  have hYnonzero : Y ≠ 0 := by
```
This line says that a proof script begins here. Everything indented underneath is a sequence of instructions that Lean will check step by step.

32. Code:
```lean
    exact partialTranspose_ne_zero_of_ne_zero (d := d) (k := d) hXnonzero
```
This line finishes the current goal by giving Lean the exact theorem, lemma, or term that proves it.

33. Code:
```lean
  have hYle :
```
This line introduces an intermediate claim. The proof pauses to establish a fact that will be used shortly afterwards.

34. Code:
```lean
      traceNormOp Y ≤ Real.sqrt (Fintype.card (d × d) : ℝ) * hsNormOp X := by
```
This line says that a proof script begins here. Everything indented underneath is a sequence of instructions that Lean will check step by step.  `Fintype.card` is the size of a finite index set.

35. Code:
```lean
    have htmp :
```
This line introduces an intermediate claim. The proof pauses to establish a fact that will be used shortly afterwards.

36. Code:
```lean
        traceNormOp Y ≤ Real.sqrt (Fintype.card (d × d) : ℝ) * hsNormOp Y := by
```
This line says that a proof script begins here. Everything indented underneath is a sequence of instructions that Lean will check step by step.  `Fintype.card` is the size of a finite index set.

37. Code:
```lean
      simpa [Y] using lemma2 (Y := Y)
```
This line simplifies the goal using definitions and known equalities. `simpa` means that, after simplification, the desired statement matches a theorem Lean already has.

38. Code:
```lean
    have hpt : hsNormOp Y = hsNormOp X := by
```
This line says that a proof script begins here. Everything indented underneath is a sequence of instructions that Lean will check step by step.

39. Code:
```lean
      simpa [X, Y] using lemma3 (d := d) (k := d) X
```
This line simplifies the goal using definitions and known equalities. `simpa` means that, after simplification, the desired statement matches a theorem Lean already has.

40. Code:
```lean
    simpa [hpt] using htmp
```
This line simplifies the goal using definitions and known equalities. `simpa` means that, after simplification, the desired statement matches a theorem Lean already has.

41. Code:
```lean
  have hXle : hsNormOp X ≤ (1 / Real.sqrt 2) * traceNormOp X := by
```
This line says that a proof script begins here. Everything indented underneath is a sequence of instructions that Lean will check step by step.

42. Code:
```lean
    simpa [X] using lemma1 (X := X) hHermX hTraceX
```
This line simplifies the goal using definitions and known equalities. `simpa` means that, after simplification, the desired statement matches a theorem Lean already has.

43. Code:
```lean
  have hRle : traceNormOp X ≤ diamondOp Φ := by
```
This line says that a proof script begins here. Everything indented underneath is a sequence of instructions that Lean will check step by step.

44. Code:
```lean
    simpa [X, Φ, diamondOp] using
```
This line simplifies the goal using definitions and known equalities. `simpa` means that, after simplification, the desired statement matches a theorem Lean already has.

45. Code:
```lean
      traceNorm_apply_le_diamond (d := d) (k := d) (Φ := Φ) (ρ := ρ)
```
This line is one local step in the declaration. It either refines the formula being defined or advances the proof by a small algebraic or logical move.

46. Code:
```lean
  have hYtarget :
```
This line introduces an intermediate claim. The proof pauses to establish a fact that will be used shortly afterwards.

47. Code:
```lean
      traceNormOp Y =
```
This line is one local step in the declaration. It either refines the formula being defined or advances the proof by a small algebraic or logical move.

48. Code:
```lean
        Real.sqrt (Fintype.card (d × d) : ℝ) * ((1 / Real.sqrt 2) * diamondOp Φ) := by
```
This line says that a proof script begins here. Everything indented underneath is a sequence of instructions that Lean will check step by step.  `Fintype.card` is the size of a finite index set.

49. Code:
```lean
    calc
```
This line begins a chained calculation. Each displayed step that follows must be justified by the indented proof after `:= by`.

50. Code:
```lean
      traceNormOp Y = diamondOp LΦ := hYmax
```
This line is one local step in the declaration. It either refines the formula being defined or advances the proof by a small algebraic or logical move.

51. Code:
```lean
      _ = (1 / Real.sqrt 2) * diamondOp (transposeMap d) * diamondOp Φ := by
```
This line says that a proof script begins here. Everything indented underneath is a sequence of instructions that Lean will check step by step.

52. Code:
```lean
        simpa [LΦ, Φ] using hEq
```
This line simplifies the goal using definitions and known equalities. `simpa` means that, after simplification, the desired statement matches a theorem Lean already has.

53. Code:
```lean
      _ = Real.sqrt (Fintype.card (d × d) : ℝ) * ((1 / Real.sqrt 2) * diamondOp Φ) := by
```
This line says that a proof script begins here. Everything indented underneath is a sequence of instructions that Lean will check step by step.  `Fintype.card` is the size of a finite index set.

54. Code:
```lean
        rw [lemma_transpose_diamond (d := d)]
```
This line uses rewriting. Lean replaces one expression by an equal expression using the lemmas listed in brackets.

55. Code:
```lean
        ring
```
This line normalizes an algebraic identity in a commutative ring, just as one would expand and collect like terms by hand.

56. Code:
```lean
  have hYeq : traceNormOp Y = Real.sqrt (Fintype.card (d × d) : ℝ) * hsNormOp X := by
```
This line says that a proof script begins here. Everything indented underneath is a sequence of instructions that Lean will check step by step.  `Fintype.card` is the size of a finite index set.

57. Code:
```lean
    apply le_antisymm hYle
```
This line applies an existing theorem to the current goal. Lean then asks the author to prove the theorem’s hypotheses.

58. Code:
```lean
    calc
```
This line begins a chained calculation. Each displayed step that follows must be justified by the indented proof after `:= by`.

59. Code:
```lean
      Real.sqrt (Fintype.card (d × d) : ℝ) * hsNormOp X
```
This line is one local step in the declaration. It either refines the formula being defined or advances the proof by a small algebraic or logical move.  `Fintype.card` is the size of a finite index set.

60. Code:
```lean
          ≤ Real.sqrt (Fintype.card (d × d) : ℝ) * ((1 / Real.sqrt 2) * diamondOp Φ) := by
```
This line says that a proof script begins here. Everything indented underneath is a sequence of instructions that Lean will check step by step.  `Fintype.card` is the size of a finite index set.

61. Code:
```lean
            apply mul_le_mul_of_nonneg_left
```
This line applies an existing theorem to the current goal. Lean then asks the author to prove the theorem’s hypotheses.

62. Code:
```lean
            · exact le_trans hXle (mul_le_mul_of_nonneg_left hRle (by positivity))
```
This bullet starts a new subgoal produced by the previous tactic. Lean is now focusing on one branch of the argument.

63. Code:
```lean
            · exact Real.sqrt_nonneg _
```
This bullet starts a new subgoal produced by the previous tactic. Lean is now focusing on one branch of the argument.

64. Code:
```lean
      _ = traceNormOp Y := by
```
This line says that a proof script begins here. Everything indented underneath is a sequence of instructions that Lean will check step by step.

65. Code:
```lean
        symm
```
This line is one local step in the declaration. It either refines the formula being defined or advances the proof by a small algebraic or logical move.

66. Code:
```lean
        exact hYtarget
```
This line finishes the current goal by giving Lean the exact theorem, lemma, or term that proves it.

67. Code:
```lean
  have hsqrt_pos : 0 < Real.sqrt (Fintype.card (d × d) : ℝ) := by
```
This line says that a proof script begins here. Everything indented underneath is a sequence of instructions that Lean will check step by step.  `Fintype.card` is the size of a finite index set.

68. Code:
```lean
    positivity
```
This line asks Lean to prove that the displayed quantity is positive or nonnegative using standard positivity rules.

69. Code:
```lean
  have hhs_eq : hsNormOp X = (1 / Real.sqrt 2) * diamondOp Φ := by
```
This line says that a proof script begins here. Everything indented underneath is a sequence of instructions that Lean will check step by step.

70. Code:
```lean
    nlinarith [hYeq, hYtarget, hsqrt_pos]
```
This line solves the current numerical inequality by combining the equalities and inequalities already available in the context.

71. Code:
```lean
  have htrace_ge : diamondOp Φ ≤ traceNormOp X := by
```
This line says that a proof script begins here. Everything indented underneath is a sequence of instructions that Lean will check step by step.

72. Code:
```lean
    have hscaled : (1 / Real.sqrt 2) * diamondOp Φ ≤ (1 / Real.sqrt 2) * traceNormOp X := by
```
This line says that a proof script begins here. Everything indented underneath is a sequence of instructions that Lean will check step by step.

73. Code:
```lean
      simpa [hhs_eq] using hXle
```
This line simplifies the goal using definitions and known equalities. `simpa` means that, after simplification, the desired statement matches a theorem Lean already has.

74. Code:
```lean
    have hfac : 0 < (1 / Real.sqrt 2 : ℝ) := by positivity
```
This line introduces an intermediate claim. The proof pauses to establish a fact that will be used shortly afterwards.

75. Code:
```lean
    exact le_of_mul_le_mul_left hscaled hfac
```
This line finishes the current goal by giving Lean the exact theorem, lemma, or term that proves it.

76. Code:
```lean
  have htrace_eq : traceNormOp X = diamondOp Φ := by
```
This line says that a proof script begins here. Everything indented underneath is a sequence of instructions that Lean will check step by step.

77. Code:
```lean
    exact le_antisymm hRle htrace_ge
```
This line finishes the current goal by giving Lean the exact theorem, lemma, or term that proves it.

78. Code:
```lean
  have hlemma1eq : hsNormOp X = (1 / Real.sqrt 2) * traceNormOp X := by
```
This line says that a proof script begins here. Everything indented underneath is a sequence of instructions that Lean will check step by step.

79. Code:
```lean
    calc
```
This line begins a chained calculation. Each displayed step that follows must be justified by the indented proof after `:= by`.

80. Code:
```lean
      hsNormOp X = (1 / Real.sqrt 2) * diamondOp Φ := hhs_eq
```
This line is one local step in the declaration. It either refines the formula being defined or advances the proof by a small algebraic or logical move.

81. Code:
```lean
      _ = (1 / Real.sqrt 2) * traceNormOp X := by rw [htrace_eq]
```
This line is one step inside a `calc` block. Lean is checking that the new expression really follows from the previous one.

82. Code:
```lean
  have hlemma2eq :
```
This line introduces an intermediate claim. The proof pauses to establish a fact that will be used shortly afterwards.

83. Code:
```lean
      traceNormOp Y = Real.sqrt (Fintype.card (d × d) : ℝ) * hsNormOp Y := by
```
This line says that a proof script begins here. Everything indented underneath is a sequence of instructions that Lean will check step by step.  `Fintype.card` is the size of a finite index set.

84. Code:
```lean
    have hpt : hsNormOp Y = hsNormOp X := by
```
This line says that a proof script begins here. Everything indented underneath is a sequence of instructions that Lean will check step by step.

85. Code:
```lean
      simpa [X, Y] using lemma3 (d := d) (k := d) X
```
This line simplifies the goal using definitions and known equalities. `simpa` means that, after simplification, the desired statement matches a theorem Lean already has.

86. Code:
```lean
    simpa [hpt] using hYeq
```
This line simplifies the goal using definitions and known equalities. `simpa` means that, after simplification, the desired statement matches a theorem Lean already has.

87. Code:
```lean
  have hrankX : X.rank = 2 :=
```
This line introduces an intermediate claim. The proof pauses to establish a fact that will be used shortly afterwards.

88. Code:
```lean
    lemma1_eq_imp_rank_two hHermX hTraceX hXnonzero hlemma1eq
```
This line is one local step in the declaration. It either refines the formula being defined or advances the proof by a small algebraic or logical move.

89. Code:
```lean
  have hrankY : Y.rank = Fintype.card (d × d) :=
```
This line introduces an intermediate claim. The proof pauses to establish a fact that will be used shortly afterwards.  `Fintype.card` is the size of a finite index set.

90. Code:
```lean
    lemma2_eq_imp_full_rank (d := d) (Y := Y) hYnonzero hlemma2eq
```
This line is one local step in the declaration. It either refines the formula being defined or advances the proof by a small algebraic or logical move.

91. Code:
```lean
  have hupper : Y.rank ≤ Fintype.card (d × d) - Fintype.card d := by
```
This line says that a proof script begins here. Everything indented underneath is a sequence of instructions that Lean will check step by step.  `Fintype.card` is the size of a finite index set.

92. Code:
```lean
    simpa [X, Y] using
```
This line simplifies the goal using definitions and known equalities. `simpa` means that, after simplification, the desired statement matches a theorem Lean already has.

93. Code:
```lean
      partialTranspose_rank_upper_bound (d := d) hXnonzero hHermX hTraceX hPartialTraceX hrankX
```
This line is one local step in the declaration. It either refines the formula being defined or advances the proof by a small algebraic or logical move.

94. Code:
```lean
  have hd_pos : 0 < Fintype.card d := Fintype.card_pos_iff.mpr inferInstance
```
This line introduces an intermediate claim. The proof pauses to establish a fact that will be used shortly afterwards.  `Fintype.card` is the size of a finite index set.

95. Code:
```lean
  have hlt : Fintype.card (d × d) - Fintype.card d < Fintype.card (d × d) := by
```
This line says that a proof script begins here. Everything indented underneath is a sequence of instructions that Lean will check step by step.  `Fintype.card` is the size of a finite index set.

96. Code:
```lean
    exact Nat.sub_lt (by positivity) hd_pos
```
This line finishes the current goal by giving Lean the exact theorem, lemma, or term that proves it.

97. Code:
```lean
  have : Fintype.card (d × d) < Fintype.card (d × d) := by
```
This line says that a proof script begins here. Everything indented underneath is a sequence of instructions that Lean will check step by step.  `Fintype.card` is the size of a finite index set.

98. Code:
```lean
    simpa [hrankY] using lt_of_le_of_lt hupper hlt
```
This line simplifies the goal using definitions and known equalities. `simpa` means that, after simplification, the desired statement matches a theorem Lean already has.

99. Code:
```lean
  exact (lt_irrefl _ this).elim
```
This line finishes the current goal by giving Lean the exact theorem, lemma, or term that proves it.

## Mathematical summary

Restated without Lean syntax, `theorem_not_tight` is the theorem or lemma written above.

- Assume equality holds in Theorem 1 and pick a maximizing state for the left-hand diamond norm.
- Show that equality in the theorem forces equality in Lemma 1 and Lemma 2 simultaneously.
- Use the equality-case theorems to deduce rank $2$ for $X_\star$ and full rank for its partial transpose.
- Use Corollary 1 together with the vectorization/swap machinery and the background rank estimate to obtain a contradictory upper bound on that rank.
- Conclude that the theorem's bound is always strict for a nonzero channel difference.

## Dependencies and downstream use

### Earlier declarations this depends on
- [`Channel`](../../Setups/Channel.md) from `Setups.lean`
- [`traceNormOp`](../../Setups/traceNormOp.md) from `Setups.lean`
- [`hsNormOp`](../../Setups/hsNormOp.md) from `Setups.lean`
- [`IsQuantumChannel`](../../Setups/IsQuantumChannel.md) from `Setups.lean`
- [`transposeMap`](../../Setups/transposeMap.md) from `Setups.lean`
- [`tensorWithIdentity`](../../Setups/tensorWithIdentity.md) from `Setups.lean`
- [`partialTransposeMap`](../../Setups/partialTransposeMap.md) from `Setups.lean`
- [`diamondOp`](../../Setups/diamondOp.md) from `Setups.lean`
- [`partialTraceLeft`](../../Setups/partialTraceLeft.md) from `Setups.lean`
- [`idMinus`](../../Setups/idMinus.md) from `Setups.lean`
- [`tensorWithIdentity_comp_transpose`](../../StandardFacts/tensorWithIdentity_comp_transpose.md) from `StandardFacts.lean`
- [`idMinus_isHermiticityPreserving`](../../StandardFacts/idMinus_isHermiticityPreserving.md) from `StandardFacts.lean`
- [`idMinus_isTraceAnnihilating`](../../StandardFacts/idMinus_isTraceAnnihilating.md) from `StandardFacts.lean`
- [`traceNorm_apply_le_diamond`](../../StandardFacts/traceNorm_apply_le_diamond.md) from `StandardFacts.lean`
- [`lemma_transpose_diamond`](../../StandardFacts/lemma_transpose_diamond.md) from `StandardFacts.lean`
- [`exists_maximizing_state`](../../StandardFacts/exists_maximizing_state.md) from `StandardFacts.lean`
- [`partialTranspose_rank_upper_bound`](partialTranspose_rank_upper_bound.md) from `PositiveGap/NotTight.lean`
- [`tensorWithIdentity_trace_zero`](../../StandardFacts/tensorWithIdentity_trace_zero.md) from `StandardFacts.lean`
- [`tensorWithIdentity_hermitian`](../../StandardFacts/tensorWithIdentity_hermitian.md) from `StandardFacts.lean`
- [`lemma1`](../../Theorem/Lemma1/lemma1.md) from `Theorem/Lemma1.lean`
- [`lemma2`](../../Theorem/Lemma2/lemma2.md) from `Theorem/Lemma2.lean`
- [`lemma3`](../../Theorem/Lemma3/lemma3.md) from `Theorem/Lemma3.lean`
- [`theorem1`](../../Theorem/Theorem1/theorem1.md) from `Theorem/Theorem1.lean`
- [`corollary1`](../Corollary1/corollary1.md) from `PositiveGap/Corollary1.lean`
- [`lemma1_eq_imp_rank_two`](lemma1_eq_imp_rank_two.md) from `PositiveGap/NotTight.lean`
- [`lemma2_eq_imp_full_rank`](lemma2_eq_imp_full_rank.md) from `PositiveGap/NotTight.lean`
- [`partialTranspose_ne_zero_of_ne_zero`](partialTranspose_ne_zero_of_ne_zero.md) from `PositiveGap/NotTight.lean`

### Later declarations that use this one
- No later documented declaration mentions this name explicitly.

## Backlinks

- [Back to `INDEX.md`](../../INDEX.md)
- [Back to the `PositiveGap/NotTight.lean` section in the index](../../INDEX.md#diamond-positivegap-nottight-lean)
- [Previous declaration in this file](partialTranspose_ne_zero_of_ne_zero.md)
