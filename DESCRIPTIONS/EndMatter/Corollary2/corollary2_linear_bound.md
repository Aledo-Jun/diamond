# corollary2_linear_bound

## Source location

- Original Lean file: `Diamond/EndMatter/Corollary2.lean`
- Declaration name: `corollary2_linear_bound`
- Declaration kind: `theorem`

## Why this declaration exists

This theorem extracts the linear inequality that sits behind the logarithmic coding bound.

 In the file `EndMatter/Corollary2.lean`, it contributes to the coding-theoretic corollary stated in terms of encoder, decoder, and effective channel. Later proofs call this result by name, so documenting it makes the larger argument readable as a mathematical chain rather than as opaque proof script.

## Original code

```lean
/-- The linear estimate underlying the improved Holevo-Werner finite-error converse. -/
theorem corollary2_linear_bound
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
  have hrem :=
    remark1 (d := msg) (Ψ := idMinus effective)
      (hH := idMinus_isHermiticityPreserving effective heffective)
      (hT := idMinus_isTraceAnnihilating effective heffective)
  have hsqrt2_ne : Real.sqrt 2 ≠ 0 := by positivity
  have herror_eq : diamondOp (idMinus effective) = 2 * ε := by
    nlinarith [herror]
  have herror_bound :
      diamondOp ((transposeMap msg).comp (idMinus effective)) ≤
        Real.sqrt 2 * (Fintype.card msg : ℝ) * ε := by
    have hcard : (Fintype.card (msg × msg) : ℝ) = (Fintype.card msg : ℝ) ^ (2 : ℕ) := by
      simp [Fintype.card_prod, Nat.cast_mul, pow_two]
    have hsqrt_msg : Real.sqrt (Fintype.card (msg × msg) : ℝ) = (Fintype.card msg : ℝ) := by
      calc
        Real.sqrt (Fintype.card (msg × msg) : ℝ)
            = Real.sqrt ((Fintype.card msg : ℝ) ^ (2 : ℕ)) := by
              rw [hcard]
        _ = Fintype.card msg := by
              rw [Real.sqrt_sq_eq_abs]
              have hnn : 0 ≤ (Fintype.card msg : ℝ) := by positivity
              simp [abs_of_nonneg hnn]
    calc
      diamondOp ((transposeMap msg).comp (idMinus effective)) ≤
          (1 / Real.sqrt 2) * diamondOp (transposeMap msg) * diamondOp (idMinus effective) :=
        hrem
      _ = (1 / Real.sqrt 2) * Real.sqrt (Fintype.card (msg × msg) : ℝ) * (2 * ε) := by
        rw [lemma_transpose_diamond (d := msg), herror_eq]
      _ = (1 / Real.sqrt 2) * (Fintype.card msg : ℝ) * (2 * ε) := by
        rw [hsqrt_msg]
      _ = Real.sqrt 2 * (Fintype.card msg : ℝ) * ε := by
        have hsqrt2 : 2 / Real.sqrt 2 = Real.sqrt 2 := by
          apply (div_eq_iff hsqrt2_ne).2
          nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 2 by positivity)]
        calc
          (1 / Real.sqrt 2) * (Fintype.card msg : ℝ) * (2 * ε)
              = ((2 / Real.sqrt 2) * (Fintype.card msg : ℝ)) * ε := by ring
          _ = (Real.sqrt 2 * (Fintype.card msg : ℝ)) * ε := by rw [hsqrt2]
          _ = Real.sqrt 2 * (Fintype.card msg : ℝ) * ε := by ring
  have hcard : (Fintype.card (msg × msg) : ℝ) = (Fintype.card msg : ℝ) ^ (2 : ℕ) := by
    simp [Fintype.card_prod, Nat.cast_mul, pow_two]
  have hsqrt_msg : Real.sqrt (Fintype.card (msg × msg) : ℝ) = (Fintype.card msg : ℝ) := by
    calc
      Real.sqrt (Fintype.card (msg × msg) : ℝ)
          = Real.sqrt ((Fintype.card msg : ℝ) ^ (2 : ℕ)) := by
            rw [hcard]
      _ = Fintype.card msg := by
            rw [Real.sqrt_sq_eq_abs]
            have hnn : 0 ≤ (Fintype.card msg : ℝ) := by positivity
            simp [abs_of_nonneg hnn]
  rw [lemma_transpose_diamond (d := msg)] at htranspose_triangle
  rw [hsqrt_msg] at htranspose_triangle
  have hlinear :
      (1 - Real.sqrt 2 * ε) * (Fintype.card msg : ℝ) ≤
        diamondOp ((transposeMap msg).comp effective) := by
    nlinarith [htranspose_triangle, herror_bound]
  calc
    (1 - Real.sqrt 2 * ε) * (Fintype.card msg : ℝ) ≤
        diamondOp ((transposeMap msg).comp effective) := hlinear
    _ ≤ (diamondOp ((transposeMap phys).comp T)) ^ m := htranspose_code_bound
```

## Block-by-block explanation

The explanation below follows the declaration block by block. Each block groups a coherent piece of the definition or proof, so the mathematical structure is easier to see than in a strictly line-oriented reading.

1. Code:
```lean
/-- The linear estimate underlying the improved Holevo-Werner finite-error converse. -/
```
This is a Lean docstring. It is a human-written comment that tells readers what the declaration is meant to express before the formal code begins.

2. Code:
```lean
theorem corollary2_linear_bound
```
This line starts the `corollary2_linear_bound` declaration. Because it begins with `theorem`, Lean now knows what kind of named object is being introduced.

3. Code:
```lean
    {phys msg : Type u}
```
This line is one local step in the declaration. It either refines the formula being defined or advances the proof by a small algebraic or logical move.

4. Code:
```lean
    [Fintype phys] [DecidableEq phys]
```
This line is one local step in the declaration. It either refines the formula being defined or advances the proof by a small algebraic or logical move.  A bracket such as `[Fintype d]` tells Lean that the index set `d` is finite, so sums over all indices make sense.  A bracket such as `[DecidableEq d]` tells Lean that it can decide whether two indices are equal.

5. Code:
```lean
    [Fintype msg] [DecidableEq msg] [Nonempty msg]
```
This line is one local step in the declaration. It either refines the formula being defined or advances the proof by a small algebraic or logical move.  A bracket such as `[Fintype d]` tells Lean that the index set `d` is finite, so sums over all indices make sense.  A bracket such as `[DecidableEq d]` tells Lean that it can decide whether two indices are equal.

6. Code:
```lean
    (T : Channel phys) (m : ℕ)
```
This line is one local step in the declaration. It either refines the formula being defined or advances the proof by a small algebraic or logical move.  `Channel d` is an abbreviation for a complex-linear map from operators on `d` to operators on `d`.

7. Code:
```lean
    (encoder : Superoperator msg phys)
```
This line is one local step in the declaration. It either refines the formula being defined or advances the proof by a small algebraic or logical move.

8. Code:
```lean
    (decoder : Superoperator phys msg)
```
This line is one local step in the declaration. It either refines the formula being defined or advances the proof by a small algebraic or logical move.

9. Code:
```lean
    (tensorPower : Channel phys)
```
This line is one local step in the declaration. It either refines the formula being defined or advances the proof by a small algebraic or logical move.  `Channel d` is an abbreviation for a complex-linear map from operators on `d` to operators on `d`.

10. Code:
```lean
    (ε : ℝ)
```
This line is one local step in the declaration. It either refines the formula being defined or advances the proof by a small algebraic or logical move.

11. Code:
```lean
    (heffective :
```
This line is one local step in the declaration. It either refines the formula being defined or advances the proof by a small algebraic or logical move.

12. Code:
```lean
      IsQuantumChannel (effectiveChannel encoder decoder tensorPower))
```
This line is one local step in the declaration. It either refines the formula being defined or advances the proof by a small algebraic or logical move.  `Channel d` is an abbreviation for a complex-linear map from operators on `d` to operators on `d`.

13. Code:
```lean
    (htranspose_triangle :
```
This line is one local step in the declaration. It either refines the formula being defined or advances the proof by a small algebraic or logical move.

14. Code:
```lean
      diamondOp (transposeMap msg) ≤
```
This line is one local step in the declaration. It either refines the formula being defined or advances the proof by a small algebraic or logical move.

15. Code:
```lean
        diamondOp
```
This line is one local step in the declaration. It either refines the formula being defined or advances the proof by a small algebraic or logical move.

16. Code:
```lean
          ((transposeMap msg).comp (effectiveChannel encoder decoder tensorPower)) +
```
This line is one local step in the declaration. It either refines the formula being defined or advances the proof by a small algebraic or logical move.  `Channel d` is an abbreviation for a complex-linear map from operators on `d` to operators on `d`.  `comp` means composition of maps: one map is applied after another.

17. Code:
```lean
            diamondOp
```
This line is one local step in the declaration. It either refines the formula being defined or advances the proof by a small algebraic or logical move.

18. Code:
```lean
              ((transposeMap msg).comp
```
This line is one local step in the declaration. It either refines the formula being defined or advances the proof by a small algebraic or logical move.  `comp` means composition of maps: one map is applied after another.

19. Code:
```lean
                (idMinus (effectiveChannel encoder decoder tensorPower))))
```
This line is one local step in the declaration. It either refines the formula being defined or advances the proof by a small algebraic or logical move.  `Channel d` is an abbreviation for a complex-linear map from operators on `d` to operators on `d`.

20. Code:
```lean
    (htranspose_code_bound :
```
This line is one local step in the declaration. It either refines the formula being defined or advances the proof by a small algebraic or logical move.

21. Code:
```lean
      diamondOp
```
This line is one local step in the declaration. It either refines the formula being defined or advances the proof by a small algebraic or logical move.

22. Code:
```lean
          ((transposeMap msg).comp (effectiveChannel encoder decoder tensorPower)) ≤
```
This line is one local step in the declaration. It either refines the formula being defined or advances the proof by a small algebraic or logical move.  `Channel d` is an abbreviation for a complex-linear map from operators on `d` to operators on `d`.  `comp` means composition of maps: one map is applied after another.

23. Code:
```lean
        (diamondOp ((transposeMap phys).comp T)) ^ m)
```
This line is one local step in the declaration. It either refines the formula being defined or advances the proof by a small algebraic or logical move.  `comp` means composition of maps: one map is applied after another.

24. Code:
```lean
    (herror :
```
This line is one local step in the declaration. It either refines the formula being defined or advances the proof by a small algebraic or logical move.

25. Code:
```lean
      ε =
```
This line is one local step in the declaration. It either refines the formula being defined or advances the proof by a small algebraic or logical move.

26. Code:
```lean
        (1 / 2 : ℝ) *
```
This line is one local step in the declaration. It either refines the formula being defined or advances the proof by a small algebraic or logical move.

27. Code:
```lean
          diamondOp (idMinus (effectiveChannel encoder decoder tensorPower))) :
```
This line is one local step in the declaration. It either refines the formula being defined or advances the proof by a small algebraic or logical move.  `Channel d` is an abbreviation for a complex-linear map from operators on `d` to operators on `d`.

28. Code:
```lean
    (1 - Real.sqrt 2 * ε) * (Fintype.card msg : ℝ) ≤
```
This line is one local step in the declaration. It either refines the formula being defined or advances the proof by a small algebraic or logical move.  `Fintype.card` is the size of a finite index set.

29. Code:
```lean
      (diamondOp ((transposeMap phys).comp T)) ^ m := by
```
This line says that a proof script begins here. Everything indented underneath is a sequence of instructions that Lean will check step by step.  `comp` means composition of maps: one map is applied after another.

30. Code:
```lean
  let effective := effectiveChannel encoder decoder tensorPower
```
This line gives a temporary name to an expression. Doing that makes later lines shorter and easier to read.  `Channel d` is an abbreviation for a complex-linear map from operators on `d` to operators on `d`.

31. Code:
```lean
  have hrem :=
```
This line introduces an intermediate claim. The proof pauses to establish a fact that will be used shortly afterwards.

32. Code:
```lean
    remark1 (d := msg) (Ψ := idMinus effective)
```
This line is one local step in the declaration. It either refines the formula being defined or advances the proof by a small algebraic or logical move.

33. Code:
```lean
      (hH := idMinus_isHermiticityPreserving effective heffective)
```
This line is one local step in the declaration. It either refines the formula being defined or advances the proof by a small algebraic or logical move.

34. Code:
```lean
      (hT := idMinus_isTraceAnnihilating effective heffective)
```
This line is one local step in the declaration. It either refines the formula being defined or advances the proof by a small algebraic or logical move.

35. Code:
```lean
  have hsqrt2_ne : Real.sqrt 2 ≠ 0 := by positivity
```
This line introduces an intermediate claim. The proof pauses to establish a fact that will be used shortly afterwards.

36. Code:
```lean
  have herror_eq : diamondOp (idMinus effective) = 2 * ε := by
```
This line says that a proof script begins here. Everything indented underneath is a sequence of instructions that Lean will check step by step.

37. Code:
```lean
    nlinarith [herror]
```
This line solves the current numerical inequality by combining the equalities and inequalities already available in the context.

38. Code:
```lean
  have herror_bound :
```
This line introduces an intermediate claim. The proof pauses to establish a fact that will be used shortly afterwards.

39. Code:
```lean
      diamondOp ((transposeMap msg).comp (idMinus effective)) ≤
```
This line is one local step in the declaration. It either refines the formula being defined or advances the proof by a small algebraic or logical move.  `comp` means composition of maps: one map is applied after another.

40. Code:
```lean
        Real.sqrt 2 * (Fintype.card msg : ℝ) * ε := by
```
This line says that a proof script begins here. Everything indented underneath is a sequence of instructions that Lean will check step by step.  `Fintype.card` is the size of a finite index set.

41. Code:
```lean
    have hcard : (Fintype.card (msg × msg) : ℝ) = (Fintype.card msg : ℝ) ^ (2 : ℕ) := by
```
This line says that a proof script begins here. Everything indented underneath is a sequence of instructions that Lean will check step by step.  `Fintype.card` is the size of a finite index set.

42. Code:
```lean
      simp [Fintype.card_prod, Nat.cast_mul, pow_two]
```
This line simplifies the goal using definitions and known equalities. `simpa` means that, after simplification, the desired statement matches a theorem Lean already has.  A bracket such as `[Fintype d]` tells Lean that the index set `d` is finite, so sums over all indices make sense.  `Fintype.card` is the size of a finite index set.

43. Code:
```lean
    have hsqrt_msg : Real.sqrt (Fintype.card (msg × msg) : ℝ) = (Fintype.card msg : ℝ) := by
```
This line says that a proof script begins here. Everything indented underneath is a sequence of instructions that Lean will check step by step.  `Fintype.card` is the size of a finite index set.

44. Code:
```lean
      calc
```
This line begins a chained calculation. Each displayed step that follows must be justified by the indented proof after `:= by`.

45. Code:
```lean
        Real.sqrt (Fintype.card (msg × msg) : ℝ)
```
This line is one local step in the declaration. It either refines the formula being defined or advances the proof by a small algebraic or logical move.  `Fintype.card` is the size of a finite index set.

46. Code:
```lean
            = Real.sqrt ((Fintype.card msg : ℝ) ^ (2 : ℕ)) := by
```
This line says that a proof script begins here. Everything indented underneath is a sequence of instructions that Lean will check step by step.  `Fintype.card` is the size of a finite index set.

47. Code:
```lean
              rw [hcard]
```
This line uses rewriting. Lean replaces one expression by an equal expression using the lemmas listed in brackets.

48. Code:
```lean
        _ = Fintype.card msg := by
```
This line says that a proof script begins here. Everything indented underneath is a sequence of instructions that Lean will check step by step.  `Fintype.card` is the size of a finite index set.

49. Code:
```lean
              rw [Real.sqrt_sq_eq_abs]
```
This line uses rewriting. Lean replaces one expression by an equal expression using the lemmas listed in brackets.

50. Code:
```lean
              have hnn : 0 ≤ (Fintype.card msg : ℝ) := by positivity
```
This line introduces an intermediate claim. The proof pauses to establish a fact that will be used shortly afterwards.  `Fintype.card` is the size of a finite index set.

51. Code:
```lean
              simp [abs_of_nonneg hnn]
```
This line simplifies the goal using definitions and known equalities. `simpa` means that, after simplification, the desired statement matches a theorem Lean already has.

52. Code:
```lean
    calc
```
This line begins a chained calculation. Each displayed step that follows must be justified by the indented proof after `:= by`.

53. Code:
```lean
      diamondOp ((transposeMap msg).comp (idMinus effective)) ≤
```
This line is one local step in the declaration. It either refines the formula being defined or advances the proof by a small algebraic or logical move.  `comp` means composition of maps: one map is applied after another.

54. Code:
```lean
          (1 / Real.sqrt 2) * diamondOp (transposeMap msg) * diamondOp (idMinus effective) :=
```
This line is one local step in the declaration. It either refines the formula being defined or advances the proof by a small algebraic or logical move.

55. Code:
```lean
        hrem
```
This line is one local step in the declaration. It either refines the formula being defined or advances the proof by a small algebraic or logical move.

56. Code:
```lean
      _ = (1 / Real.sqrt 2) * Real.sqrt (Fintype.card (msg × msg) : ℝ) * (2 * ε) := by
```
This line says that a proof script begins here. Everything indented underneath is a sequence of instructions that Lean will check step by step.  `Fintype.card` is the size of a finite index set.

57. Code:
```lean
        rw [lemma_transpose_diamond (d := msg), herror_eq]
```
This line uses rewriting. Lean replaces one expression by an equal expression using the lemmas listed in brackets.

58. Code:
```lean
      _ = (1 / Real.sqrt 2) * (Fintype.card msg : ℝ) * (2 * ε) := by
```
This line says that a proof script begins here. Everything indented underneath is a sequence of instructions that Lean will check step by step.  `Fintype.card` is the size of a finite index set.

59. Code:
```lean
        rw [hsqrt_msg]
```
This line uses rewriting. Lean replaces one expression by an equal expression using the lemmas listed in brackets.

60. Code:
```lean
      _ = Real.sqrt 2 * (Fintype.card msg : ℝ) * ε := by
```
This line says that a proof script begins here. Everything indented underneath is a sequence of instructions that Lean will check step by step.  `Fintype.card` is the size of a finite index set.

61. Code:
```lean
        have hsqrt2 : 2 / Real.sqrt 2 = Real.sqrt 2 := by
```
This line says that a proof script begins here. Everything indented underneath is a sequence of instructions that Lean will check step by step.

62. Code:
```lean
          apply (div_eq_iff hsqrt2_ne).2
```
This line applies an existing theorem to the current goal. Lean then asks the author to prove the theorem’s hypotheses.

63. Code:
```lean
          nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 2 by positivity)]
```
This line solves the current numerical inequality by combining the equalities and inequalities already available in the context.

64. Code:
```lean
        calc
```
This line begins a chained calculation. Each displayed step that follows must be justified by the indented proof after `:= by`.

65. Code:
```lean
          (1 / Real.sqrt 2) * (Fintype.card msg : ℝ) * (2 * ε)
```
This line is one local step in the declaration. It either refines the formula being defined or advances the proof by a small algebraic or logical move.  `Fintype.card` is the size of a finite index set.

66. Code:
```lean
              = ((2 / Real.sqrt 2) * (Fintype.card msg : ℝ)) * ε := by ring
```
This line is one local step in the declaration. It either refines the formula being defined or advances the proof by a small algebraic or logical move.  `Fintype.card` is the size of a finite index set.

67. Code:
```lean
          _ = (Real.sqrt 2 * (Fintype.card msg : ℝ)) * ε := by rw [hsqrt2]
```
This line is one step inside a `calc` block. Lean is checking that the new expression really follows from the previous one.  `Fintype.card` is the size of a finite index set.

68. Code:
```lean
          _ = Real.sqrt 2 * (Fintype.card msg : ℝ) * ε := by ring
```
This line is one step inside a `calc` block. Lean is checking that the new expression really follows from the previous one.  `Fintype.card` is the size of a finite index set.

69. Code:
```lean
  have hcard : (Fintype.card (msg × msg) : ℝ) = (Fintype.card msg : ℝ) ^ (2 : ℕ) := by
```
This line says that a proof script begins here. Everything indented underneath is a sequence of instructions that Lean will check step by step.  `Fintype.card` is the size of a finite index set.

70. Code:
```lean
    simp [Fintype.card_prod, Nat.cast_mul, pow_two]
```
This line simplifies the goal using definitions and known equalities. `simpa` means that, after simplification, the desired statement matches a theorem Lean already has.  A bracket such as `[Fintype d]` tells Lean that the index set `d` is finite, so sums over all indices make sense.  `Fintype.card` is the size of a finite index set.

71. Code:
```lean
  have hsqrt_msg : Real.sqrt (Fintype.card (msg × msg) : ℝ) = (Fintype.card msg : ℝ) := by
```
This line says that a proof script begins here. Everything indented underneath is a sequence of instructions that Lean will check step by step.  `Fintype.card` is the size of a finite index set.

72. Code:
```lean
    calc
```
This line begins a chained calculation. Each displayed step that follows must be justified by the indented proof after `:= by`.

73. Code:
```lean
      Real.sqrt (Fintype.card (msg × msg) : ℝ)
```
This line is one local step in the declaration. It either refines the formula being defined or advances the proof by a small algebraic or logical move.  `Fintype.card` is the size of a finite index set.

74. Code:
```lean
          = Real.sqrt ((Fintype.card msg : ℝ) ^ (2 : ℕ)) := by
```
This line says that a proof script begins here. Everything indented underneath is a sequence of instructions that Lean will check step by step.  `Fintype.card` is the size of a finite index set.

75. Code:
```lean
            rw [hcard]
```
This line uses rewriting. Lean replaces one expression by an equal expression using the lemmas listed in brackets.

76. Code:
```lean
      _ = Fintype.card msg := by
```
This line says that a proof script begins here. Everything indented underneath is a sequence of instructions that Lean will check step by step.  `Fintype.card` is the size of a finite index set.

77. Code:
```lean
            rw [Real.sqrt_sq_eq_abs]
```
This line uses rewriting. Lean replaces one expression by an equal expression using the lemmas listed in brackets.

78. Code:
```lean
            have hnn : 0 ≤ (Fintype.card msg : ℝ) := by positivity
```
This line introduces an intermediate claim. The proof pauses to establish a fact that will be used shortly afterwards.  `Fintype.card` is the size of a finite index set.

79. Code:
```lean
            simp [abs_of_nonneg hnn]
```
This line simplifies the goal using definitions and known equalities. `simpa` means that, after simplification, the desired statement matches a theorem Lean already has.

80. Code:
```lean
  rw [lemma_transpose_diamond (d := msg)] at htranspose_triangle
```
This line uses rewriting. Lean replaces one expression by an equal expression using the lemmas listed in brackets.

81. Code:
```lean
  rw [hsqrt_msg] at htranspose_triangle
```
This line uses rewriting. Lean replaces one expression by an equal expression using the lemmas listed in brackets.

82. Code:
```lean
  have hlinear :
```
This line introduces an intermediate claim. The proof pauses to establish a fact that will be used shortly afterwards.

83. Code:
```lean
      (1 - Real.sqrt 2 * ε) * (Fintype.card msg : ℝ) ≤
```
This line is one local step in the declaration. It either refines the formula being defined or advances the proof by a small algebraic or logical move.  `Fintype.card` is the size of a finite index set.

84. Code:
```lean
        diamondOp ((transposeMap msg).comp effective) := by
```
This line says that a proof script begins here. Everything indented underneath is a sequence of instructions that Lean will check step by step.  `comp` means composition of maps: one map is applied after another.

85. Code:
```lean
    nlinarith [htranspose_triangle, herror_bound]
```
This line solves the current numerical inequality by combining the equalities and inequalities already available in the context.

86. Code:
```lean
  calc
```
This line begins a chained calculation. Each displayed step that follows must be justified by the indented proof after `:= by`.

87. Code:
```lean
    (1 - Real.sqrt 2 * ε) * (Fintype.card msg : ℝ) ≤
```
This line is one local step in the declaration. It either refines the formula being defined or advances the proof by a small algebraic or logical move.  `Fintype.card` is the size of a finite index set.

88. Code:
```lean
        diamondOp ((transposeMap msg).comp effective) := hlinear
```
This line is one local step in the declaration. It either refines the formula being defined or advances the proof by a small algebraic or logical move.  `comp` means composition of maps: one map is applied after another.

89. Code:
```lean
    _ ≤ (diamondOp ((transposeMap phys).comp T)) ^ m := htranspose_code_bound
```
This line is one step inside a `calc` block. Lean is checking that the new expression really follows from the previous one.  `comp` means composition of maps: one map is applied after another.

## Mathematical summary

Restated without Lean syntax, `corollary2_linear_bound` is the theorem or lemma written above.

- State the desired identity or inequality in Lean’s syntax.
- Introduce temporary names and intermediate claims that organize the argument.
- Use rewriting, simplification, and earlier lemmas to reduce the goal to standard matrix or norm manipulations.
- Close the remaining algebraic or order-theoretic steps with Lean’s proof tactics.

## Dependencies and downstream use

### Earlier declarations this depends on
- [`Channel`](../../Setups/Channel.md) from `Setups.lean`
- [`IsQuantumChannel`](../../Setups/IsQuantumChannel.md) from `Setups.lean`
- [`transposeMap`](../../Setups/transposeMap.md) from `Setups.lean`
- [`diamondOp`](../../Setups/diamondOp.md) from `Setups.lean`
- [`idMinus`](../../Setups/idMinus.md) from `Setups.lean`
- [`idMinus_isHermiticityPreserving`](../../StandardFacts/idMinus_isHermiticityPreserving.md) from `StandardFacts.lean`
- [`idMinus_isTraceAnnihilating`](../../StandardFacts/idMinus_isTraceAnnihilating.md) from `StandardFacts.lean`
- [`lemma_transpose_diamond`](../../StandardFacts/lemma_transpose_diamond.md) from `StandardFacts.lean`
- [`remark1`](../../Theorem/Remark1/remark1.md) from `Theorem/Remark1.lean`
- [`Superoperator`](Superoperator.md) from `EndMatter/Corollary2.lean`
- [`effectiveChannel`](effectiveChannel.md) from `EndMatter/Corollary2.lean`

### Later declarations that use this one
- [`corollary2`](corollary2.md) in `EndMatter/Corollary2.lean`

## Backlinks

- [Back to `INDEX.md`](../../INDEX.md)
- [Back to the `EndMatter/Corollary2.lean` section in the index](../../INDEX.md#diamond-endmatter-corollary2-lean)
- [Previous declaration in this file](effectiveChannel.md)
- [Next declaration in this file](corollary2.md)