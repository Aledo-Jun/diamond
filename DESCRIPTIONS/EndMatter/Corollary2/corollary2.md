# corollary2

## Source location

- Original Lean file: `Diamond/EndMatter/Corollary2.lean`
- Declaration name: `corollary2`
- Declaration kind: `theorem`

## Why this declaration exists

This is the final coding statement: the improved finite-error Holevo--Werner converse written in terms of encoder, decoder, blocklength, and decoding error.

 In the file `EndMatter/Corollary2.lean`, it contributes to the coding-theoretic corollary stated in terms of encoder, decoder, and effective channel. Later proofs call this result by name, so documenting it makes the larger argument readable as a mathematical chain rather than as opaque proof script.

## Original code

```lean
/-- Paper Corollary 2, stated directly in terms of encoder, decoder,
    `m` channel uses, and the diamond-norm decoding error. -/
theorem corollary2
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
  let msgDim : ℝ := Fintype.card msg
  let delta : ℝ := 1 - Real.sqrt 2 * ε
  let bound : ℝ := diamondOp ((transposeMap phys).comp T)
  have hlinear : delta * msgDim ≤ bound ^ m := by
    simpa [delta, msgDim, bound] using
      corollary2_linear_bound T m encoder decoder tensorPower ε
        heffective htranspose_triangle htranspose_code_bound herror
  have hm_real : 0 < (m : ℝ) := by exact_mod_cast hm
  have hmsgDim_pos : 0 < msgDim := by
    have hcard_pos : 0 < Fintype.card msg := Fintype.card_pos_iff.mpr inferInstance
    simpa [msgDim] using
      (show (0 : ℝ) < (Fintype.card msg : ℝ) from by exact_mod_cast hcard_pos)
  have hdelta_pos : 0 < delta := by
    have hdelta_pos' : 0 < 1 - Real.sqrt 2 * ε := by
      have hsqrt2_pos : 0 < Real.sqrt 2 := by positivity
      have hsqrt2_ne : Real.sqrt 2 ≠ 0 := by positivity
      have hmul : Real.sqrt 2 * ε < 1 := by
        calc
          Real.sqrt 2 * ε < Real.sqrt 2 * (1 / Real.sqrt 2) := by
            exact mul_lt_mul_of_pos_left hε hsqrt2_pos
          _ = 1 := by
            field_simp [hsqrt2_ne]
      nlinarith
    simpa [delta] using hdelta_pos'
  have hlog :
      Real.logb 2 (delta * msgDim) ≤ Real.logb 2 (bound ^ m) := by
    exact Real.logb_le_logb_of_le (b := 2) (by norm_num) (mul_pos hdelta_pos hmsgDim_pos) hlinear
  have hlog' :
      Real.logb 2 delta + Real.logb 2 msgDim ≤ (m : ℝ) * Real.logb 2 bound := by
    simpa [delta, msgDim, bound, Real.logb_mul (ne_of_gt hdelta_pos) (ne_of_gt hmsgDim_pos),
      Real.logb_pow] using hlog
  have hmain :
      Real.logb 2 msgDim ≤
        (m : ℝ) * Real.logb 2 bound + Real.logb 2 (1 / delta) := by
    have htmp : Real.logb 2 msgDim ≤ (m : ℝ) * Real.logb 2 bound - Real.logb 2 delta := by
      linarith
    calc
      Real.logb 2 msgDim ≤ (m : ℝ) * Real.logb 2 bound - Real.logb 2 delta := htmp
      _ = (m : ℝ) * Real.logb 2 bound + Real.logb 2 (1 / delta) := by
        have hlog_inv : -Real.logb 2 delta = Real.logb 2 (1 / delta) := by
          rw [one_div]
          exact (Real.logb_inv 2 delta).symm
        rw [sub_eq_add_neg]
        rw [hlog_inv]
  refine (div_le_iff₀ hm_real).2 ?_
  have hm_ne : (m : ℝ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hm
  calc
    Real.logb 2 msgDim ≤ (m : ℝ) * Real.logb 2 bound + Real.logb 2 (1 / delta) := hmain
    _ = (Real.logb 2 bound + (1 / (m : ℝ)) * Real.logb 2 (1 / delta)) * (m : ℝ) := by
      field_simp [hm_ne]
    _ = (Real.logb 2 (diamondOp ((transposeMap phys).comp T)) +
          (1 / (m : ℝ)) * Real.logb 2 (1 / (1 - Real.sqrt 2 * ε))) * (m : ℝ) := by
      simp [delta, bound]
```

## Line-by-line explanation

The explanation below follows the declaration one physical line at a time. For long proofs, some lines are tiny bookkeeping steps; those are still explained, but briefly.

1. Code:
```lean
/-- Paper Corollary 2, stated directly in terms of encoder, decoder,
```
This is a Lean docstring. It is a human-written comment that tells readers what the declaration is meant to express before the formal code begins.

2. Code:
```lean
    `m` channel uses, and the diamond-norm decoding error. -/
```
This line is one local step in the declaration. It either refines the formula being defined or advances the proof by a small algebraic or logical move.

3. Code:
```lean
theorem corollary2
```
This line starts the `corollary2` declaration. Because it begins with `theorem`, Lean now knows what kind of named object is being introduced.

4. Code:
```lean
    {phys msg : Type u}
```
This line is one local step in the declaration. It either refines the formula being defined or advances the proof by a small algebraic or logical move.

5. Code:
```lean
    [Fintype phys] [DecidableEq phys]
```
This line is one local step in the declaration. It either refines the formula being defined or advances the proof by a small algebraic or logical move.  A bracket such as `[Fintype d]` tells Lean that the index set `d` is finite, so sums over all indices make sense.  A bracket such as `[DecidableEq d]` tells Lean that it can decide whether two indices are equal.

6. Code:
```lean
    [Fintype msg] [DecidableEq msg] [Nonempty msg]
```
This line is one local step in the declaration. It either refines the formula being defined or advances the proof by a small algebraic or logical move.  A bracket such as `[Fintype d]` tells Lean that the index set `d` is finite, so sums over all indices make sense.  A bracket such as `[DecidableEq d]` tells Lean that it can decide whether two indices are equal.

7. Code:
```lean
    (T : Channel phys) (m : ℕ)
```
This line is one local step in the declaration. It either refines the formula being defined or advances the proof by a small algebraic or logical move.  `Channel d` is an abbreviation for a complex-linear map from operators on `d` to operators on `d`.

8. Code:
```lean
    (encoder : Superoperator msg phys)
```
This line is one local step in the declaration. It either refines the formula being defined or advances the proof by a small algebraic or logical move.

9. Code:
```lean
    (decoder : Superoperator phys msg)
```
This line is one local step in the declaration. It either refines the formula being defined or advances the proof by a small algebraic or logical move.

10. Code:
```lean
    (tensorPower : Channel phys)
```
This line is one local step in the declaration. It either refines the formula being defined or advances the proof by a small algebraic or logical move.  `Channel d` is an abbreviation for a complex-linear map from operators on `d` to operators on `d`.

11. Code:
```lean
    (ε : ℝ)
```
This line is one local step in the declaration. It either refines the formula being defined or advances the proof by a small algebraic or logical move.

12. Code:
```lean
    (heffective :
```
This line is one local step in the declaration. It either refines the formula being defined or advances the proof by a small algebraic or logical move.

13. Code:
```lean
      IsQuantumChannel (effectiveChannel encoder decoder tensorPower))
```
This line is one local step in the declaration. It either refines the formula being defined or advances the proof by a small algebraic or logical move.  `Channel d` is an abbreviation for a complex-linear map from operators on `d` to operators on `d`.

14. Code:
```lean
    (htranspose_triangle :
```
This line is one local step in the declaration. It either refines the formula being defined or advances the proof by a small algebraic or logical move.

15. Code:
```lean
      diamondOp (transposeMap msg) ≤
```
This line is one local step in the declaration. It either refines the formula being defined or advances the proof by a small algebraic or logical move.

16. Code:
```lean
        diamondOp
```
This line is one local step in the declaration. It either refines the formula being defined or advances the proof by a small algebraic or logical move.

17. Code:
```lean
          ((transposeMap msg).comp (effectiveChannel encoder decoder tensorPower)) +
```
This line is one local step in the declaration. It either refines the formula being defined or advances the proof by a small algebraic or logical move.  `Channel d` is an abbreviation for a complex-linear map from operators on `d` to operators on `d`.  `comp` means composition of maps: one map is applied after another.

18. Code:
```lean
            diamondOp
```
This line is one local step in the declaration. It either refines the formula being defined or advances the proof by a small algebraic or logical move.

19. Code:
```lean
              ((transposeMap msg).comp
```
This line is one local step in the declaration. It either refines the formula being defined or advances the proof by a small algebraic or logical move.  `comp` means composition of maps: one map is applied after another.

20. Code:
```lean
                (idMinus (effectiveChannel encoder decoder tensorPower))))
```
This line is one local step in the declaration. It either refines the formula being defined or advances the proof by a small algebraic or logical move.  `Channel d` is an abbreviation for a complex-linear map from operators on `d` to operators on `d`.

21. Code:
```lean
    (htranspose_code_bound :
```
This line is one local step in the declaration. It either refines the formula being defined or advances the proof by a small algebraic or logical move.

22. Code:
```lean
      diamondOp
```
This line is one local step in the declaration. It either refines the formula being defined or advances the proof by a small algebraic or logical move.

23. Code:
```lean
          ((transposeMap msg).comp (effectiveChannel encoder decoder tensorPower)) ≤
```
This line is one local step in the declaration. It either refines the formula being defined or advances the proof by a small algebraic or logical move.  `Channel d` is an abbreviation for a complex-linear map from operators on `d` to operators on `d`.  `comp` means composition of maps: one map is applied after another.

24. Code:
```lean
        (diamondOp ((transposeMap phys).comp T)) ^ m)
```
This line is one local step in the declaration. It either refines the formula being defined or advances the proof by a small algebraic or logical move.  `comp` means composition of maps: one map is applied after another.

25. Code:
```lean
    (herror :
```
This line is one local step in the declaration. It either refines the formula being defined or advances the proof by a small algebraic or logical move.

26. Code:
```lean
      ε =
```
This line is one local step in the declaration. It either refines the formula being defined or advances the proof by a small algebraic or logical move.

27. Code:
```lean
        (1 / 2 : ℝ) *
```
This line is one local step in the declaration. It either refines the formula being defined or advances the proof by a small algebraic or logical move.

28. Code:
```lean
          diamondOp (idMinus (effectiveChannel encoder decoder tensorPower)))
```
This line is one local step in the declaration. It either refines the formula being defined or advances the proof by a small algebraic or logical move.  `Channel d` is an abbreviation for a complex-linear map from operators on `d` to operators on `d`.

29. Code:
```lean
    (hm : 0 < m) (hε : ε < 1 / Real.sqrt 2) :
```
This line is one local step in the declaration. It either refines the formula being defined or advances the proof by a small algebraic or logical move.

30. Code:
```lean
    Real.logb 2 (Fintype.card msg : ℝ) / (m : ℝ) ≤
```
This line is one local step in the declaration. It either refines the formula being defined or advances the proof by a small algebraic or logical move.  `Fintype.card` is the size of a finite index set.

31. Code:
```lean
      Real.logb 2 (diamondOp ((transposeMap phys).comp T)) +
```
This line is one local step in the declaration. It either refines the formula being defined or advances the proof by a small algebraic or logical move.  `comp` means composition of maps: one map is applied after another.

32. Code:
```lean
        (1 / (m : ℝ)) * Real.logb 2 (1 / (1 - Real.sqrt 2 * ε)) := by
```
This line says that a proof script begins here. Everything indented underneath is a sequence of instructions that Lean will check step by step.

33. Code:
```lean
  let msgDim : ℝ := Fintype.card msg
```
This line gives a temporary name to an expression. Doing that makes later lines shorter and easier to read.  `Fintype.card` is the size of a finite index set.

34. Code:
```lean
  let delta : ℝ := 1 - Real.sqrt 2 * ε
```
This line gives a temporary name to an expression. Doing that makes later lines shorter and easier to read.

35. Code:
```lean
  let bound : ℝ := diamondOp ((transposeMap phys).comp T)
```
This line gives a temporary name to an expression. Doing that makes later lines shorter and easier to read.  `comp` means composition of maps: one map is applied after another.

36. Code:
```lean
  have hlinear : delta * msgDim ≤ bound ^ m := by
```
This line says that a proof script begins here. Everything indented underneath is a sequence of instructions that Lean will check step by step.

37. Code:
```lean
    simpa [delta, msgDim, bound] using
```
This line simplifies the goal using definitions and known equalities. `simpa` means that, after simplification, the desired statement matches a theorem Lean already has.

38. Code:
```lean
      corollary2_linear_bound T m encoder decoder tensorPower ε
```
This line is one local step in the declaration. It either refines the formula being defined or advances the proof by a small algebraic or logical move.

39. Code:
```lean
        heffective htranspose_triangle htranspose_code_bound herror
```
This line is one local step in the declaration. It either refines the formula being defined or advances the proof by a small algebraic or logical move.

40. Code:
```lean
  have hm_real : 0 < (m : ℝ) := by exact_mod_cast hm
```
This line introduces an intermediate claim. The proof pauses to establish a fact that will be used shortly afterwards.

41. Code:
```lean
  have hmsgDim_pos : 0 < msgDim := by
```
This line says that a proof script begins here. Everything indented underneath is a sequence of instructions that Lean will check step by step.

42. Code:
```lean
    have hcard_pos : 0 < Fintype.card msg := Fintype.card_pos_iff.mpr inferInstance
```
This line introduces an intermediate claim. The proof pauses to establish a fact that will be used shortly afterwards.  `Fintype.card` is the size of a finite index set.

43. Code:
```lean
    simpa [msgDim] using
```
This line simplifies the goal using definitions and known equalities. `simpa` means that, after simplification, the desired statement matches a theorem Lean already has.

44. Code:
```lean
      (show (0 : ℝ) < (Fintype.card msg : ℝ) from by exact_mod_cast hcard_pos)
```
This line is one local step in the declaration. It either refines the formula being defined or advances the proof by a small algebraic or logical move.  `Fintype.card` is the size of a finite index set.

45. Code:
```lean
  have hdelta_pos : 0 < delta := by
```
This line says that a proof script begins here. Everything indented underneath is a sequence of instructions that Lean will check step by step.

46. Code:
```lean
    have hdelta_pos' : 0 < 1 - Real.sqrt 2 * ε := by
```
This line says that a proof script begins here. Everything indented underneath is a sequence of instructions that Lean will check step by step.

47. Code:
```lean
      have hsqrt2_pos : 0 < Real.sqrt 2 := by positivity
```
This line introduces an intermediate claim. The proof pauses to establish a fact that will be used shortly afterwards.

48. Code:
```lean
      have hsqrt2_ne : Real.sqrt 2 ≠ 0 := by positivity
```
This line introduces an intermediate claim. The proof pauses to establish a fact that will be used shortly afterwards.

49. Code:
```lean
      have hmul : Real.sqrt 2 * ε < 1 := by
```
This line says that a proof script begins here. Everything indented underneath is a sequence of instructions that Lean will check step by step.

50. Code:
```lean
        calc
```
This line begins a chained calculation. Each displayed step that follows must be justified by the indented proof after `:= by`.

51. Code:
```lean
          Real.sqrt 2 * ε < Real.sqrt 2 * (1 / Real.sqrt 2) := by
```
This line says that a proof script begins here. Everything indented underneath is a sequence of instructions that Lean will check step by step.

52. Code:
```lean
            exact mul_lt_mul_of_pos_left hε hsqrt2_pos
```
This line finishes the current goal by giving Lean the exact theorem, lemma, or term that proves it.

53. Code:
```lean
          _ = 1 := by
```
This line says that a proof script begins here. Everything indented underneath is a sequence of instructions that Lean will check step by step.

54. Code:
```lean
            field_simp [hsqrt2_ne]
```
This line is one local step in the declaration. It either refines the formula being defined or advances the proof by a small algebraic or logical move.

55. Code:
```lean
      nlinarith
```
This line solves the current numerical inequality by combining the equalities and inequalities already available in the context.

56. Code:
```lean
    simpa [delta] using hdelta_pos'
```
This line simplifies the goal using definitions and known equalities. `simpa` means that, after simplification, the desired statement matches a theorem Lean already has.

57. Code:
```lean
  have hlog :
```
This line introduces an intermediate claim. The proof pauses to establish a fact that will be used shortly afterwards.

58. Code:
```lean
      Real.logb 2 (delta * msgDim) ≤ Real.logb 2 (bound ^ m) := by
```
This line says that a proof script begins here. Everything indented underneath is a sequence of instructions that Lean will check step by step.

59. Code:
```lean
    exact Real.logb_le_logb_of_le (b := 2) (by norm_num) (mul_pos hdelta_pos hmsgDim_pos) hlinear
```
This line finishes the current goal by giving Lean the exact theorem, lemma, or term that proves it.

60. Code:
```lean
  have hlog' :
```
This line introduces an intermediate claim. The proof pauses to establish a fact that will be used shortly afterwards.

61. Code:
```lean
      Real.logb 2 delta + Real.logb 2 msgDim ≤ (m : ℝ) * Real.logb 2 bound := by
```
This line says that a proof script begins here. Everything indented underneath is a sequence of instructions that Lean will check step by step.

62. Code:
```lean
    simpa [delta, msgDim, bound, Real.logb_mul (ne_of_gt hdelta_pos) (ne_of_gt hmsgDim_pos),
```
This line simplifies the goal using definitions and known equalities. `simpa` means that, after simplification, the desired statement matches a theorem Lean already has.

63. Code:
```lean
      Real.logb_pow] using hlog
```
This line is one local step in the declaration. It either refines the formula being defined or advances the proof by a small algebraic or logical move.

64. Code:
```lean
  have hmain :
```
This line introduces an intermediate claim. The proof pauses to establish a fact that will be used shortly afterwards.

65. Code:
```lean
      Real.logb 2 msgDim ≤
```
This line is one local step in the declaration. It either refines the formula being defined or advances the proof by a small algebraic or logical move.

66. Code:
```lean
        (m : ℝ) * Real.logb 2 bound + Real.logb 2 (1 / delta) := by
```
This line says that a proof script begins here. Everything indented underneath is a sequence of instructions that Lean will check step by step.

67. Code:
```lean
    have htmp : Real.logb 2 msgDim ≤ (m : ℝ) * Real.logb 2 bound - Real.logb 2 delta := by
```
This line says that a proof script begins here. Everything indented underneath is a sequence of instructions that Lean will check step by step.

68. Code:
```lean
      linarith
```
This line solves the current numerical inequality by combining the equalities and inequalities already available in the context.

69. Code:
```lean
    calc
```
This line begins a chained calculation. Each displayed step that follows must be justified by the indented proof after `:= by`.

70. Code:
```lean
      Real.logb 2 msgDim ≤ (m : ℝ) * Real.logb 2 bound - Real.logb 2 delta := htmp
```
This line is one local step in the declaration. It either refines the formula being defined or advances the proof by a small algebraic or logical move.

71. Code:
```lean
      _ = (m : ℝ) * Real.logb 2 bound + Real.logb 2 (1 / delta) := by
```
This line says that a proof script begins here. Everything indented underneath is a sequence of instructions that Lean will check step by step.

72. Code:
```lean
        have hlog_inv : -Real.logb 2 delta = Real.logb 2 (1 / delta) := by
```
This line says that a proof script begins here. Everything indented underneath is a sequence of instructions that Lean will check step by step.

73. Code:
```lean
          rw [one_div]
```
This line uses rewriting. Lean replaces one expression by an equal expression using the lemmas listed in brackets.

74. Code:
```lean
          exact (Real.logb_inv 2 delta).symm
```
This line finishes the current goal by giving Lean the exact theorem, lemma, or term that proves it.

75. Code:
```lean
        rw [sub_eq_add_neg]
```
This line uses rewriting. Lean replaces one expression by an equal expression using the lemmas listed in brackets.

76. Code:
```lean
        rw [hlog_inv]
```
This line uses rewriting. Lean replaces one expression by an equal expression using the lemmas listed in brackets.

77. Code:
```lean
  refine (div_le_iff₀ hm_real).2 ?_
```
This line is a more controlled version of `apply`. It sets up the proof with a partly specified argument and leaves smaller goals to solve next.

78. Code:
```lean
  have hm_ne : (m : ℝ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hm
```
This line introduces an intermediate claim. The proof pauses to establish a fact that will be used shortly afterwards.

79. Code:
```lean
  calc
```
This line begins a chained calculation. Each displayed step that follows must be justified by the indented proof after `:= by`.

80. Code:
```lean
    Real.logb 2 msgDim ≤ (m : ℝ) * Real.logb 2 bound + Real.logb 2 (1 / delta) := hmain
```
This line is one local step in the declaration. It either refines the formula being defined or advances the proof by a small algebraic or logical move.

81. Code:
```lean
    _ = (Real.logb 2 bound + (1 / (m : ℝ)) * Real.logb 2 (1 / delta)) * (m : ℝ) := by
```
This line says that a proof script begins here. Everything indented underneath is a sequence of instructions that Lean will check step by step.

82. Code:
```lean
      field_simp [hm_ne]
```
This line is one local step in the declaration. It either refines the formula being defined or advances the proof by a small algebraic or logical move.

83. Code:
```lean
    _ = (Real.logb 2 (diamondOp ((transposeMap phys).comp T)) +
```
This line is one step inside a `calc` block. Lean is checking that the new expression really follows from the previous one.  `comp` means composition of maps: one map is applied after another.

84. Code:
```lean
          (1 / (m : ℝ)) * Real.logb 2 (1 / (1 - Real.sqrt 2 * ε))) * (m : ℝ) := by
```
This line says that a proof script begins here. Everything indented underneath is a sequence of instructions that Lean will check step by step.

85. Code:
```lean
      simp [delta, bound]
```
This line simplifies the goal using definitions and known equalities. `simpa` means that, after simplification, the desired statement matches a theorem Lean already has.

## Mathematical summary

Restated without Lean syntax, `corollary2` is the theorem or lemma written above.

- Apply `remark1` to the effective channel seen by the coding scheme.
- Use the decoding error identity to convert the diamond norm of `idMinus` of the effective channel into the parameter $\varepsilon$.
- Combine the resulting linear estimate with the assumed transposed-channel code bound.
- Take logarithms and divide by the blocklength to obtain the final rate inequality.

## Dependencies and downstream use

### Earlier declarations this depends on
- [`Channel`](../../Setups/Channel.md) from `Setups.lean`
- [`IsQuantumChannel`](../../Setups/IsQuantumChannel.md) from `Setups.lean`
- [`transposeMap`](../../Setups/transposeMap.md) from `Setups.lean`
- [`diamondOp`](../../Setups/diamondOp.md) from `Setups.lean`
- [`idMinus`](../../Setups/idMinus.md) from `Setups.lean`
- [`Superoperator`](Superoperator.md) from `EndMatter/Corollary2.lean`
- [`effectiveChannel`](effectiveChannel.md) from `EndMatter/Corollary2.lean`
- [`corollary2_linear_bound`](corollary2_linear_bound.md) from `EndMatter/Corollary2.lean`

### Later declarations that use this one
- No later documented declaration mentions this name explicitly.

## Backlinks

- [Back to `INDEX.md`](../../INDEX.md)
- [Back to the `EndMatter/Corollary2.lean` section in the index](../../INDEX.md#diamond-endmatter-corollary2-lean)
- [Previous declaration in this file](corollary2_linear_bound.md)