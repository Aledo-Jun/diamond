# lemma1

## Source location

- Original Lean file: `Diamond/Theorem/Lemma1.lean`
- Declaration name: `lemma1`
- Declaration kind: `theorem`

## Why this declaration exists

Lemma 1: For traceless Hermitian `X`, `‖X‖₂ ≤ (1 / √2) ‖X‖₁`.

 In the file `Theorem/Lemma1.lean`, it contributes to the proof infrastructure for the first norm inequality and the public theorem `lemma1`. Later proofs call this result by name, so documenting it makes the larger argument readable as a mathematical chain rather than as opaque proof script.

## Original code

```lean
/-- Lemma 1: For traceless Hermitian `X`, `‖X‖₂ ≤ (1 / √2) ‖X‖₁`. -/
theorem lemma1
    {d : Type u} [Fintype d] [DecidableEq d]
    (X : Matrix d d ℂ) (hHerm : Matrix.IsHermitian X) (hTrace : Matrix.trace X = 0) :
    hsNormOp X ≤ (1 / Real.sqrt 2) * traceNormOp X := by
  let p : d → ℝ := fun i => max (hHerm.eigenvalues i) 0
  let q : d → ℝ := fun i => max (-hHerm.eigenvalues i) 0
  have hp_nonneg : ∀ i, 0 ≤ p i := by
    intro i
    simp [p]
  have hq_nonneg : ∀ i, 0 ≤ q i := by
    intro i
    simp [q]
  have habs : ∀ i, |hHerm.eigenvalues i| = p i + q i := by
    intro i
    by_cases hi : 0 ≤ hHerm.eigenvalues i
    · simp [p, q, hi, abs_of_nonneg hi]
    · have hi' : hHerm.eigenvalues i < 0 := lt_of_not_ge hi
      simp [p, q, hi'.le, abs_of_neg hi']
  have hsub : ∀ i, hHerm.eigenvalues i = p i - q i := by
    intro i
    by_cases hi : 0 ≤ hHerm.eigenvalues i
    · simp [p, q, hi]
    · have hi' : hHerm.eigenvalues i < 0 := lt_of_not_ge hi
      simp [p, q, hi'.le]
  have hsq : ∀ i, (hHerm.eigenvalues i) ^ 2 = (p i) ^ 2 + (q i) ^ 2 := by
    intro i
    by_cases hi : 0 ≤ hHerm.eigenvalues i
    · simp [p, q, hi, pow_two]
    · have hi' : hHerm.eigenvalues i < 0 := lt_of_not_ge hi
      simp [p, q, hi'.le, pow_two]
  have hsum_zero : ∑ i, hHerm.eigenvalues i = 0 := by
    have htraceC : (∑ i, ((hHerm.eigenvalues i : ℝ) : ℂ)) = 0 := by
      simpa [hHerm.trace_eq_sum_eigenvalues] using hTrace
    exact_mod_cast congrArg Complex.re htraceC
  have hpq : ∑ i, p i = ∑ i, q i := by
    have hsum_sub : ∑ i, (p i - q i) = 0 := by
      simpa [hsub] using hsum_zero
    rw [Finset.sum_sub_distrib] at hsum_sub
    linarith
  have hsumsq_le : ∑ i, (hHerm.eigenvalues i) ^ 2 ≤ 2 * (∑ i, p i) ^ 2 := by
    calc
      ∑ i, (hHerm.eigenvalues i) ^ 2 = ∑ i, (p i) ^ 2 + ∑ i, (q i) ^ 2 := by
        simp [hsq, Finset.sum_add_distrib]
      _ ≤ (∑ i, p i) ^ 2 + (∑ i, q i) ^ 2 := by
        gcongr
        · exact Finset.sum_sq_le_sq_sum_of_nonneg (fun i _ => hp_nonneg i)
        · exact Finset.sum_sq_le_sq_sum_of_nonneg (fun i _ => hq_nonneg i)
      _ = 2 * (∑ i, p i) ^ 2 := by
        rw [hpq]
        ring
  have htraceNorm :
      (∑ i, |hHerm.eigenvalues i|) = 2 * ∑ i, p i := by
    calc
      (∑ i, |hHerm.eigenvalues i|) = ∑ i, (p i + q i) := by
        simp [habs]
      _ = ∑ i, p i + ∑ i, q i := by
        rw [Finset.sum_add_distrib]
      _ = 2 * ∑ i, p i := by
        rw [hpq]
        ring
  have hsqrt2_ne : Real.sqrt 2 ≠ 0 := by
    positivity
  have hrhs :
      ((1 / Real.sqrt 2) * (2 * ∑ i, p i)) ^ 2 = 2 * (∑ i, p i) ^ 2 := by
    field_simp [pow_two, hsqrt2_ne]
    nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 2 by positivity)]
  have hsqineq : hsNormOp X ^ 2 ≤ ((1 / Real.sqrt 2) * (∑ i, |hHerm.eigenvalues i|)) ^ 2 := by
    rw [hsNorm_sq_eq_re_trace_conjTranspose_mul_self,
      hermitian_re_trace_conjTranspose_mul_self_eq_sum_sq_eigenvalues hHerm]
    rw [htraceNorm, hrhs]
    exact hsumsq_le
  have hleft : 0 ≤ hsNormOp X := norm_nonneg _
  have hright : 0 ≤ (1 / Real.sqrt 2) * (∑ i, |hHerm.eigenvalues i|) := by
    positivity
  have hle_abs : hsNormOp X ≤ |(1 / Real.sqrt 2) * (∑ i, |hHerm.eigenvalues i|)| := by
    simpa [abs_of_nonneg hleft] using (sq_le_sq.mp hsqineq)
  calc
    hsNormOp X ≤ |(1 / Real.sqrt 2) * (∑ i, |hHerm.eigenvalues i|)| := hle_abs
    _ = (1 / Real.sqrt 2) * (∑ i, |hHerm.eigenvalues i|) := abs_of_nonneg hright
    _ = (1 / Real.sqrt 2) * traceNormOp X := by
      rw [traceNormOp_hermitian_eq_sum_abs_eigenvalues hHerm]
```

## Block-by-block explanation

The explanation below follows the declaration block by block. Each block groups a coherent piece of the definition or proof, so the mathematical structure is easier to see than in a strictly line-oriented reading.

1. Code:
```lean
/-- Lemma 1: For traceless Hermitian `X`, `‖X‖₂ ≤ (1 / √2) ‖X‖₁`. -/
```
This is a Lean docstring. It is a human-written comment that tells readers what the declaration is meant to express before the formal code begins.

2. Code:
```lean
theorem lemma1
```
This line starts the `lemma1` declaration. Because it begins with `theorem`, Lean now knows what kind of named object is being introduced.

3. Code:
```lean
    {d : Type u} [Fintype d] [DecidableEq d]
```
This line is one local step in the declaration. It either refines the formula being defined or advances the proof by a small algebraic or logical move.  A bracket such as `[Fintype d]` tells Lean that the index set `d` is finite, so sums over all indices make sense.  A bracket such as `[DecidableEq d]` tells Lean that it can decide whether two indices are equal.

4. Code:
```lean
    (X : Matrix d d ℂ) (hHerm : Matrix.IsHermitian X) (hTrace : Matrix.trace X = 0) :
```
This line is one local step in the declaration. It either refines the formula being defined or advances the proof by a small algebraic or logical move.  `Matrix d d ℂ` means a square matrix with complex entries; the index type `d` tells Lean which rows and columns exist.

5. Code:
```lean
    hsNormOp X ≤ (1 / Real.sqrt 2) * traceNormOp X := by
```
This line says that a proof script begins here. Everything indented underneath is a sequence of instructions that Lean will check step by step.

6. Code:
```lean
  let p : d → ℝ := fun i => max (hHerm.eigenvalues i) 0
```
This line gives a temporary name to an expression. Doing that makes later lines shorter and easier to read.

7. Code:
```lean
  let q : d → ℝ := fun i => max (-hHerm.eigenvalues i) 0
```
This line gives a temporary name to an expression. Doing that makes later lines shorter and easier to read.

8. Code:
```lean
  have hp_nonneg : ∀ i, 0 ≤ p i := by
```
This line says that a proof script begins here. Everything indented underneath is a sequence of instructions that Lean will check step by step.

9. Code:
```lean
    intro i
```
This line introduces the variable or hypothesis named here into the proof context. In ordinary mathematical prose, it is the same as saying “let” or “assume”.

10. Code:
```lean
    simp [p]
```
This line simplifies the goal using definitions and known equalities. `simpa` means that, after simplification, the desired statement matches a theorem Lean already has.

11. Code:
```lean
  have hq_nonneg : ∀ i, 0 ≤ q i := by
```
This line says that a proof script begins here. Everything indented underneath is a sequence of instructions that Lean will check step by step.

12. Code:
```lean
    intro i
```
This line introduces the variable or hypothesis named here into the proof context. In ordinary mathematical prose, it is the same as saying “let” or “assume”.

13. Code:
```lean
    simp [q]
```
This line simplifies the goal using definitions and known equalities. `simpa` means that, after simplification, the desired statement matches a theorem Lean already has.

14. Code:
```lean
  have habs : ∀ i, |hHerm.eigenvalues i| = p i + q i := by
```
This line says that a proof script begins here. Everything indented underneath is a sequence of instructions that Lean will check step by step.

15. Code:
```lean
    intro i
```
This line introduces the variable or hypothesis named here into the proof context. In ordinary mathematical prose, it is the same as saying “let” or “assume”.

16. Code:
```lean
    by_cases hi : 0 ≤ hHerm.eigenvalues i
```
This line splits the proof into cases according to whether the named proposition is true or false.

17. Code:
```lean
    · simp [p, q, hi, abs_of_nonneg hi]
```
This bullet starts a new subgoal produced by the previous tactic. Lean is now focusing on one branch of the argument.

18. Code:
```lean
    · have hi' : hHerm.eigenvalues i < 0 := lt_of_not_ge hi
```
This bullet starts a new subgoal produced by the previous tactic. Lean is now focusing on one branch of the argument.

19. Code:
```lean
      simp [p, q, hi'.le, abs_of_neg hi']
```
This line simplifies the goal using definitions and known equalities. `simpa` means that, after simplification, the desired statement matches a theorem Lean already has.

20. Code:
```lean
  have hsub : ∀ i, hHerm.eigenvalues i = p i - q i := by
```
This line says that a proof script begins here. Everything indented underneath is a sequence of instructions that Lean will check step by step.

21. Code:
```lean
    intro i
```
This line introduces the variable or hypothesis named here into the proof context. In ordinary mathematical prose, it is the same as saying “let” or “assume”.

22. Code:
```lean
    by_cases hi : 0 ≤ hHerm.eigenvalues i
```
This line splits the proof into cases according to whether the named proposition is true or false.

23. Code:
```lean
    · simp [p, q, hi]
```
This bullet starts a new subgoal produced by the previous tactic. Lean is now focusing on one branch of the argument.

24. Code:
```lean
    · have hi' : hHerm.eigenvalues i < 0 := lt_of_not_ge hi
```
This bullet starts a new subgoal produced by the previous tactic. Lean is now focusing on one branch of the argument.

25. Code:
```lean
      simp [p, q, hi'.le]
```
This line simplifies the goal using definitions and known equalities. `simpa` means that, after simplification, the desired statement matches a theorem Lean already has.

26. Code:
```lean
  have hsq : ∀ i, (hHerm.eigenvalues i) ^ 2 = (p i) ^ 2 + (q i) ^ 2 := by
```
This line says that a proof script begins here. Everything indented underneath is a sequence of instructions that Lean will check step by step.

27. Code:
```lean
    intro i
```
This line introduces the variable or hypothesis named here into the proof context. In ordinary mathematical prose, it is the same as saying “let” or “assume”.

28. Code:
```lean
    by_cases hi : 0 ≤ hHerm.eigenvalues i
```
This line splits the proof into cases according to whether the named proposition is true or false.

29. Code:
```lean
    · simp [p, q, hi, pow_two]
```
This bullet starts a new subgoal produced by the previous tactic. Lean is now focusing on one branch of the argument.

30. Code:
```lean
    · have hi' : hHerm.eigenvalues i < 0 := lt_of_not_ge hi
```
This bullet starts a new subgoal produced by the previous tactic. Lean is now focusing on one branch of the argument.

31. Code:
```lean
      simp [p, q, hi'.le, pow_two]
```
This line simplifies the goal using definitions and known equalities. `simpa` means that, after simplification, the desired statement matches a theorem Lean already has.

32. Code:
```lean
  have hsum_zero : ∑ i, hHerm.eigenvalues i = 0 := by
```
This line says that a proof script begins here. Everything indented underneath is a sequence of instructions that Lean will check step by step.

33. Code:
```lean
    have htraceC : (∑ i, ((hHerm.eigenvalues i : ℝ) : ℂ)) = 0 := by
```
This line says that a proof script begins here. Everything indented underneath is a sequence of instructions that Lean will check step by step.

34. Code:
```lean
      simpa [hHerm.trace_eq_sum_eigenvalues] using hTrace
```
This line simplifies the goal using definitions and known equalities. `simpa` means that, after simplification, the desired statement matches a theorem Lean already has.

35. Code:
```lean
    exact_mod_cast congrArg Complex.re htraceC
```
This line finishes the current goal by giving Lean the exact theorem, lemma, or term that proves it.

36. Code:
```lean
  have hpq : ∑ i, p i = ∑ i, q i := by
```
This line says that a proof script begins here. Everything indented underneath is a sequence of instructions that Lean will check step by step.

37. Code:
```lean
    have hsum_sub : ∑ i, (p i - q i) = 0 := by
```
This line says that a proof script begins here. Everything indented underneath is a sequence of instructions that Lean will check step by step.

38. Code:
```lean
      simpa [hsub] using hsum_zero
```
This line simplifies the goal using definitions and known equalities. `simpa` means that, after simplification, the desired statement matches a theorem Lean already has.

39. Code:
```lean
    rw [Finset.sum_sub_distrib] at hsum_sub
```
This line uses rewriting. Lean replaces one expression by an equal expression using the lemmas listed in brackets.

40. Code:
```lean
    linarith
```
This line solves the current numerical inequality by combining the equalities and inequalities already available in the context.

41. Code:
```lean
  have hsumsq_le : ∑ i, (hHerm.eigenvalues i) ^ 2 ≤ 2 * (∑ i, p i) ^ 2 := by
```
This line says that a proof script begins here. Everything indented underneath is a sequence of instructions that Lean will check step by step.

42. Code:
```lean
    calc
```
This line begins a chained calculation. Each displayed step that follows must be justified by the indented proof after `:= by`.

43. Code:
```lean
      ∑ i, (hHerm.eigenvalues i) ^ 2 = ∑ i, (p i) ^ 2 + ∑ i, (q i) ^ 2 := by
```
This line says that a proof script begins here. Everything indented underneath is a sequence of instructions that Lean will check step by step.

44. Code:
```lean
        simp [hsq, Finset.sum_add_distrib]
```
This line simplifies the goal using definitions and known equalities. `simpa` means that, after simplification, the desired statement matches a theorem Lean already has.

45. Code:
```lean
      _ ≤ (∑ i, p i) ^ 2 + (∑ i, q i) ^ 2 := by
```
This line says that a proof script begins here. Everything indented underneath is a sequence of instructions that Lean will check step by step.

46. Code:
```lean
        gcongr
```
This line pushes an inequality through expressions that preserve order.

47. Code:
```lean
        · exact Finset.sum_sq_le_sq_sum_of_nonneg (fun i _ => hp_nonneg i)
```
This bullet starts a new subgoal produced by the previous tactic. Lean is now focusing on one branch of the argument.

48. Code:
```lean
        · exact Finset.sum_sq_le_sq_sum_of_nonneg (fun i _ => hq_nonneg i)
```
This bullet starts a new subgoal produced by the previous tactic. Lean is now focusing on one branch of the argument.

49. Code:
```lean
      _ = 2 * (∑ i, p i) ^ 2 := by
```
This line says that a proof script begins here. Everything indented underneath is a sequence of instructions that Lean will check step by step.

50. Code:
```lean
        rw [hpq]
```
This line uses rewriting. Lean replaces one expression by an equal expression using the lemmas listed in brackets.

51. Code:
```lean
        ring
```
This line normalizes an algebraic identity in a commutative ring, just as one would expand and collect like terms by hand.

52. Code:
```lean
  have htraceNorm :
```
This line introduces an intermediate claim. The proof pauses to establish a fact that will be used shortly afterwards.

53. Code:
```lean
      (∑ i, |hHerm.eigenvalues i|) = 2 * ∑ i, p i := by
```
This line says that a proof script begins here. Everything indented underneath is a sequence of instructions that Lean will check step by step.

54. Code:
```lean
    calc
```
This line begins a chained calculation. Each displayed step that follows must be justified by the indented proof after `:= by`.

55. Code:
```lean
      (∑ i, |hHerm.eigenvalues i|) = ∑ i, (p i + q i) := by
```
This line says that a proof script begins here. Everything indented underneath is a sequence of instructions that Lean will check step by step.

56. Code:
```lean
        simp [habs]
```
This line simplifies the goal using definitions and known equalities. `simpa` means that, after simplification, the desired statement matches a theorem Lean already has.

57. Code:
```lean
      _ = ∑ i, p i + ∑ i, q i := by
```
This line says that a proof script begins here. Everything indented underneath is a sequence of instructions that Lean will check step by step.

58. Code:
```lean
        rw [Finset.sum_add_distrib]
```
This line uses rewriting. Lean replaces one expression by an equal expression using the lemmas listed in brackets.

59. Code:
```lean
      _ = 2 * ∑ i, p i := by
```
This line says that a proof script begins here. Everything indented underneath is a sequence of instructions that Lean will check step by step.

60. Code:
```lean
        rw [hpq]
```
This line uses rewriting. Lean replaces one expression by an equal expression using the lemmas listed in brackets.

61. Code:
```lean
        ring
```
This line normalizes an algebraic identity in a commutative ring, just as one would expand and collect like terms by hand.

62. Code:
```lean
  have hsqrt2_ne : Real.sqrt 2 ≠ 0 := by
```
This line says that a proof script begins here. Everything indented underneath is a sequence of instructions that Lean will check step by step.

63. Code:
```lean
    positivity
```
This line asks Lean to prove that the displayed quantity is positive or nonnegative using standard positivity rules.

64. Code:
```lean
  have hrhs :
```
This line introduces an intermediate claim. The proof pauses to establish a fact that will be used shortly afterwards.

65. Code:
```lean
      ((1 / Real.sqrt 2) * (2 * ∑ i, p i)) ^ 2 = 2 * (∑ i, p i) ^ 2 := by
```
This line says that a proof script begins here. Everything indented underneath is a sequence of instructions that Lean will check step by step.

66. Code:
```lean
    field_simp [pow_two, hsqrt2_ne]
```
This line is one local step in the declaration. It either refines the formula being defined or advances the proof by a small algebraic or logical move.

67. Code:
```lean
    nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 2 by positivity)]
```
This line solves the current numerical inequality by combining the equalities and inequalities already available in the context.

68. Code:
```lean
  have hsqineq : hsNormOp X ^ 2 ≤ ((1 / Real.sqrt 2) * (∑ i, |hHerm.eigenvalues i|)) ^ 2 := by
```
This line says that a proof script begins here. Everything indented underneath is a sequence of instructions that Lean will check step by step.

69. Code:
```lean
    rw [hsNorm_sq_eq_re_trace_conjTranspose_mul_self,
```
This line uses rewriting. Lean replaces one expression by an equal expression using the lemmas listed in brackets.

70. Code:
```lean
      hermitian_re_trace_conjTranspose_mul_self_eq_sum_sq_eigenvalues hHerm]
```
This line is one local step in the declaration. It either refines the formula being defined or advances the proof by a small algebraic or logical move.

71. Code:
```lean
    rw [htraceNorm, hrhs]
```
This line uses rewriting. Lean replaces one expression by an equal expression using the lemmas listed in brackets.

72. Code:
```lean
    exact hsumsq_le
```
This line finishes the current goal by giving Lean the exact theorem, lemma, or term that proves it.

73. Code:
```lean
  have hleft : 0 ≤ hsNormOp X := norm_nonneg _
```
This line introduces an intermediate claim. The proof pauses to establish a fact that will be used shortly afterwards.

74. Code:
```lean
  have hright : 0 ≤ (1 / Real.sqrt 2) * (∑ i, |hHerm.eigenvalues i|) := by
```
This line says that a proof script begins here. Everything indented underneath is a sequence of instructions that Lean will check step by step.

75. Code:
```lean
    positivity
```
This line asks Lean to prove that the displayed quantity is positive or nonnegative using standard positivity rules.

76. Code:
```lean
  have hle_abs : hsNormOp X ≤ |(1 / Real.sqrt 2) * (∑ i, |hHerm.eigenvalues i|)| := by
```
This line says that a proof script begins here. Everything indented underneath is a sequence of instructions that Lean will check step by step.

77. Code:
```lean
    simpa [abs_of_nonneg hleft] using (sq_le_sq.mp hsqineq)
```
This line simplifies the goal using definitions and known equalities. `simpa` means that, after simplification, the desired statement matches a theorem Lean already has.

78. Code:
```lean
  calc
```
This line begins a chained calculation. Each displayed step that follows must be justified by the indented proof after `:= by`.

79. Code:
```lean
    hsNormOp X ≤ |(1 / Real.sqrt 2) * (∑ i, |hHerm.eigenvalues i|)| := hle_abs
```
This line is one local step in the declaration. It either refines the formula being defined or advances the proof by a small algebraic or logical move.

80. Code:
```lean
    _ = (1 / Real.sqrt 2) * (∑ i, |hHerm.eigenvalues i|) := abs_of_nonneg hright
```
This line is one step inside a `calc` block. Lean is checking that the new expression really follows from the previous one.

81. Code:
```lean
    _ = (1 / Real.sqrt 2) * traceNormOp X := by
```
This line says that a proof script begins here. Everything indented underneath is a sequence of instructions that Lean will check step by step.

82. Code:
```lean
      rw [traceNormOp_hermitian_eq_sum_abs_eigenvalues hHerm]
```
This line uses rewriting. Lean replaces one expression by an equal expression using the lemmas listed in brackets.

## Mathematical summary

Restated without Lean syntax, `lemma1` is the theorem or lemma written above.

- State the desired identity or inequality in Lean’s syntax.
- Introduce temporary names and intermediate claims that organize the argument.
- Use rewriting, simplification, and earlier lemmas to reduce the goal to standard matrix or norm manipulations.
- Close the remaining algebraic or order-theoretic steps with Lean’s proof tactics.

## Dependencies and downstream use

### Earlier declarations this depends on
- [`traceNormOp`](../../Setups/traceNormOp.md) from `Setups.lean`
- [`hsNormOp`](../../Setups/hsNormOp.md) from `Setups.lean`
- [`hsNorm_sq_eq_re_trace_conjTranspose_mul_self`](hsNorm_sq_eq_re_trace_conjTranspose_mul_self.md) from `Theorem/Lemma1.lean`
- [`hermitian_re_trace_conjTranspose_mul_self_eq_sum_sq_eigenvalues`](hermitian_re_trace_conjTranspose_mul_self_eq_sum_sq_eigenvalues.md) from `Theorem/Lemma1.lean`
- [`traceNormOp_hermitian_eq_sum_abs_eigenvalues`](traceNormOp_hermitian_eq_sum_abs_eigenvalues.md) from `Theorem/Lemma1.lean`

### Later declarations that use this one
- [`theorem1`](../Theorem1/theorem1.md) in `Theorem/Theorem1.lean`
- [`remark1`](../Remark1/remark1.md) in `Theorem/Remark1.lean`
- [`theorem_not_tight`](../../PositiveGap/NotTight/theorem_not_tight.md) in `PositiveGap/NotTight.lean`

## Backlinks

- [Back to `INDEX.md`](../../INDEX.md)
- [Back to the `Theorem/Lemma1.lean` section in the index](../../INDEX.md#diamond-theorem-lemma1-lean)
- [Previous declaration in this file](traceNormOp_hermitian_eq_sum_abs_eigenvalues.md)
- [Next declaration in this file](traceNormOp_posSemidef_eq_trace.md)