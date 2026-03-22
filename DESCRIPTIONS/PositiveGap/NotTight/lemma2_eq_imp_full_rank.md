# lemma2_eq_imp_full_rank

## Source location

- Original Lean file: `Diamond/PositiveGap/NotTight.lean`
- Declaration name: `lemma2_eq_imp_full_rank`
- Declaration kind: `theorem`

## Why this declaration exists

This theorem identifies the equality case of Lemma 2: saturation forces full rank.

 In the file `PositiveGap/NotTight.lean`, it contributes to the finite-dimensional non-tightness argument and the equality-case analysis behind it. Later proofs call this result by name, so documenting it makes the larger argument readable as a mathematical chain rather than as opaque proof script.

## Original code

```lean
/-- Equality case of paper Lemma 2:
    a nonzero matrix saturating Lemma 2 has full rank. -/
theorem lemma2_eq_imp_full_rank
    {d : Type u} [Fintype d] [DecidableEq d]
    [Nonempty d]
    {Y : Matrix (d × d) (d × d) ℂ} (hY0 : Y ≠ 0)
    (heq : traceNormOp Y =
      Real.sqrt (Fintype.card (d × d) : ℝ) * hsNormOp Y) :
    Matrix.rank Y = Fintype.card (d × d) := by
  let μ : d × d → ℝ := (Matrix.isHermitian_conjTranspose_mul_self Y).eigenvalues
  have hμ_nonneg : ∀ i, 0 ≤ μ i := by
    intro i
    exact Matrix.eigenvalues_conjTranspose_mul_self_nonneg Y i
  have hnorm_sq : hsNormOp Y ^ 2 = ∑ i, μ i := by
    calc
      hsNormOp Y ^ 2 = Complex.re (Matrix.trace (Yᴴ * Y)) := by
        exact hsNorm_sq_eq_re_trace_conjTranspose_mul_self Y
      _ = ∑ i, μ i := by
        rw [(Matrix.isHermitian_conjTranspose_mul_self Y).trace_eq_sum_eigenvalues]
        simp [μ]
  have hsqeq : (∑ i, Real.sqrt (μ i)) ^ 2 = (Fintype.card (d × d) : ℝ) * ∑ i, μ i := by
    have hsq := congrArg (fun t : ℝ => t ^ 2) heq
    calc
      (∑ i, Real.sqrt (μ i)) ^ 2 = (traceNormOp Y) ^ 2 := by
        rfl
      _ = (Real.sqrt (Fintype.card (d × d) : ℝ) * hsNormOp Y) ^ 2 := by
        simpa using hsq
      _ = (Fintype.card (d × d) : ℝ) * ∑ i, μ i := by
        rw [show (Real.sqrt (Fintype.card (d × d) : ℝ) * hsNormOp Y) ^ 2 =
              (Real.sqrt (Fintype.card (d × d) : ℝ)) ^ 2 * (hsNormOp Y) ^ 2 by ring]
        rw [Real.sq_sqrt (by positivity), hnorm_sq]
  have hall : ∀ i j, Real.sqrt (μ i) = Real.sqrt (μ j) := by
    have hsqeq' :
        (∑ i, Real.sqrt (μ i)) ^ 2 =
          (Fintype.card (d × d) : ℝ) * ∑ i, (Real.sqrt (μ i)) ^ 2 := by
      calc
        (∑ i, Real.sqrt (μ i)) ^ 2 = (Fintype.card (d × d) : ℝ) * ∑ i, μ i := hsqeq
        _ = (Fintype.card (d × d) : ℝ) * ∑ i, (Real.sqrt (μ i)) ^ 2 := by
          refine congrArg ((Fintype.card (d × d) : ℝ) * ·) ?_
          refine Finset.sum_congr rfl ?_
          intro i hi
          exact (Real.sq_sqrt (hμ_nonneg i)).symm
    exact all_equal_of_sq_sum_eq_card_mul_sum_sq hsqeq'
  have hμ_not_zero_fun : μ ≠ 0 := by
    intro hμ0
    have hzeroMat : Yᴴ * Y = 0 := by
      exact
        (Matrix.IsHermitian.eigenvalues_eq_zero_iff
          (Matrix.isHermitian_conjTranspose_mul_self Y)).1 hμ0
    exact hY0 ((Matrix.conjTranspose_mul_self_eq_zero).1 hzeroMat)
  classical
  have hex : ∃ i, μ i ≠ 0 := by
    by_contra h
    push_neg at h
    exact hμ_not_zero_fun (funext h)
  rcases hex with ⟨i0, hi0⟩
  have hsqrt_pos : 0 < Real.sqrt (μ i0) := by
    apply Real.sqrt_pos.2
    exact lt_of_le_of_ne (hμ_nonneg i0) (by simpa [eq_comm] using hi0)
  have hμ_ne : ∀ i, μ i ≠ 0 := by
    intro i
    have hsqrt_eq : Real.sqrt (μ i) = Real.sqrt (μ i0) := hall i i0
    intro hzi
    rw [hzi, Real.sqrt_zero] at hsqrt_eq
    linarith
  have hcard : Fintype.card {i : d × d // μ i ≠ 0} = Fintype.card (d × d) := by
    classical
    exact
      Fintype.card_of_subtype
        (s := (Finset.univ : Finset (d × d)))
        (H := fun i => by simp [hμ_ne i])
  calc
    Y.rank = (Yᴴ * Y).rank := by
      symm
      exact Matrix.rank_conjTranspose_mul_self Y
    _ = Fintype.card {i : d × d // μ i ≠ 0} := by
      rw [(Matrix.isHermitian_conjTranspose_mul_self Y).rank_eq_card_non_zero_eigs]
    _ = Fintype.card (d × d) := hcard
```

## Block-by-block explanation

The explanation below follows the declaration block by block. Each block groups a coherent piece of the definition or proof, so the mathematical structure is easier to see than in a strictly line-oriented reading.

1. Code:
```lean
/-- Equality case of paper Lemma 2:
```
This is a Lean docstring. It is a human-written comment that tells readers what the declaration is meant to express before the formal code begins.

2. Code:
```lean
    a nonzero matrix saturating Lemma 2 has full rank. -/
```
This line is one local step in the declaration. It either refines the formula being defined or advances the proof by a small algebraic or logical move.

3. Code:
```lean
theorem lemma2_eq_imp_full_rank
```
This line starts the `lemma2_eq_imp_full_rank` declaration. Because it begins with `theorem`, Lean now knows what kind of named object is being introduced.

4. Code:
```lean
    {d : Type u} [Fintype d] [DecidableEq d]
```
This line is one local step in the declaration. It either refines the formula being defined or advances the proof by a small algebraic or logical move.  A bracket such as `[Fintype d]` tells Lean that the index set `d` is finite, so sums over all indices make sense.  A bracket such as `[DecidableEq d]` tells Lean that it can decide whether two indices are equal.

5. Code:
```lean
    [Nonempty d]
```
This line is one local step in the declaration. It either refines the formula being defined or advances the proof by a small algebraic or logical move.

6. Code:
```lean
    {Y : Matrix (d × d) (d × d) ℂ} (hY0 : Y ≠ 0)
```
This line is one local step in the declaration. It either refines the formula being defined or advances the proof by a small algebraic or logical move.  `Matrix d d ℂ` means a square matrix with complex entries; the index type `d` tells Lean which rows and columns exist.

7. Code:
```lean
    (heq : traceNormOp Y =
```
This line is one local step in the declaration. It either refines the formula being defined or advances the proof by a small algebraic or logical move.

8. Code:
```lean
      Real.sqrt (Fintype.card (d × d) : ℝ) * hsNormOp Y) :
```
This line is one local step in the declaration. It either refines the formula being defined or advances the proof by a small algebraic or logical move.  `Fintype.card` is the size of a finite index set.

9. Code:
```lean
    Matrix.rank Y = Fintype.card (d × d) := by
```
This line says that a proof script begins here. Everything indented underneath is a sequence of instructions that Lean will check step by step.  `Fintype.card` is the size of a finite index set.

10. Code:
```lean
  let μ : d × d → ℝ := (Matrix.isHermitian_conjTranspose_mul_self Y).eigenvalues
```
This line gives a temporary name to an expression. Doing that makes later lines shorter and easier to read.

11. Code:
```lean
  have hμ_nonneg : ∀ i, 0 ≤ μ i := by
```
This line says that a proof script begins here. Everything indented underneath is a sequence of instructions that Lean will check step by step.

12. Code:
```lean
    intro i
```
This line introduces the variable or hypothesis named here into the proof context. In ordinary mathematical prose, it is the same as saying “let” or “assume”.

13. Code:
```lean
    exact Matrix.eigenvalues_conjTranspose_mul_self_nonneg Y i
```
This line finishes the current goal by giving Lean the exact theorem, lemma, or term that proves it.

14. Code:
```lean
  have hnorm_sq : hsNormOp Y ^ 2 = ∑ i, μ i := by
```
This line says that a proof script begins here. Everything indented underneath is a sequence of instructions that Lean will check step by step.

15. Code:
```lean
    calc
```
This line begins a chained calculation. Each displayed step that follows must be justified by the indented proof after `:= by`.

16. Code:
```lean
      hsNormOp Y ^ 2 = Complex.re (Matrix.trace (Yᴴ * Y)) := by
```
This line says that a proof script begins here. Everything indented underneath is a sequence of instructions that Lean will check step by step.  The superscript `ᴴ` means conjugate transpose (also called the adjoint).

17. Code:
```lean
        exact hsNorm_sq_eq_re_trace_conjTranspose_mul_self Y
```
This line finishes the current goal by giving Lean the exact theorem, lemma, or term that proves it.

18. Code:
```lean
      _ = ∑ i, μ i := by
```
This line says that a proof script begins here. Everything indented underneath is a sequence of instructions that Lean will check step by step.

19. Code:
```lean
        rw [(Matrix.isHermitian_conjTranspose_mul_self Y).trace_eq_sum_eigenvalues]
```
This line uses rewriting. Lean replaces one expression by an equal expression using the lemmas listed in brackets.

20. Code:
```lean
        simp [μ]
```
This line simplifies the goal using definitions and known equalities. `simpa` means that, after simplification, the desired statement matches a theorem Lean already has.

21. Code:
```lean
  have hsqeq : (∑ i, Real.sqrt (μ i)) ^ 2 = (Fintype.card (d × d) : ℝ) * ∑ i, μ i := by
```
This line says that a proof script begins here. Everything indented underneath is a sequence of instructions that Lean will check step by step.  `Fintype.card` is the size of a finite index set.

22. Code:
```lean
    have hsq := congrArg (fun t : ℝ => t ^ 2) heq
```
This line introduces an intermediate claim. The proof pauses to establish a fact that will be used shortly afterwards.

23. Code:
```lean
    calc
```
This line begins a chained calculation. Each displayed step that follows must be justified by the indented proof after `:= by`.

24. Code:
```lean
      (∑ i, Real.sqrt (μ i)) ^ 2 = (traceNormOp Y) ^ 2 := by
```
This line says that a proof script begins here. Everything indented underneath is a sequence of instructions that Lean will check step by step.

25. Code:
```lean
        rfl
```
This line closes the goal by reflexivity: after unfolding definitions, both sides are literally the same expression.

26. Code:
```lean
      _ = (Real.sqrt (Fintype.card (d × d) : ℝ) * hsNormOp Y) ^ 2 := by
```
This line says that a proof script begins here. Everything indented underneath is a sequence of instructions that Lean will check step by step.  `Fintype.card` is the size of a finite index set.

27. Code:
```lean
        simpa using hsq
```
This line simplifies the goal using definitions and known equalities. `simpa` means that, after simplification, the desired statement matches a theorem Lean already has.

28. Code:
```lean
      _ = (Fintype.card (d × d) : ℝ) * ∑ i, μ i := by
```
This line says that a proof script begins here. Everything indented underneath is a sequence of instructions that Lean will check step by step.  `Fintype.card` is the size of a finite index set.

29. Code:
```lean
        rw [show (Real.sqrt (Fintype.card (d × d) : ℝ) * hsNormOp Y) ^ 2 =
```
This line uses rewriting. Lean replaces one expression by an equal expression using the lemmas listed in brackets.  `Fintype.card` is the size of a finite index set.

30. Code:
```lean
              (Real.sqrt (Fintype.card (d × d) : ℝ)) ^ 2 * (hsNormOp Y) ^ 2 by ring]
```
This line is one local step in the declaration. It either refines the formula being defined or advances the proof by a small algebraic or logical move.  `Fintype.card` is the size of a finite index set.

31. Code:
```lean
        rw [Real.sq_sqrt (by positivity), hnorm_sq]
```
This line uses rewriting. Lean replaces one expression by an equal expression using the lemmas listed in brackets.

32. Code:
```lean
  have hall : ∀ i j, Real.sqrt (μ i) = Real.sqrt (μ j) := by
```
This line says that a proof script begins here. Everything indented underneath is a sequence of instructions that Lean will check step by step.

33. Code:
```lean
    have hsqeq' :
```
This line introduces an intermediate claim. The proof pauses to establish a fact that will be used shortly afterwards.

34. Code:
```lean
        (∑ i, Real.sqrt (μ i)) ^ 2 =
```
This line is one local step in the declaration. It either refines the formula being defined or advances the proof by a small algebraic or logical move.

35. Code:
```lean
          (Fintype.card (d × d) : ℝ) * ∑ i, (Real.sqrt (μ i)) ^ 2 := by
```
This line says that a proof script begins here. Everything indented underneath is a sequence of instructions that Lean will check step by step.  `Fintype.card` is the size of a finite index set.

36. Code:
```lean
      calc
```
This line begins a chained calculation. Each displayed step that follows must be justified by the indented proof after `:= by`.

37. Code:
```lean
        (∑ i, Real.sqrt (μ i)) ^ 2 = (Fintype.card (d × d) : ℝ) * ∑ i, μ i := hsqeq
```
This line is one local step in the declaration. It either refines the formula being defined or advances the proof by a small algebraic or logical move.  `Fintype.card` is the size of a finite index set.

38. Code:
```lean
        _ = (Fintype.card (d × d) : ℝ) * ∑ i, (Real.sqrt (μ i)) ^ 2 := by
```
This line says that a proof script begins here. Everything indented underneath is a sequence of instructions that Lean will check step by step.  `Fintype.card` is the size of a finite index set.

39. Code:
```lean
          refine congrArg ((Fintype.card (d × d) : ℝ) * ·) ?_
```
This line is a more controlled version of `apply`. It sets up the proof with a partly specified argument and leaves smaller goals to solve next.  `Fintype.card` is the size of a finite index set.

40. Code:
```lean
          refine Finset.sum_congr rfl ?_
```
This line is a more controlled version of `apply`. It sets up the proof with a partly specified argument and leaves smaller goals to solve next.

41. Code:
```lean
          intro i hi
```
This line introduces the variable or hypothesis named here into the proof context. In ordinary mathematical prose, it is the same as saying “let” or “assume”.

42. Code:
```lean
          exact (Real.sq_sqrt (hμ_nonneg i)).symm
```
This line finishes the current goal by giving Lean the exact theorem, lemma, or term that proves it.

43. Code:
```lean
    exact all_equal_of_sq_sum_eq_card_mul_sum_sq hsqeq'
```
This line finishes the current goal by giving Lean the exact theorem, lemma, or term that proves it.

44. Code:
```lean
  have hμ_not_zero_fun : μ ≠ 0 := by
```
This line says that a proof script begins here. Everything indented underneath is a sequence of instructions that Lean will check step by step.

45. Code:
```lean
    intro hμ0
```
This line introduces the variable or hypothesis named here into the proof context. In ordinary mathematical prose, it is the same as saying “let” or “assume”.

46. Code:
```lean
    have hzeroMat : Yᴴ * Y = 0 := by
```
This line says that a proof script begins here. Everything indented underneath is a sequence of instructions that Lean will check step by step.  The superscript `ᴴ` means conjugate transpose (also called the adjoint).

47. Code:
```lean
      exact
```
This line finishes the current goal by giving Lean the exact theorem, lemma, or term that proves it.

48. Code:
```lean
        (Matrix.IsHermitian.eigenvalues_eq_zero_iff
```
This line is one local step in the declaration. It either refines the formula being defined or advances the proof by a small algebraic or logical move.

49. Code:
```lean
          (Matrix.isHermitian_conjTranspose_mul_self Y)).1 hμ0
```
This line is one local step in the declaration. It either refines the formula being defined or advances the proof by a small algebraic or logical move.

50. Code:
```lean
    exact hY0 ((Matrix.conjTranspose_mul_self_eq_zero).1 hzeroMat)
```
This line finishes the current goal by giving Lean the exact theorem, lemma, or term that proves it.

51. Code:
```lean
  classical
```
This line is one local step in the declaration. It either refines the formula being defined or advances the proof by a small algebraic or logical move.

52. Code:
```lean
  have hex : ∃ i, μ i ≠ 0 := by
```
This line says that a proof script begins here. Everything indented underneath is a sequence of instructions that Lean will check step by step.

53. Code:
```lean
    by_contra h
```
This line is one local step in the declaration. It either refines the formula being defined or advances the proof by a small algebraic or logical move.

54. Code:
```lean
    push_neg at h
```
This line is one local step in the declaration. It either refines the formula being defined or advances the proof by a small algebraic or logical move.

55. Code:
```lean
    exact hμ_not_zero_fun (funext h)
```
This line finishes the current goal by giving Lean the exact theorem, lemma, or term that proves it.

56. Code:
```lean
  rcases hex with ⟨i0, hi0⟩
```
This line is one local step in the declaration. It either refines the formula being defined or advances the proof by a small algebraic or logical move.

57. Code:
```lean
  have hsqrt_pos : 0 < Real.sqrt (μ i0) := by
```
This line says that a proof script begins here. Everything indented underneath is a sequence of instructions that Lean will check step by step.

58. Code:
```lean
    apply Real.sqrt_pos.2
```
This line applies an existing theorem to the current goal. Lean then asks the author to prove the theorem’s hypotheses.

59. Code:
```lean
    exact lt_of_le_of_ne (hμ_nonneg i0) (by simpa [eq_comm] using hi0)
```
This line finishes the current goal by giving Lean the exact theorem, lemma, or term that proves it.

60. Code:
```lean
  have hμ_ne : ∀ i, μ i ≠ 0 := by
```
This line says that a proof script begins here. Everything indented underneath is a sequence of instructions that Lean will check step by step.

61. Code:
```lean
    intro i
```
This line introduces the variable or hypothesis named here into the proof context. In ordinary mathematical prose, it is the same as saying “let” or “assume”.

62. Code:
```lean
    have hsqrt_eq : Real.sqrt (μ i) = Real.sqrt (μ i0) := hall i i0
```
This line introduces an intermediate claim. The proof pauses to establish a fact that will be used shortly afterwards.

63. Code:
```lean
    intro hzi
```
This line introduces the variable or hypothesis named here into the proof context. In ordinary mathematical prose, it is the same as saying “let” or “assume”.

64. Code:
```lean
    rw [hzi, Real.sqrt_zero] at hsqrt_eq
```
This line uses rewriting. Lean replaces one expression by an equal expression using the lemmas listed in brackets.

65. Code:
```lean
    linarith
```
This line solves the current numerical inequality by combining the equalities and inequalities already available in the context.

66. Code:
```lean
  have hcard : Fintype.card {i : d × d // μ i ≠ 0} = Fintype.card (d × d) := by
```
This line says that a proof script begins here. Everything indented underneath is a sequence of instructions that Lean will check step by step.  `Fintype.card` is the size of a finite index set.

67. Code:
```lean
    classical
```
This line is one local step in the declaration. It either refines the formula being defined or advances the proof by a small algebraic or logical move.

68. Code:
```lean
    exact
```
This line finishes the current goal by giving Lean the exact theorem, lemma, or term that proves it.

69. Code:
```lean
      Fintype.card_of_subtype
```
This line is one local step in the declaration. It either refines the formula being defined or advances the proof by a small algebraic or logical move.  `Fintype.card` is the size of a finite index set.

70. Code:
```lean
        (s := (Finset.univ : Finset (d × d)))
```
This line is one local step in the declaration. It either refines the formula being defined or advances the proof by a small algebraic or logical move.

71. Code:
```lean
        (H := fun i => by simp [hμ_ne i])
```
This line is one local step in the declaration. It either refines the formula being defined or advances the proof by a small algebraic or logical move.

72. Code:
```lean
  calc
```
This line begins a chained calculation. Each displayed step that follows must be justified by the indented proof after `:= by`.

73. Code:
```lean
    Y.rank = (Yᴴ * Y).rank := by
```
This line says that a proof script begins here. Everything indented underneath is a sequence of instructions that Lean will check step by step.  The superscript `ᴴ` means conjugate transpose (also called the adjoint).

74. Code:
```lean
      symm
```
This line is one local step in the declaration. It either refines the formula being defined or advances the proof by a small algebraic or logical move.

75. Code:
```lean
      exact Matrix.rank_conjTranspose_mul_self Y
```
This line finishes the current goal by giving Lean the exact theorem, lemma, or term that proves it.

76. Code:
```lean
    _ = Fintype.card {i : d × d // μ i ≠ 0} := by
```
This line says that a proof script begins here. Everything indented underneath is a sequence of instructions that Lean will check step by step.  `Fintype.card` is the size of a finite index set.

77. Code:
```lean
      rw [(Matrix.isHermitian_conjTranspose_mul_self Y).rank_eq_card_non_zero_eigs]
```
This line uses rewriting. Lean replaces one expression by an equal expression using the lemmas listed in brackets.

78. Code:
```lean
    _ = Fintype.card (d × d) := hcard
```
This line is one step inside a `calc` block. Lean is checking that the new expression really follows from the previous one.  `Fintype.card` is the size of a finite index set.

## Mathematical summary

Restated without Lean syntax, `lemma2_eq_imp_full_rank` is the theorem or lemma written above.

- State the desired identity or inequality in Lean’s syntax.
- Introduce temporary names and intermediate claims that organize the argument.
- Use rewriting, simplification, and earlier lemmas to reduce the goal to standard matrix or norm manipulations.
- Close the remaining algebraic or order-theoretic steps with Lean’s proof tactics.

## Dependencies and downstream use

### Earlier declarations this depends on
- [`traceNormOp`](../../Setups/traceNormOp.md) from `Setups.lean`
- [`hsNormOp`](../../Setups/hsNormOp.md) from `Setups.lean`
- [`hsNorm_sq_eq_re_trace_conjTranspose_mul_self`](../../Theorem/Lemma1/hsNorm_sq_eq_re_trace_conjTranspose_mul_self.md) from `Theorem/Lemma1.lean`
- [`hsNorm_sq_eq_re_trace_conjTranspose_mul_self`](../../Theorem/Lemma2/hsNorm_sq_eq_re_trace_conjTranspose_mul_self.md) from `Theorem/Lemma2.lean`
- [`all_equal_of_sq_sum_eq_card_mul_sum_sq`](all_equal_of_sq_sum_eq_card_mul_sum_sq.md) from `PositiveGap/NotTight.lean`

### Later declarations that use this one
- [`theorem_not_tight`](theorem_not_tight.md) in `PositiveGap/NotTight.lean`

## Backlinks

- [Back to `INDEX.md`](../../INDEX.md)
- [Back to the `PositiveGap/NotTight.lean` section in the index](../../INDEX.md#diamond-positivegap-nottight-lean)
- [Previous declaration in this file](lemma1_eq_imp_rank_two.md)
- [Next declaration in this file](partialTranspose_ne_zero_of_ne_zero.md)