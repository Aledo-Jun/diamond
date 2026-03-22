# traceNormOp_sub_density_le_two

## Source location

- Original Lean file: `Diamond/Theorem/Lemma1.lean`
- Declaration name: `traceNormOp_sub_density_le_two`
- Declaration kind: `theorem`

## Why this declaration exists

The concrete trace distance between density states is at most `2`.

 In the file `Theorem/Lemma1.lean`, it contributes to the proof infrastructure for the first norm inequality and the public theorem `lemma1`. Later proofs call this result by name, so documenting it makes the larger argument readable as a mathematical chain rather than as opaque proof script.

## Original code

```lean
/-- The concrete trace distance between density states is at most `2`. -/
private theorem traceNormOp_sub_density_le_two
    {d : Type u} [Fintype d] [DecidableEq d]
    {ρ σ : Matrix d d ℂ} (hρ : IsDensityState ρ) (hσ : IsDensityState σ) :
    traceNormOp (ρ - σ) ≤ 2 := by
  let X : Matrix d d ℂ := ρ - σ
  have hX : Matrix.IsHermitian X := hρ.1.isHermitian.sub hσ.1.isHermitian
  let U : Matrix d d ℂ := hX.eigenvectorUnitary
  let Ustar : Matrix d d ℂ := star hX.eigenvectorUnitary
  let D : Matrix d d ℂ := Matrix.diagonal (fun i => ((hX.eigenvalues i : ℝ) : ℂ))
  let P : Matrix d d ℂ := Ustar * ρ * U
  let Q : Matrix d d ℂ := Ustar * σ * U
  have hU_right : U * Ustar = 1 := by
    exact (Matrix.mem_unitaryGroup_iff).1 hX.eigenvectorUnitary.property
  have hP_pos : P.PosSemidef := by
    simpa [P, U, Ustar, Matrix.mul_assoc] using hρ.1.conjTranspose_mul_mul_same U
  have hQ_pos : Q.PosSemidef := by
    simpa [Q, U, Ustar, Matrix.mul_assoc] using hσ.1.conjTranspose_mul_mul_same U
  have hP_trace : Matrix.trace P = 1 := by
    calc
      Matrix.trace P = Matrix.trace ((U * Ustar) * ρ) := by
        dsimp [P]
        rw [Matrix.trace_mul_cycle Ustar ρ U, Matrix.mul_assoc]
      _ = Matrix.trace ρ := by
        rw [hU_right, one_mul]
      _ = 1 := hρ.2
  have hQ_trace : Matrix.trace Q = 1 := by
    calc
      Matrix.trace Q = Matrix.trace ((U * Ustar) * σ) := by
        dsimp [Q]
        rw [Matrix.trace_mul_cycle Ustar σ U, Matrix.mul_assoc]
      _ = Matrix.trace σ := by
        rw [hU_right, one_mul]
      _ = 1 := hσ.2
  have hdiag :
      P - Q = D := by
    simpa [X, U, Ustar, D, P, Q, Unitary.conjStarAlgAut_apply, Matrix.mul_assoc,
      Matrix.mul_sub, Matrix.sub_mul] using hX.conjStarAlgAut_star_eigenvectorUnitary
  have hbound :
      ∀ i : d, |hX.eigenvalues i| ≤ Complex.re (P i i) + Complex.re (Q i i) := by
    intro i
    have hPiC : 0 ≤ P i i := hP_pos.diag_nonneg
    have hQiC : 0 ≤ Q i i := hQ_pos.diag_nonneg
    have hPi : 0 ≤ Complex.re (P i i) := by
      exact (RCLike.nonneg_iff.mp hPiC).1
    have hQi : 0 ≤ Complex.re (Q i i) := by
      exact (RCLike.nonneg_iff.mp hQiC).1
    have hpoint :
        Complex.re (P i i) - Complex.re (Q i i) = hX.eigenvalues i := by
      have hpointC := congrArg (fun M : Matrix d d ℂ => M i i) hdiag
      simpa [D] using congrArg Complex.re hpointC
    calc
      |hX.eigenvalues i| = |Complex.re (P i i) - Complex.re (Q i i)| := by
        rw [← hpoint]
      _ = |Complex.re (P i i) + (-Complex.re (Q i i))| := by
        rw [sub_eq_add_neg]
      _ ≤ |Complex.re (P i i)| + |-Complex.re (Q i i)| := abs_add_le _ _
      _ = Complex.re (P i i) + Complex.re (Q i i) := by
        rw [abs_of_nonneg hPi, abs_neg, abs_of_nonneg hQi]
  calc
    traceNormOp X = ∑ i, |hX.eigenvalues i| := by
      simpa [X] using traceNormOp_hermitian_eq_sum_abs_eigenvalues hX
    _ ≤ ∑ i, (Complex.re (P i i) + Complex.re (Q i i)) := by
      exact Finset.sum_le_sum (fun i hi => hbound i)
    _ = (∑ i, Complex.re (P i i)) + ∑ i, Complex.re (Q i i) := by
      rw [Finset.sum_add_distrib]
    _ = Complex.re (Matrix.trace P) + Complex.re (Matrix.trace Q) := by
      simp [Matrix.trace]
    _ = 2 := by
      rw [hP_trace, hQ_trace]
      norm_num
```

## Block-by-block explanation

The explanation below follows the declaration block by block. Each block groups a coherent piece of the definition or proof, so the mathematical structure is easier to see than in a strictly line-oriented reading.

1. Code:
```lean
/-- The concrete trace distance between density states is at most `2`. -/
```
This is a Lean docstring. It is a human-written comment that tells readers what the declaration is meant to express before the formal code begins.

2. Code:
```lean
private theorem traceNormOp_sub_density_le_two
```
This line starts the `traceNormOp_sub_density_le_two` declaration. Because it begins with `theorem`, Lean now knows what kind of named object is being introduced.

3. Code:
```lean
    {d : Type u} [Fintype d] [DecidableEq d]
```
This line is one local step in the declaration. It either refines the formula being defined or advances the proof by a small algebraic or logical move.  A bracket such as `[Fintype d]` tells Lean that the index set `d` is finite, so sums over all indices make sense.  A bracket such as `[DecidableEq d]` tells Lean that it can decide whether two indices are equal.

4. Code:
```lean
    {ρ σ : Matrix d d ℂ} (hρ : IsDensityState ρ) (hσ : IsDensityState σ) :
```
This line is one local step in the declaration. It either refines the formula being defined or advances the proof by a small algebraic or logical move.  `Matrix d d ℂ` means a square matrix with complex entries; the index type `d` tells Lean which rows and columns exist.

5. Code:
```lean
    traceNormOp (ρ - σ) ≤ 2 := by
```
This line says that a proof script begins here. Everything indented underneath is a sequence of instructions that Lean will check step by step.

6. Code:
```lean
  let X : Matrix d d ℂ := ρ - σ
```
This line gives a temporary name to an expression. Doing that makes later lines shorter and easier to read.  `Matrix d d ℂ` means a square matrix with complex entries; the index type `d` tells Lean which rows and columns exist.

7. Code:
```lean
  have hX : Matrix.IsHermitian X := hρ.1.isHermitian.sub hσ.1.isHermitian
```
This line introduces an intermediate claim. The proof pauses to establish a fact that will be used shortly afterwards.

8. Code:
```lean
  let U : Matrix d d ℂ := hX.eigenvectorUnitary
```
This line gives a temporary name to an expression. Doing that makes later lines shorter and easier to read.  `Matrix d d ℂ` means a square matrix with complex entries; the index type `d` tells Lean which rows and columns exist.

9. Code:
```lean
  let Ustar : Matrix d d ℂ := star hX.eigenvectorUnitary
```
This line gives a temporary name to an expression. Doing that makes later lines shorter and easier to read.  `Matrix d d ℂ` means a square matrix with complex entries; the index type `d` tells Lean which rows and columns exist.

10. Code:
```lean
  let D : Matrix d d ℂ := Matrix.diagonal (fun i => ((hX.eigenvalues i : ℝ) : ℂ))
```
This line gives a temporary name to an expression. Doing that makes later lines shorter and easier to read.  `Matrix d d ℂ` means a square matrix with complex entries; the index type `d` tells Lean which rows and columns exist.

11. Code:
```lean
  let P : Matrix d d ℂ := Ustar * ρ * U
```
This line gives a temporary name to an expression. Doing that makes later lines shorter and easier to read.  `Matrix d d ℂ` means a square matrix with complex entries; the index type `d` tells Lean which rows and columns exist.

12. Code:
```lean
  let Q : Matrix d d ℂ := Ustar * σ * U
```
This line gives a temporary name to an expression. Doing that makes later lines shorter and easier to read.  `Matrix d d ℂ` means a square matrix with complex entries; the index type `d` tells Lean which rows and columns exist.

13. Code:
```lean
  have hU_right : U * Ustar = 1 := by
```
This line says that a proof script begins here. Everything indented underneath is a sequence of instructions that Lean will check step by step.

14. Code:
```lean
    exact (Matrix.mem_unitaryGroup_iff).1 hX.eigenvectorUnitary.property
```
This line finishes the current goal by giving Lean the exact theorem, lemma, or term that proves it.

15. Code:
```lean
  have hP_pos : P.PosSemidef := by
```
This line says that a proof script begins here. Everything indented underneath is a sequence of instructions that Lean will check step by step.  `PosSemidef` is Lean’s name for “positive semidefinite”.

16. Code:
```lean
    simpa [P, U, Ustar, Matrix.mul_assoc] using hρ.1.conjTranspose_mul_mul_same U
```
This line simplifies the goal using definitions and known equalities. `simpa` means that, after simplification, the desired statement matches a theorem Lean already has.

17. Code:
```lean
  have hQ_pos : Q.PosSemidef := by
```
This line says that a proof script begins here. Everything indented underneath is a sequence of instructions that Lean will check step by step.  `PosSemidef` is Lean’s name for “positive semidefinite”.

18. Code:
```lean
    simpa [Q, U, Ustar, Matrix.mul_assoc] using hσ.1.conjTranspose_mul_mul_same U
```
This line simplifies the goal using definitions and known equalities. `simpa` means that, after simplification, the desired statement matches a theorem Lean already has.

19. Code:
```lean
  have hP_trace : Matrix.trace P = 1 := by
```
This line says that a proof script begins here. Everything indented underneath is a sequence of instructions that Lean will check step by step.

20. Code:
```lean
    calc
```
This line begins a chained calculation. Each displayed step that follows must be justified by the indented proof after `:= by`.

21. Code:
```lean
      Matrix.trace P = Matrix.trace ((U * Ustar) * ρ) := by
```
This line says that a proof script begins here. Everything indented underneath is a sequence of instructions that Lean will check step by step.

22. Code:
```lean
        dsimp [P]
```
This line is one local step in the declaration. It either refines the formula being defined or advances the proof by a small algebraic or logical move.

23. Code:
```lean
        rw [Matrix.trace_mul_cycle Ustar ρ U, Matrix.mul_assoc]
```
This line uses rewriting. Lean replaces one expression by an equal expression using the lemmas listed in brackets.

24. Code:
```lean
      _ = Matrix.trace ρ := by
```
This line says that a proof script begins here. Everything indented underneath is a sequence of instructions that Lean will check step by step.

25. Code:
```lean
        rw [hU_right, one_mul]
```
This line uses rewriting. Lean replaces one expression by an equal expression using the lemmas listed in brackets.

26. Code:
```lean
      _ = 1 := hρ.2
```
This line is one step inside a `calc` block. Lean is checking that the new expression really follows from the previous one.

27. Code:
```lean
  have hQ_trace : Matrix.trace Q = 1 := by
```
This line says that a proof script begins here. Everything indented underneath is a sequence of instructions that Lean will check step by step.

28. Code:
```lean
    calc
```
This line begins a chained calculation. Each displayed step that follows must be justified by the indented proof after `:= by`.

29. Code:
```lean
      Matrix.trace Q = Matrix.trace ((U * Ustar) * σ) := by
```
This line says that a proof script begins here. Everything indented underneath is a sequence of instructions that Lean will check step by step.

30. Code:
```lean
        dsimp [Q]
```
This line is one local step in the declaration. It either refines the formula being defined or advances the proof by a small algebraic or logical move.

31. Code:
```lean
        rw [Matrix.trace_mul_cycle Ustar σ U, Matrix.mul_assoc]
```
This line uses rewriting. Lean replaces one expression by an equal expression using the lemmas listed in brackets.

32. Code:
```lean
      _ = Matrix.trace σ := by
```
This line says that a proof script begins here. Everything indented underneath is a sequence of instructions that Lean will check step by step.

33. Code:
```lean
        rw [hU_right, one_mul]
```
This line uses rewriting. Lean replaces one expression by an equal expression using the lemmas listed in brackets.

34. Code:
```lean
      _ = 1 := hσ.2
```
This line is one step inside a `calc` block. Lean is checking that the new expression really follows from the previous one.

35. Code:
```lean
  have hdiag :
```
This line introduces an intermediate claim. The proof pauses to establish a fact that will be used shortly afterwards.

36. Code:
```lean
      P - Q = D := by
```
This line says that a proof script begins here. Everything indented underneath is a sequence of instructions that Lean will check step by step.

37. Code:
```lean
    simpa [X, U, Ustar, D, P, Q, Unitary.conjStarAlgAut_apply, Matrix.mul_assoc,
```
This line simplifies the goal using definitions and known equalities. `simpa` means that, after simplification, the desired statement matches a theorem Lean already has.

38. Code:
```lean
      Matrix.mul_sub, Matrix.sub_mul] using hX.conjStarAlgAut_star_eigenvectorUnitary
```
This line is one local step in the declaration. It either refines the formula being defined or advances the proof by a small algebraic or logical move.

39. Code:
```lean
  have hbound :
```
This line introduces an intermediate claim. The proof pauses to establish a fact that will be used shortly afterwards.

40. Code:
```lean
      ∀ i : d, |hX.eigenvalues i| ≤ Complex.re (P i i) + Complex.re (Q i i) := by
```
This line says that a proof script begins here. Everything indented underneath is a sequence of instructions that Lean will check step by step.

41. Code:
```lean
    intro i
```
This line introduces the variable or hypothesis named here into the proof context. In ordinary mathematical prose, it is the same as saying “let” or “assume”.

42. Code:
```lean
    have hPiC : 0 ≤ P i i := hP_pos.diag_nonneg
```
This line introduces an intermediate claim. The proof pauses to establish a fact that will be used shortly afterwards.

43. Code:
```lean
    have hQiC : 0 ≤ Q i i := hQ_pos.diag_nonneg
```
This line introduces an intermediate claim. The proof pauses to establish a fact that will be used shortly afterwards.

44. Code:
```lean
    have hPi : 0 ≤ Complex.re (P i i) := by
```
This line says that a proof script begins here. Everything indented underneath is a sequence of instructions that Lean will check step by step.

45. Code:
```lean
      exact (RCLike.nonneg_iff.mp hPiC).1
```
This line finishes the current goal by giving Lean the exact theorem, lemma, or term that proves it.

46. Code:
```lean
    have hQi : 0 ≤ Complex.re (Q i i) := by
```
This line says that a proof script begins here. Everything indented underneath is a sequence of instructions that Lean will check step by step.

47. Code:
```lean
      exact (RCLike.nonneg_iff.mp hQiC).1
```
This line finishes the current goal by giving Lean the exact theorem, lemma, or term that proves it.

48. Code:
```lean
    have hpoint :
```
This line introduces an intermediate claim. The proof pauses to establish a fact that will be used shortly afterwards.

49. Code:
```lean
        Complex.re (P i i) - Complex.re (Q i i) = hX.eigenvalues i := by
```
This line says that a proof script begins here. Everything indented underneath is a sequence of instructions that Lean will check step by step.

50. Code:
```lean
      have hpointC := congrArg (fun M : Matrix d d ℂ => M i i) hdiag
```
This line introduces an intermediate claim. The proof pauses to establish a fact that will be used shortly afterwards.  `Matrix d d ℂ` means a square matrix with complex entries; the index type `d` tells Lean which rows and columns exist.

51. Code:
```lean
      simpa [D] using congrArg Complex.re hpointC
```
This line simplifies the goal using definitions and known equalities. `simpa` means that, after simplification, the desired statement matches a theorem Lean already has.

52. Code:
```lean
    calc
```
This line begins a chained calculation. Each displayed step that follows must be justified by the indented proof after `:= by`.

53. Code:
```lean
      |hX.eigenvalues i| = |Complex.re (P i i) - Complex.re (Q i i)| := by
```
This line says that a proof script begins here. Everything indented underneath is a sequence of instructions that Lean will check step by step.

54. Code:
```lean
        rw [← hpoint]
```
This line uses rewriting. Lean replaces one expression by an equal expression using the lemmas listed in brackets.

55. Code:
```lean
      _ = |Complex.re (P i i) + (-Complex.re (Q i i))| := by
```
This line says that a proof script begins here. Everything indented underneath is a sequence of instructions that Lean will check step by step.

56. Code:
```lean
        rw [sub_eq_add_neg]
```
This line uses rewriting. Lean replaces one expression by an equal expression using the lemmas listed in brackets.

57. Code:
```lean
      _ ≤ |Complex.re (P i i)| + |-Complex.re (Q i i)| := abs_add_le _ _
```
This line is one step inside a `calc` block. Lean is checking that the new expression really follows from the previous one.

58. Code:
```lean
      _ = Complex.re (P i i) + Complex.re (Q i i) := by
```
This line says that a proof script begins here. Everything indented underneath is a sequence of instructions that Lean will check step by step.

59. Code:
```lean
        rw [abs_of_nonneg hPi, abs_neg, abs_of_nonneg hQi]
```
This line uses rewriting. Lean replaces one expression by an equal expression using the lemmas listed in brackets.

60. Code:
```lean
  calc
```
This line begins a chained calculation. Each displayed step that follows must be justified by the indented proof after `:= by`.

61. Code:
```lean
    traceNormOp X = ∑ i, |hX.eigenvalues i| := by
```
This line says that a proof script begins here. Everything indented underneath is a sequence of instructions that Lean will check step by step.

62. Code:
```lean
      simpa [X] using traceNormOp_hermitian_eq_sum_abs_eigenvalues hX
```
This line simplifies the goal using definitions and known equalities. `simpa` means that, after simplification, the desired statement matches a theorem Lean already has.

63. Code:
```lean
    _ ≤ ∑ i, (Complex.re (P i i) + Complex.re (Q i i)) := by
```
This line says that a proof script begins here. Everything indented underneath is a sequence of instructions that Lean will check step by step.

64. Code:
```lean
      exact Finset.sum_le_sum (fun i hi => hbound i)
```
This line finishes the current goal by giving Lean the exact theorem, lemma, or term that proves it.

65. Code:
```lean
    _ = (∑ i, Complex.re (P i i)) + ∑ i, Complex.re (Q i i) := by
```
This line says that a proof script begins here. Everything indented underneath is a sequence of instructions that Lean will check step by step.

66. Code:
```lean
      rw [Finset.sum_add_distrib]
```
This line uses rewriting. Lean replaces one expression by an equal expression using the lemmas listed in brackets.

67. Code:
```lean
    _ = Complex.re (Matrix.trace P) + Complex.re (Matrix.trace Q) := by
```
This line says that a proof script begins here. Everything indented underneath is a sequence of instructions that Lean will check step by step.

68. Code:
```lean
      simp [Matrix.trace]
```
This line simplifies the goal using definitions and known equalities. `simpa` means that, after simplification, the desired statement matches a theorem Lean already has.

69. Code:
```lean
    _ = 2 := by
```
This line says that a proof script begins here. Everything indented underneath is a sequence of instructions that Lean will check step by step.

70. Code:
```lean
      rw [hP_trace, hQ_trace]
```
This line uses rewriting. Lean replaces one expression by an equal expression using the lemmas listed in brackets.

71. Code:
```lean
      norm_num
```
This line is one local step in the declaration. It either refines the formula being defined or advances the proof by a small algebraic or logical move.

## Mathematical summary

Restated without Lean syntax, `traceNormOp_sub_density_le_two` is the theorem or lemma written above.

- State the desired identity or inequality in Lean’s syntax.
- Introduce temporary names and intermediate claims that organize the argument.
- Use rewriting, simplification, and earlier lemmas to reduce the goal to standard matrix or norm manipulations.
- Close the remaining algebraic or order-theoretic steps with Lean’s proof tactics.

## Dependencies and downstream use

### Earlier declarations this depends on
- [`traceNormOp`](../../Setups/traceNormOp.md) from `Setups.lean`
- [`IsDensityState`](../../Setups/IsDensityState.md) from `Setups.lean`
- [`traceNormOp_hermitian_eq_sum_abs_eigenvalues`](traceNormOp_hermitian_eq_sum_abs_eigenvalues.md) from `Theorem/Lemma1.lean`

### Later declarations that use this one
- No later documented declaration mentions this name explicitly.

## Backlinks

- [Back to `INDEX.md`](../../INDEX.md)
- [Back to the `Theorem/Lemma1.lean` section in the index](../../INDEX.md#diamond-theorem-lemma1-lean)
- [Previous declaration in this file](traceNormOp_density_eq_one.md)
- [Next declaration in this file](traceNormOp_eq_of_conjTranspose_mul_self_eq.md)