# explicit_witness_eq_swap_diagonal

## Source location

- Original Lean file: `Diamond/EndMatter/Eq7.lean`
- Declaration name: `explicit_witness_eq_swap_diagonal`
- Declaration kind: `theorem`

## Why this declaration exists

The explicit witness is a swap times a diagonal matrix.

 In the file `EndMatter/Eq7.lean`, it contributes to the explicit witness construction used to prove the lower bound labelled Eq. (7). Later proofs call this result by name, so documenting it makes the larger argument readable as a mathematical chain rather than as opaque proof script.

## Original code

```lean
/-- The explicit witness is a swap times a diagonal matrix. -/
theorem explicit_witness_eq_swap_diagonal (d : ℕ) [Fact (1 < d)] :
    ((d : ℂ)⁻¹ •
      (swapMatrix d - swapMatrix d * ((Ud d)ᵀ ⊗ₖ star (Ud d)))) =
    swapMatrix d * Matrix.diagonal (fun ab =>
      (d : ℂ)⁻¹ * (1 - Ud d ab.1 ab.1 * star (Ud d ab.2 ab.2))) := by
  ext i j
  rcases i with ⟨a, b⟩
  rcases j with ⟨c, e⟩
  by_cases h : b = c ∧ a = e
  · rcases h with ⟨hbc, hae⟩
    subst hbc
    subst hae
    have hswap : swapMatrix d (a, b) (b, a) = 1 := by
      simp [swapMatrix]
    have hphase :
        (swapMatrix d * ((Ud d)ᵀ ⊗ₖ star (Ud d))) (a, b) (b, a) =
          Ud d b b * star (Ud d a a) := by
      simpa using swapMatrix_mul_phase_apply d a b b a
    have hdiag :
        (swapMatrix d *
            Matrix.diagonal (fun ab : Fin d × Fin d =>
              (d : ℂ)⁻¹ * (1 - Ud d ab.1 ab.1 * star (Ud d ab.2 ab.2))))
            (a, b) (b, a) =
          (d : ℂ)⁻¹ * (1 - Ud d b b * star (Ud d a a)) := by
      simpa using
        swapMatrix_mul_diagonal_apply d
          (fun ab : Fin d × Fin d =>
            (d : ℂ)⁻¹ * (1 - Ud d ab.1 ab.1 * star (Ud d ab.2 ab.2)))
          a b b a
    rw [hdiag]
    simp [hswap, hphase, sub_eq_add_neg]
  · have hcases : ¬ b = c ∨ ¬ a = e := by
      by_cases hbc : b = c
      · right
        intro hae
        apply h
        exact ⟨hbc, hae⟩
      · left
        exact hbc
    rcases hcases with hbc | hae
    · have hcb : ¬ c = b := by
        simpa [eq_comm] using hbc
      have hswap : swapMatrix d (a, b) (c, e) = 0 := by
        simp [swapMatrix, hbc]
      have hphase :
          (swapMatrix d * ((Ud d)ᵀ ⊗ₖ star (Ud d))) (a, b) (c, e) = 0 := by
        simpa [hbc] using swapMatrix_mul_phase_apply d a b c e
      have hdiag :
          (swapMatrix d *
              Matrix.diagonal (fun ab : Fin d × Fin d =>
                (d : ℂ)⁻¹ * (1 - Ud d ab.1 ab.1 * star (Ud d ab.2 ab.2))))
              (a, b) (c, e) = 0 := by
        simpa [hbc] using
          swapMatrix_mul_diagonal_apply d
            (fun ab : Fin d × Fin d =>
              (d : ℂ)⁻¹ * (1 - Ud d ab.1 ab.1 * star (Ud d ab.2 ab.2)))
            a b c e
      rw [hdiag]
      simp [Matrix.sub_apply, hswap, hphase]
    · have hea : ¬ e = a := by
        simpa [eq_comm] using hae
      have hswap : swapMatrix d (a, b) (c, e) = 0 := by
        simp [swapMatrix, hae]
      have hphase :
          (swapMatrix d * ((Ud d)ᵀ ⊗ₖ star (Ud d))) (a, b) (c, e) = 0 := by
        simpa [hae] using swapMatrix_mul_phase_apply d a b c e
      have hdiag :
          (swapMatrix d *
              Matrix.diagonal (fun ab : Fin d × Fin d =>
                (d : ℂ)⁻¹ * (1 - Ud d ab.1 ab.1 * star (Ud d ab.2 ab.2))))
              (a, b) (c, e) = 0 := by
        simpa [hae] using
          swapMatrix_mul_diagonal_apply d
            (fun ab : Fin d × Fin d =>
              (d : ℂ)⁻¹ * (1 - Ud d ab.1 ab.1 * star (Ud d ab.2 ab.2)))
            a b c e
      rw [hdiag]
      simp [Matrix.sub_apply, hswap, hphase]
```

## Block-by-block explanation

The explanation below follows the declaration block by block. Each block groups a coherent piece of the definition or proof, so the mathematical structure is easier to see than in a strictly line-oriented reading.

1. Code:
```lean
/-- The explicit witness is a swap times a diagonal matrix. -/
```
This is a Lean docstring. It is a human-written comment that tells readers what the declaration is meant to express before the formal code begins.

2. Code:
```lean
theorem explicit_witness_eq_swap_diagonal (d : ℕ) [Fact (1 < d)] :
```
This line starts the `explicit_witness_eq_swap_diagonal` declaration. Because it begins with `theorem`, Lean now knows what kind of named object is being introduced.

3. Code:
```lean
    ((d : ℂ)⁻¹ •
```
This line is one local step in the declaration. It either refines the formula being defined or advances the proof by a small algebraic or logical move.

4. Code:
```lean
      (swapMatrix d - swapMatrix d * ((Ud d)ᵀ ⊗ₖ star (Ud d)))) =
```
This line is one local step in the declaration. It either refines the formula being defined or advances the proof by a small algebraic or logical move.  `Matrix d d ℂ` means a square matrix with complex entries; the index type `d` tells Lean which rows and columns exist.  The symbol `⊗ₖ` is the Kronecker (tensor) product of matrices.  The superscript `ᵀ` means ordinary transpose.

5. Code:
```lean
    swapMatrix d * Matrix.diagonal (fun ab =>
```
This line is one local step in the declaration. It either refines the formula being defined or advances the proof by a small algebraic or logical move.  `Matrix d d ℂ` means a square matrix with complex entries; the index type `d` tells Lean which rows and columns exist.

6. Code:
```lean
      (d : ℂ)⁻¹ * (1 - Ud d ab.1 ab.1 * star (Ud d ab.2 ab.2))) := by
```
This line says that a proof script begins here. Everything indented underneath is a sequence of instructions that Lean will check step by step.

7. Code:
```lean
  ext i j
```
This line invokes extensionality. To prove two maps or matrices are equal, Lean reduces the problem to checking their values entry by entry.

8. Code:
```lean
  rcases i with ⟨a, b⟩
```
This line is one local step in the declaration. It either refines the formula being defined or advances the proof by a small algebraic or logical move.

9. Code:
```lean
  rcases j with ⟨c, e⟩
```
This line is one local step in the declaration. It either refines the formula being defined or advances the proof by a small algebraic or logical move.

10. Code:
```lean
  by_cases h : b = c ∧ a = e
```
This line splits the proof into cases according to whether the named proposition is true or false.

11. Code:
```lean
  · rcases h with ⟨hbc, hae⟩
```
This bullet starts a new subgoal produced by the previous tactic. Lean is now focusing on one branch of the argument.

12. Code:
```lean
    subst hbc
```
This line substitutes an equality into the goal and context, replacing one symbol by an equal one everywhere.

13. Code:
```lean
    subst hae
```
This line substitutes an equality into the goal and context, replacing one symbol by an equal one everywhere.

14. Code:
```lean
    have hswap : swapMatrix d (a, b) (b, a) = 1 := by
```
This line says that a proof script begins here. Everything indented underneath is a sequence of instructions that Lean will check step by step.  `Matrix d d ℂ` means a square matrix with complex entries; the index type `d` tells Lean which rows and columns exist.

15. Code:
```lean
      simp [swapMatrix]
```
This line simplifies the goal using definitions and known equalities. `simpa` means that, after simplification, the desired statement matches a theorem Lean already has.

16. Code:
```lean
    have hphase :
```
This line introduces an intermediate claim. The proof pauses to establish a fact that will be used shortly afterwards.

17. Code:
```lean
        (swapMatrix d * ((Ud d)ᵀ ⊗ₖ star (Ud d))) (a, b) (b, a) =
```
This line is one local step in the declaration. It either refines the formula being defined or advances the proof by a small algebraic or logical move.  `Matrix d d ℂ` means a square matrix with complex entries; the index type `d` tells Lean which rows and columns exist.  The symbol `⊗ₖ` is the Kronecker (tensor) product of matrices.  The superscript `ᵀ` means ordinary transpose.

18. Code:
```lean
          Ud d b b * star (Ud d a a) := by
```
This line says that a proof script begins here. Everything indented underneath is a sequence of instructions that Lean will check step by step.

19. Code:
```lean
      simpa using swapMatrix_mul_phase_apply d a b b a
```
This line simplifies the goal using definitions and known equalities. `simpa` means that, after simplification, the desired statement matches a theorem Lean already has.

20. Code:
```lean
    have hdiag :
```
This line introduces an intermediate claim. The proof pauses to establish a fact that will be used shortly afterwards.

21. Code:
```lean
        (swapMatrix d *
```
This line is one local step in the declaration. It either refines the formula being defined or advances the proof by a small algebraic or logical move.  `Matrix d d ℂ` means a square matrix with complex entries; the index type `d` tells Lean which rows and columns exist.

22. Code:
```lean
            Matrix.diagonal (fun ab : Fin d × Fin d =>
```
This line is one local step in the declaration. It either refines the formula being defined or advances the proof by a small algebraic or logical move.

23. Code:
```lean
              (d : ℂ)⁻¹ * (1 - Ud d ab.1 ab.1 * star (Ud d ab.2 ab.2))))
```
This line is one local step in the declaration. It either refines the formula being defined or advances the proof by a small algebraic or logical move.

24. Code:
```lean
            (a, b) (b, a) =
```
This line is one local step in the declaration. It either refines the formula being defined or advances the proof by a small algebraic or logical move.

25. Code:
```lean
          (d : ℂ)⁻¹ * (1 - Ud d b b * star (Ud d a a)) := by
```
This line says that a proof script begins here. Everything indented underneath is a sequence of instructions that Lean will check step by step.

26. Code:
```lean
      simpa using
```
This line simplifies the goal using definitions and known equalities. `simpa` means that, after simplification, the desired statement matches a theorem Lean already has.

27. Code:
```lean
        swapMatrix_mul_diagonal_apply d
```
This line is one local step in the declaration. It either refines the formula being defined or advances the proof by a small algebraic or logical move.

28. Code:
```lean
          (fun ab : Fin d × Fin d =>
```
This line is one local step in the declaration. It either refines the formula being defined or advances the proof by a small algebraic or logical move.

29. Code:
```lean
            (d : ℂ)⁻¹ * (1 - Ud d ab.1 ab.1 * star (Ud d ab.2 ab.2)))
```
This line is one local step in the declaration. It either refines the formula being defined or advances the proof by a small algebraic or logical move.

30. Code:
```lean
          a b b a
```
This line is one local step in the declaration. It either refines the formula being defined or advances the proof by a small algebraic or logical move.

31. Code:
```lean
    rw [hdiag]
```
This line uses rewriting. Lean replaces one expression by an equal expression using the lemmas listed in brackets.

32. Code:
```lean
    simp [hswap, hphase, sub_eq_add_neg]
```
This line simplifies the goal using definitions and known equalities. `simpa` means that, after simplification, the desired statement matches a theorem Lean already has.

33. Code:
```lean
  · have hcases : ¬ b = c ∨ ¬ a = e := by
```
This line says that a proof script begins here. Everything indented underneath is a sequence of instructions that Lean will check step by step.

34. Code:
```lean
      by_cases hbc : b = c
```
This line splits the proof into cases according to whether the named proposition is true or false.

35. Code:
```lean
      · right
```
This bullet starts a new subgoal produced by the previous tactic. Lean is now focusing on one branch of the argument.

36. Code:
```lean
        intro hae
```
This line introduces the variable or hypothesis named here into the proof context. In ordinary mathematical prose, it is the same as saying “let” or “assume”.

37. Code:
```lean
        apply h
```
This line applies an existing theorem to the current goal. Lean then asks the author to prove the theorem’s hypotheses.

38. Code:
```lean
        exact ⟨hbc, hae⟩
```
This line finishes the current goal by giving Lean the exact theorem, lemma, or term that proves it.

39. Code:
```lean
      · left
```
This bullet starts a new subgoal produced by the previous tactic. Lean is now focusing on one branch of the argument.

40. Code:
```lean
        exact hbc
```
This line finishes the current goal by giving Lean the exact theorem, lemma, or term that proves it.

41. Code:
```lean
    rcases hcases with hbc | hae
```
This line is one local step in the declaration. It either refines the formula being defined or advances the proof by a small algebraic or logical move.

42. Code:
```lean
    · have hcb : ¬ c = b := by
```
This line says that a proof script begins here. Everything indented underneath is a sequence of instructions that Lean will check step by step.

43. Code:
```lean
        simpa [eq_comm] using hbc
```
This line simplifies the goal using definitions and known equalities. `simpa` means that, after simplification, the desired statement matches a theorem Lean already has.

44. Code:
```lean
      have hswap : swapMatrix d (a, b) (c, e) = 0 := by
```
This line says that a proof script begins here. Everything indented underneath is a sequence of instructions that Lean will check step by step.  `Matrix d d ℂ` means a square matrix with complex entries; the index type `d` tells Lean which rows and columns exist.

45. Code:
```lean
        simp [swapMatrix, hbc]
```
This line simplifies the goal using definitions and known equalities. `simpa` means that, after simplification, the desired statement matches a theorem Lean already has.

46. Code:
```lean
      have hphase :
```
This line introduces an intermediate claim. The proof pauses to establish a fact that will be used shortly afterwards.

47. Code:
```lean
          (swapMatrix d * ((Ud d)ᵀ ⊗ₖ star (Ud d))) (a, b) (c, e) = 0 := by
```
This line says that a proof script begins here. Everything indented underneath is a sequence of instructions that Lean will check step by step.  `Matrix d d ℂ` means a square matrix with complex entries; the index type `d` tells Lean which rows and columns exist.  The symbol `⊗ₖ` is the Kronecker (tensor) product of matrices.  The superscript `ᵀ` means ordinary transpose.

48. Code:
```lean
        simpa [hbc] using swapMatrix_mul_phase_apply d a b c e
```
This line simplifies the goal using definitions and known equalities. `simpa` means that, after simplification, the desired statement matches a theorem Lean already has.

49. Code:
```lean
      have hdiag :
```
This line introduces an intermediate claim. The proof pauses to establish a fact that will be used shortly afterwards.

50. Code:
```lean
          (swapMatrix d *
```
This line is one local step in the declaration. It either refines the formula being defined or advances the proof by a small algebraic or logical move.  `Matrix d d ℂ` means a square matrix with complex entries; the index type `d` tells Lean which rows and columns exist.

51. Code:
```lean
              Matrix.diagonal (fun ab : Fin d × Fin d =>
```
This line is one local step in the declaration. It either refines the formula being defined or advances the proof by a small algebraic or logical move.

52. Code:
```lean
                (d : ℂ)⁻¹ * (1 - Ud d ab.1 ab.1 * star (Ud d ab.2 ab.2))))
```
This line is one local step in the declaration. It either refines the formula being defined or advances the proof by a small algebraic or logical move.

53. Code:
```lean
              (a, b) (c, e) = 0 := by
```
This line says that a proof script begins here. Everything indented underneath is a sequence of instructions that Lean will check step by step.

54. Code:
```lean
        simpa [hbc] using
```
This line simplifies the goal using definitions and known equalities. `simpa` means that, after simplification, the desired statement matches a theorem Lean already has.

55. Code:
```lean
          swapMatrix_mul_diagonal_apply d
```
This line is one local step in the declaration. It either refines the formula being defined or advances the proof by a small algebraic or logical move.

56. Code:
```lean
            (fun ab : Fin d × Fin d =>
```
This line is one local step in the declaration. It either refines the formula being defined or advances the proof by a small algebraic or logical move.

57. Code:
```lean
              (d : ℂ)⁻¹ * (1 - Ud d ab.1 ab.1 * star (Ud d ab.2 ab.2)))
```
This line is one local step in the declaration. It either refines the formula being defined or advances the proof by a small algebraic or logical move.

58. Code:
```lean
            a b c e
```
This line is one local step in the declaration. It either refines the formula being defined or advances the proof by a small algebraic or logical move.

59. Code:
```lean
      rw [hdiag]
```
This line uses rewriting. Lean replaces one expression by an equal expression using the lemmas listed in brackets.

60. Code:
```lean
      simp [Matrix.sub_apply, hswap, hphase]
```
This line simplifies the goal using definitions and known equalities. `simpa` means that, after simplification, the desired statement matches a theorem Lean already has.

61. Code:
```lean
    · have hea : ¬ e = a := by
```
This line says that a proof script begins here. Everything indented underneath is a sequence of instructions that Lean will check step by step.

62. Code:
```lean
        simpa [eq_comm] using hae
```
This line simplifies the goal using definitions and known equalities. `simpa` means that, after simplification, the desired statement matches a theorem Lean already has.

63. Code:
```lean
      have hswap : swapMatrix d (a, b) (c, e) = 0 := by
```
This line says that a proof script begins here. Everything indented underneath is a sequence of instructions that Lean will check step by step.  `Matrix d d ℂ` means a square matrix with complex entries; the index type `d` tells Lean which rows and columns exist.

64. Code:
```lean
        simp [swapMatrix, hae]
```
This line simplifies the goal using definitions and known equalities. `simpa` means that, after simplification, the desired statement matches a theorem Lean already has.

65. Code:
```lean
      have hphase :
```
This line introduces an intermediate claim. The proof pauses to establish a fact that will be used shortly afterwards.

66. Code:
```lean
          (swapMatrix d * ((Ud d)ᵀ ⊗ₖ star (Ud d))) (a, b) (c, e) = 0 := by
```
This line says that a proof script begins here. Everything indented underneath is a sequence of instructions that Lean will check step by step.  `Matrix d d ℂ` means a square matrix with complex entries; the index type `d` tells Lean which rows and columns exist.  The symbol `⊗ₖ` is the Kronecker (tensor) product of matrices.  The superscript `ᵀ` means ordinary transpose.

67. Code:
```lean
        simpa [hae] using swapMatrix_mul_phase_apply d a b c e
```
This line simplifies the goal using definitions and known equalities. `simpa` means that, after simplification, the desired statement matches a theorem Lean already has.

68. Code:
```lean
      have hdiag :
```
This line introduces an intermediate claim. The proof pauses to establish a fact that will be used shortly afterwards.

69. Code:
```lean
          (swapMatrix d *
```
This line is one local step in the declaration. It either refines the formula being defined or advances the proof by a small algebraic or logical move.  `Matrix d d ℂ` means a square matrix with complex entries; the index type `d` tells Lean which rows and columns exist.

70. Code:
```lean
              Matrix.diagonal (fun ab : Fin d × Fin d =>
```
This line is one local step in the declaration. It either refines the formula being defined or advances the proof by a small algebraic or logical move.

71. Code:
```lean
                (d : ℂ)⁻¹ * (1 - Ud d ab.1 ab.1 * star (Ud d ab.2 ab.2))))
```
This line is one local step in the declaration. It either refines the formula being defined or advances the proof by a small algebraic or logical move.

72. Code:
```lean
              (a, b) (c, e) = 0 := by
```
This line says that a proof script begins here. Everything indented underneath is a sequence of instructions that Lean will check step by step.

73. Code:
```lean
        simpa [hae] using
```
This line simplifies the goal using definitions and known equalities. `simpa` means that, after simplification, the desired statement matches a theorem Lean already has.

74. Code:
```lean
          swapMatrix_mul_diagonal_apply d
```
This line is one local step in the declaration. It either refines the formula being defined or advances the proof by a small algebraic or logical move.

75. Code:
```lean
            (fun ab : Fin d × Fin d =>
```
This line is one local step in the declaration. It either refines the formula being defined or advances the proof by a small algebraic or logical move.

76. Code:
```lean
              (d : ℂ)⁻¹ * (1 - Ud d ab.1 ab.1 * star (Ud d ab.2 ab.2)))
```
This line is one local step in the declaration. It either refines the formula being defined or advances the proof by a small algebraic or logical move.

77. Code:
```lean
            a b c e
```
This line is one local step in the declaration. It either refines the formula being defined or advances the proof by a small algebraic or logical move.

78. Code:
```lean
      rw [hdiag]
```
This line uses rewriting. Lean replaces one expression by an equal expression using the lemmas listed in brackets.

79. Code:
```lean
      simp [Matrix.sub_apply, hswap, hphase]
```
This line simplifies the goal using definitions and known equalities. `simpa` means that, after simplification, the desired statement matches a theorem Lean already has.

## Mathematical summary

Restated without Lean syntax, `explicit_witness_eq_swap_diagonal` is the theorem or lemma written above.

- State the desired identity or inequality in Lean’s syntax.
- Introduce temporary names and intermediate claims that organize the argument.
- Use rewriting, simplification, and earlier lemmas to reduce the goal to standard matrix or norm manipulations.
- Close the remaining algebraic or order-theoretic steps with Lean’s proof tactics.

## Dependencies and downstream use

### Earlier declarations this depends on
- [`Ud`](../../Setups/Ud.md) from `Setups.lean`
- [`swapMatrix`](../../PositiveGap/Lemma6/swapMatrix.md) from `PositiveGap/Lemma6.lean`
- [`swapMatrix_mul_phase_apply`](swapMatrix_mul_phase_apply.md) from `EndMatter/Eq7.lean`
- [`swapMatrix_mul_diagonal_apply`](swapMatrix_mul_diagonal_apply.md) from `EndMatter/Eq7.lean`

### Later declarations that use this one
- [`explicit_witness_traceNorm_eq_sum`](explicit_witness_traceNorm_eq_sum.md) in `EndMatter/Eq7.lean`

## Backlinks

- [Back to `INDEX.md`](../../INDEX.md)
- [Back to the `EndMatter/Eq7.lean` section in the index](../../INDEX.md#diamond-endmatter-eq7-lean)
- [Previous declaration in this file](swapMatrix_mul_diagonal_apply.md)
- [Next declaration in this file](explicit_witness_traceNorm_eq_sum.md)