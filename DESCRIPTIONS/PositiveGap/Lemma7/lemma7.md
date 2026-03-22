# lemma7

## Source location

- Original Lean file: `Diamond/PositiveGap/Lemma7.lean`
- Declaration name: `lemma7`
- Declaration kind: `theorem`

## Why this declaration exists

This lemma rewrites partial transpose of a rank-one operator into the swap-matrix expression used later in the rank argument.

 In the file `PositiveGap/Lemma7.lean`, it contributes to the partial-transpose formula for rank-one operators written in vectorized form. Later proofs call this result by name, so documenting it makes the larger argument readable as a mathematical chain rather than as opaque proof script.

## Original code

```lean
theorem lemma7 (d : ℕ)
    (A B : Matrix (Fin d) (Fin d) ℂ) :
    tensorWithIdentity
        (Fin d)
        (Fin d)
        (transposeMap (Fin d))
        (Matrix.vecMulVec (vecKet d A) (star (vecKet d B))) =
      (((1 : Matrix (Fin d) (Fin d) ℂ) ⊗ₖ Aᵀ) * swapMatrix d) *
        ((1 : Matrix (Fin d) (Fin d) ℂ) ⊗ₖ B.map star) := by
  ext i j
  rcases i with ⟨p, i⟩
  rcases j with ⟨q, j⟩
  have hleft :
      tensorWithIdentity
          (Fin d)
          (Fin d)
          (transposeMap (Fin d))
          (Matrix.vecMulVec (vecKet d A) (star (vecKet d B)))
          (p, i)
          (q, j) =
        A q i * star (B p j) := by
    simp [tensorWithIdentity, transposeMap, Matrix.vecMulVec_apply, vecKet]
  have hright :
      ((((1 : Matrix (Fin d) (Fin d) ℂ) ⊗ₖ Aᵀ) * swapMatrix d) *
          ((1 : Matrix (Fin d) (Fin d) ℂ) ⊗ₖ B.map star))
          (p, i) (q, j) =
        A q i * star (B p j) := by
    rw [Matrix.mul_apply]
    rw [Finset.sum_eq_single (q, p)]
    · simp [oneKronecker_mul_swap_apply, Matrix.kroneckerMap_apply]
    · intro x _ hx
      by_cases hx1 : x.1 = q
      · by_cases hx2 : x.2 = p
        · apply (hx <| by ext <;> simp [hx1, hx2]).elim
        · have hleftzero :
              (((1 : Matrix (Fin d) (Fin d) ℂ) ⊗ₖ Aᵀ) * swapMatrix d) (p, i) x = 0 := by
            rw [oneKronecker_mul_swap_apply]
            simp [show ¬ p = x.2 by simpa [eq_comm] using hx2]
          simp [hleftzero, Matrix.kroneckerMap_apply, Matrix.one_apply, hx1]
      · have hrightzero :
            (((1 : Matrix (Fin d) (Fin d) ℂ) ⊗ₖ B.map star) x (q, j)) = 0 := by
          simp [Matrix.kroneckerMap_apply, hx1]
        rw [hrightzero]
        simp
    · intro hqp
      simp at hqp
  rw [hleft, hright]
```

## Block-by-block explanation

The explanation below follows the declaration block by block. Each block groups a coherent piece of the definition or proof, so the mathematical structure is easier to see than in a strictly line-oriented reading.

1. Code:
```lean
theorem lemma7 (d : ℕ)
```
This line starts the `lemma7` declaration. Because it begins with `theorem`, Lean now knows what kind of named object is being introduced.

2. Code:
```lean
    (A B : Matrix (Fin d) (Fin d) ℂ) :
```
This line is one local step in the declaration. It either refines the formula being defined or advances the proof by a small algebraic or logical move.  `Matrix d d ℂ` means a square matrix with complex entries; the index type `d` tells Lean which rows and columns exist.

3. Code:
```lean
    tensorWithIdentity
```
This line is one local step in the declaration. It either refines the formula being defined or advances the proof by a small algebraic or logical move.

4. Code:
```lean
        (Fin d)
```
This line is one local step in the declaration. It either refines the formula being defined or advances the proof by a small algebraic or logical move.

5. Code:
```lean
        (Fin d)
```
This line is one local step in the declaration. It either refines the formula being defined or advances the proof by a small algebraic or logical move.

6. Code:
```lean
        (transposeMap (Fin d))
```
This line is one local step in the declaration. It either refines the formula being defined or advances the proof by a small algebraic or logical move.

7. Code:
```lean
        (Matrix.vecMulVec (vecKet d A) (star (vecKet d B))) =
```
This line is one local step in the declaration. It either refines the formula being defined or advances the proof by a small algebraic or logical move.

8. Code:
```lean
      (((1 : Matrix (Fin d) (Fin d) ℂ) ⊗ₖ Aᵀ) * swapMatrix d) *
```
This line is one local step in the declaration. It either refines the formula being defined or advances the proof by a small algebraic or logical move.  `Matrix d d ℂ` means a square matrix with complex entries; the index type `d` tells Lean which rows and columns exist.  The symbol `⊗ₖ` is the Kronecker (tensor) product of matrices.  The superscript `ᵀ` means ordinary transpose.

9. Code:
```lean
        ((1 : Matrix (Fin d) (Fin d) ℂ) ⊗ₖ B.map star) := by
```
This line says that a proof script begins here. Everything indented underneath is a sequence of instructions that Lean will check step by step.  `Matrix d d ℂ` means a square matrix with complex entries; the index type `d` tells Lean which rows and columns exist.  The symbol `⊗ₖ` is the Kronecker (tensor) product of matrices.

10. Code:
```lean
  ext i j
```
This line invokes extensionality. To prove two maps or matrices are equal, Lean reduces the problem to checking their values entry by entry.

11. Code:
```lean
  rcases i with ⟨p, i⟩
```
This line is one local step in the declaration. It either refines the formula being defined or advances the proof by a small algebraic or logical move.

12. Code:
```lean
  rcases j with ⟨q, j⟩
```
This line is one local step in the declaration. It either refines the formula being defined or advances the proof by a small algebraic or logical move.

13. Code:
```lean
  have hleft :
```
This line introduces an intermediate claim. The proof pauses to establish a fact that will be used shortly afterwards.

14. Code:
```lean
      tensorWithIdentity
```
This line is one local step in the declaration. It either refines the formula being defined or advances the proof by a small algebraic or logical move.

15. Code:
```lean
          (Fin d)
```
This line is one local step in the declaration. It either refines the formula being defined or advances the proof by a small algebraic or logical move.

16. Code:
```lean
          (Fin d)
```
This line is one local step in the declaration. It either refines the formula being defined or advances the proof by a small algebraic or logical move.

17. Code:
```lean
          (transposeMap (Fin d))
```
This line is one local step in the declaration. It either refines the formula being defined or advances the proof by a small algebraic or logical move.

18. Code:
```lean
          (Matrix.vecMulVec (vecKet d A) (star (vecKet d B)))
```
This line is one local step in the declaration. It either refines the formula being defined or advances the proof by a small algebraic or logical move.

19. Code:
```lean
          (p, i)
```
This line is one local step in the declaration. It either refines the formula being defined or advances the proof by a small algebraic or logical move.

20. Code:
```lean
          (q, j) =
```
This line is one local step in the declaration. It either refines the formula being defined or advances the proof by a small algebraic or logical move.

21. Code:
```lean
        A q i * star (B p j) := by
```
This line says that a proof script begins here. Everything indented underneath is a sequence of instructions that Lean will check step by step.

22. Code:
```lean
    simp [tensorWithIdentity, transposeMap, Matrix.vecMulVec_apply, vecKet]
```
This line simplifies the goal using definitions and known equalities. `simpa` means that, after simplification, the desired statement matches a theorem Lean already has.

23. Code:
```lean
  have hright :
```
This line introduces an intermediate claim. The proof pauses to establish a fact that will be used shortly afterwards.

24. Code:
```lean
      ((((1 : Matrix (Fin d) (Fin d) ℂ) ⊗ₖ Aᵀ) * swapMatrix d) *
```
This line is one local step in the declaration. It either refines the formula being defined or advances the proof by a small algebraic or logical move.  `Matrix d d ℂ` means a square matrix with complex entries; the index type `d` tells Lean which rows and columns exist.  The symbol `⊗ₖ` is the Kronecker (tensor) product of matrices.  The superscript `ᵀ` means ordinary transpose.

25. Code:
```lean
          ((1 : Matrix (Fin d) (Fin d) ℂ) ⊗ₖ B.map star))
```
This line is one local step in the declaration. It either refines the formula being defined or advances the proof by a small algebraic or logical move.  `Matrix d d ℂ` means a square matrix with complex entries; the index type `d` tells Lean which rows and columns exist.  The symbol `⊗ₖ` is the Kronecker (tensor) product of matrices.

26. Code:
```lean
          (p, i) (q, j) =
```
This line is one local step in the declaration. It either refines the formula being defined or advances the proof by a small algebraic or logical move.

27. Code:
```lean
        A q i * star (B p j) := by
```
This line says that a proof script begins here. Everything indented underneath is a sequence of instructions that Lean will check step by step.

28. Code:
```lean
    rw [Matrix.mul_apply]
```
This line uses rewriting. Lean replaces one expression by an equal expression using the lemmas listed in brackets.

29. Code:
```lean
    rw [Finset.sum_eq_single (q, p)]
```
This line uses rewriting. Lean replaces one expression by an equal expression using the lemmas listed in brackets.

30. Code:
```lean
    · simp [oneKronecker_mul_swap_apply, Matrix.kroneckerMap_apply]
```
This bullet starts a new subgoal produced by the previous tactic. Lean is now focusing on one branch of the argument.

31. Code:
```lean
    · intro x _ hx
```
This bullet starts a new subgoal produced by the previous tactic. Lean is now focusing on one branch of the argument.

32. Code:
```lean
      by_cases hx1 : x.1 = q
```
This line splits the proof into cases according to whether the named proposition is true or false.

33. Code:
```lean
      · by_cases hx2 : x.2 = p
```
This bullet starts a new subgoal produced by the previous tactic. Lean is now focusing on one branch of the argument.

34. Code:
```lean
        · apply (hx <| by ext <;> simp [hx1, hx2]).elim
```
This bullet starts a new subgoal produced by the previous tactic. Lean is now focusing on one branch of the argument.

35. Code:
```lean
        · have hleftzero :
```
This bullet starts a new subgoal produced by the previous tactic. Lean is now focusing on one branch of the argument.

36. Code:
```lean
              (((1 : Matrix (Fin d) (Fin d) ℂ) ⊗ₖ Aᵀ) * swapMatrix d) (p, i) x = 0 := by
```
This line says that a proof script begins here. Everything indented underneath is a sequence of instructions that Lean will check step by step.  `Matrix d d ℂ` means a square matrix with complex entries; the index type `d` tells Lean which rows and columns exist.  The symbol `⊗ₖ` is the Kronecker (tensor) product of matrices.  The superscript `ᵀ` means ordinary transpose.

37. Code:
```lean
            rw [oneKronecker_mul_swap_apply]
```
This line uses rewriting. Lean replaces one expression by an equal expression using the lemmas listed in brackets.

38. Code:
```lean
            simp [show ¬ p = x.2 by simpa [eq_comm] using hx2]
```
This line simplifies the goal using definitions and known equalities. `simpa` means that, after simplification, the desired statement matches a theorem Lean already has.

39. Code:
```lean
          simp [hleftzero, Matrix.kroneckerMap_apply, Matrix.one_apply, hx1]
```
This line simplifies the goal using definitions and known equalities. `simpa` means that, after simplification, the desired statement matches a theorem Lean already has.

40. Code:
```lean
      · have hrightzero :
```
This bullet starts a new subgoal produced by the previous tactic. Lean is now focusing on one branch of the argument.

41. Code:
```lean
            (((1 : Matrix (Fin d) (Fin d) ℂ) ⊗ₖ B.map star) x (q, j)) = 0 := by
```
This line says that a proof script begins here. Everything indented underneath is a sequence of instructions that Lean will check step by step.  `Matrix d d ℂ` means a square matrix with complex entries; the index type `d` tells Lean which rows and columns exist.  The symbol `⊗ₖ` is the Kronecker (tensor) product of matrices.

42. Code:
```lean
          simp [Matrix.kroneckerMap_apply, hx1]
```
This line simplifies the goal using definitions and known equalities. `simpa` means that, after simplification, the desired statement matches a theorem Lean already has.

43. Code:
```lean
        rw [hrightzero]
```
This line uses rewriting. Lean replaces one expression by an equal expression using the lemmas listed in brackets.

44. Code:
```lean
        simp
```
This line simplifies the goal using definitions and known equalities. `simpa` means that, after simplification, the desired statement matches a theorem Lean already has.

45. Code:
```lean
    · intro hqp
```
This bullet starts a new subgoal produced by the previous tactic. Lean is now focusing on one branch of the argument.

46. Code:
```lean
      simp at hqp
```
This line simplifies the goal using definitions and known equalities. `simpa` means that, after simplification, the desired statement matches a theorem Lean already has.

47. Code:
```lean
  rw [hleft, hright]
```
This line uses rewriting. Lean replaces one expression by an equal expression using the lemmas listed in brackets.

## Mathematical summary

Restated without Lean syntax, `lemma7` is the theorem or lemma written above.

- State the desired identity or inequality in Lean’s syntax.
- Introduce temporary names and intermediate claims that organize the argument.
- Use rewriting, simplification, and earlier lemmas to reduce the goal to standard matrix or norm manipulations.
- Close the remaining algebraic or order-theoretic steps with Lean’s proof tactics.

## Dependencies and downstream use

### Earlier declarations this depends on
- [`transposeMap`](../../Setups/transposeMap.md) from `Setups.lean`
- [`tensorWithIdentity`](../../Setups/tensorWithIdentity.md) from `Setups.lean`
- [`vecKet`](../Lemma5/vecKet.md) from `PositiveGap/Lemma5.lean`
- [`swapMatrix`](../Lemma6/swapMatrix.md) from `PositiveGap/Lemma6.lean`
- [`oneKronecker_mul_swap_apply`](oneKronecker_mul_swap_apply.md) from `PositiveGap/Lemma7.lean`

### Later declarations that use this one
- No later documented declaration mentions this name explicitly.

## Backlinks

- [Back to `INDEX.md`](../../INDEX.md)
- [Back to the `PositiveGap/Lemma7.lean` section in the index](../../INDEX.md#diamond-positivegap-lemma7-lean)
- [Previous declaration in this file](oneKronecker_mul_swap_apply.md)