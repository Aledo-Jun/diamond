# lemma6

## Source location

- Original Lean file: `Diamond/PositiveGap/Lemma6.lean`
- Declaration name: `lemma6`
- Declaration kind: `theorem`

## Why this declaration exists

This lemma proves the basic commutation rule between the swap operator and Kronecker products.

 In the file `PositiveGap/Lemma6.lean`, it contributes to the swap operator and its algebraic interaction with tensor products. Later proofs call this result by name, so documenting it makes the larger argument readable as a mathematical chain rather than as opaque proof script.

## Original code

```lean
theorem lemma6 (d : ℕ)
    (X Y : Matrix (Fin d) (Fin d) ℂ) :
    swapMatrix d * (X ⊗ₖ Y) = (Y ⊗ₖ X) * swapMatrix d := by
  ext i j
  rcases i with ⟨a, b⟩
  rcases j with ⟨c, e⟩
  have hleft :
      (swapMatrix d * (X ⊗ₖ Y)) (a, b) (c, e) = X b c * Y a e := by
    rw [Matrix.mul_apply]
    rw [Finset.sum_eq_single (b, a)]
    · simp [swapMatrix, Matrix.kroneckerMap_apply]
    · intro x _ hx
      have hzero : ¬ (a = x.2 ∧ b = x.1) := by
        intro h
        apply hx
        ext <;> simp [h.1, h.2]
      simp [swapMatrix, Matrix.kroneckerMap_apply, hzero]
    · intro hba
      simp at hba
  have hright :
      ((Y ⊗ₖ X) * swapMatrix d) (a, b) (c, e) = Y a e * X b c := by
    rw [Matrix.mul_apply]
    rw [Finset.sum_eq_single (e, c)]
    · simp [swapMatrix, Matrix.kroneckerMap_apply]
    · intro x _ hx
      have hzero : ¬ (x.1 = e ∧ x.2 = c) := by
        intro h
        apply hx
        ext <;> simp [h.1, h.2]
      simp [swapMatrix, Matrix.kroneckerMap_apply, hzero]
    · intro hec
      simp at hec
  rw [hleft, hright, mul_comm]
```

## Block-by-block explanation

The explanation below follows the declaration block by block. Each block groups a coherent piece of the definition or proof, so the mathematical structure is easier to see than in a strictly line-oriented reading.

1. Code:
```lean
theorem lemma6 (d : ℕ)
```
This line starts the `lemma6` declaration. Because it begins with `theorem`, Lean now knows what kind of named object is being introduced.

2. Code:
```lean
    (X Y : Matrix (Fin d) (Fin d) ℂ) :
```
This line is one local step in the declaration. It either refines the formula being defined or advances the proof by a small algebraic or logical move.  `Matrix d d ℂ` means a square matrix with complex entries; the index type `d` tells Lean which rows and columns exist.

3. Code:
```lean
    swapMatrix d * (X ⊗ₖ Y) = (Y ⊗ₖ X) * swapMatrix d := by
```
This line says that a proof script begins here. Everything indented underneath is a sequence of instructions that Lean will check step by step.  `Matrix d d ℂ` means a square matrix with complex entries; the index type `d` tells Lean which rows and columns exist.  The symbol `⊗ₖ` is the Kronecker (tensor) product of matrices.

4. Code:
```lean
  ext i j
```
This line invokes extensionality. To prove two maps or matrices are equal, Lean reduces the problem to checking their values entry by entry.

5. Code:
```lean
  rcases i with ⟨a, b⟩
```
This line is one local step in the declaration. It either refines the formula being defined or advances the proof by a small algebraic or logical move.

6. Code:
```lean
  rcases j with ⟨c, e⟩
```
This line is one local step in the declaration. It either refines the formula being defined or advances the proof by a small algebraic or logical move.

7. Code:
```lean
  have hleft :
```
This line introduces an intermediate claim. The proof pauses to establish a fact that will be used shortly afterwards.

8. Code:
```lean
      (swapMatrix d * (X ⊗ₖ Y)) (a, b) (c, e) = X b c * Y a e := by
```
This line says that a proof script begins here. Everything indented underneath is a sequence of instructions that Lean will check step by step.  `Matrix d d ℂ` means a square matrix with complex entries; the index type `d` tells Lean which rows and columns exist.  The symbol `⊗ₖ` is the Kronecker (tensor) product of matrices.

9. Code:
```lean
    rw [Matrix.mul_apply]
```
This line uses rewriting. Lean replaces one expression by an equal expression using the lemmas listed in brackets.

10. Code:
```lean
    rw [Finset.sum_eq_single (b, a)]
```
This line uses rewriting. Lean replaces one expression by an equal expression using the lemmas listed in brackets.

11. Code:
```lean
    · simp [swapMatrix, Matrix.kroneckerMap_apply]
```
This bullet starts a new subgoal produced by the previous tactic. Lean is now focusing on one branch of the argument.

12. Code:
```lean
    · intro x _ hx
```
This bullet starts a new subgoal produced by the previous tactic. Lean is now focusing on one branch of the argument.

13. Code:
```lean
      have hzero : ¬ (a = x.2 ∧ b = x.1) := by
```
This line says that a proof script begins here. Everything indented underneath is a sequence of instructions that Lean will check step by step.

14. Code:
```lean
        intro h
```
This line introduces the variable or hypothesis named here into the proof context. In ordinary mathematical prose, it is the same as saying “let” or “assume”.

15. Code:
```lean
        apply hx
```
This line applies an existing theorem to the current goal. Lean then asks the author to prove the theorem’s hypotheses.

16. Code:
```lean
        ext <;> simp [h.1, h.2]
```
This line invokes extensionality. To prove two maps or matrices are equal, Lean reduces the problem to checking their values entry by entry.

17. Code:
```lean
      simp [swapMatrix, Matrix.kroneckerMap_apply, hzero]
```
This line simplifies the goal using definitions and known equalities. `simpa` means that, after simplification, the desired statement matches a theorem Lean already has.

18. Code:
```lean
    · intro hba
```
This bullet starts a new subgoal produced by the previous tactic. Lean is now focusing on one branch of the argument.

19. Code:
```lean
      simp at hba
```
This line simplifies the goal using definitions and known equalities. `simpa` means that, after simplification, the desired statement matches a theorem Lean already has.

20. Code:
```lean
  have hright :
```
This line introduces an intermediate claim. The proof pauses to establish a fact that will be used shortly afterwards.

21. Code:
```lean
      ((Y ⊗ₖ X) * swapMatrix d) (a, b) (c, e) = Y a e * X b c := by
```
This line says that a proof script begins here. Everything indented underneath is a sequence of instructions that Lean will check step by step.  `Matrix d d ℂ` means a square matrix with complex entries; the index type `d` tells Lean which rows and columns exist.  The symbol `⊗ₖ` is the Kronecker (tensor) product of matrices.

22. Code:
```lean
    rw [Matrix.mul_apply]
```
This line uses rewriting. Lean replaces one expression by an equal expression using the lemmas listed in brackets.

23. Code:
```lean
    rw [Finset.sum_eq_single (e, c)]
```
This line uses rewriting. Lean replaces one expression by an equal expression using the lemmas listed in brackets.

24. Code:
```lean
    · simp [swapMatrix, Matrix.kroneckerMap_apply]
```
This bullet starts a new subgoal produced by the previous tactic. Lean is now focusing on one branch of the argument.

25. Code:
```lean
    · intro x _ hx
```
This bullet starts a new subgoal produced by the previous tactic. Lean is now focusing on one branch of the argument.

26. Code:
```lean
      have hzero : ¬ (x.1 = e ∧ x.2 = c) := by
```
This line says that a proof script begins here. Everything indented underneath is a sequence of instructions that Lean will check step by step.

27. Code:
```lean
        intro h
```
This line introduces the variable or hypothesis named here into the proof context. In ordinary mathematical prose, it is the same as saying “let” or “assume”.

28. Code:
```lean
        apply hx
```
This line applies an existing theorem to the current goal. Lean then asks the author to prove the theorem’s hypotheses.

29. Code:
```lean
        ext <;> simp [h.1, h.2]
```
This line invokes extensionality. To prove two maps or matrices are equal, Lean reduces the problem to checking their values entry by entry.

30. Code:
```lean
      simp [swapMatrix, Matrix.kroneckerMap_apply, hzero]
```
This line simplifies the goal using definitions and known equalities. `simpa` means that, after simplification, the desired statement matches a theorem Lean already has.

31. Code:
```lean
    · intro hec
```
This bullet starts a new subgoal produced by the previous tactic. Lean is now focusing on one branch of the argument.

32. Code:
```lean
      simp at hec
```
This line simplifies the goal using definitions and known equalities. `simpa` means that, after simplification, the desired statement matches a theorem Lean already has.

33. Code:
```lean
  rw [hleft, hright, mul_comm]
```
This line uses rewriting. Lean replaces one expression by an equal expression using the lemmas listed in brackets.

## Mathematical summary

Restated without Lean syntax, `lemma6` is the theorem or lemma written above.

- State the desired identity or inequality in Lean’s syntax.
- Introduce temporary names and intermediate claims that organize the argument.
- Use rewriting, simplification, and earlier lemmas to reduce the goal to standard matrix or norm manipulations.
- Close the remaining algebraic or order-theoretic steps with Lean’s proof tactics.

## Dependencies and downstream use

### Earlier declarations this depends on
- [`swapMatrix`](swapMatrix.md) from `PositiveGap/Lemma6.lean`

### Later declarations that use this one
- No later documented declaration mentions this name explicitly.

## Backlinks

- [Back to `INDEX.md`](../../INDEX.md)
- [Back to the `PositiveGap/Lemma6.lean` section in the index](../../INDEX.md#diamond-positivegap-lemma6-lean)
- [Previous declaration in this file](swapMatrix_conjTranspose_mul_self.md)