# swapMatrix_mul_self

## Source location

- Original Lean file: `Diamond/PositiveGap/Lemma6.lean`
- Declaration name: `swapMatrix_mul_self`
- Declaration kind: `theorem`

## Why this declaration exists

This theorem records a reusable fact named `swapMatrix_mul_self`. Its role is to make the later proof flow easier to state and reuse.

 In the file `PositiveGap/Lemma6.lean`, it contributes to the swap operator and its algebraic interaction with tensor products. Later proofs call this result by name, so documenting it makes the larger argument readable as a mathematical chain rather than as opaque proof script.

## Original code

```lean
theorem swapMatrix_mul_self (d : ℕ) :
    swapMatrix d * swapMatrix d = 1 := by
  ext i j
  rw [Matrix.mul_apply]
  rw [Finset.sum_eq_single (i.2, i.1)]
  · by_cases hij : i = j
    · subst hij
      simp [swapMatrix]
    · have hneq : ¬ (i.2 = j.2 ∧ i.1 = j.1) := by
        intro h
        apply hij
        cases i with
        | mk a b =>
          cases j with
          | mk c e =>
            simp only [Prod.mk.injEq] at h ⊢
            exact ⟨h.2, h.1⟩
      simp [swapMatrix, hneq, hij]
  · intro x _ hx
    have hzero : ¬ (i.1 = x.2 ∧ i.2 = x.1) := by
      intro h
      apply hx
      ext <;> simp [h.1, h.2]
    simp [swapMatrix, hzero]
  · intro hi
    simp at hi
```

## Block-by-block explanation

The explanation below follows the declaration block by block. Each block groups a coherent piece of the definition or proof, so the mathematical structure is easier to see than in a strictly line-oriented reading.

1. Code:
```lean
theorem swapMatrix_mul_self (d : ℕ) :
```
This line starts the `swapMatrix_mul_self` declaration. Because it begins with `theorem`, Lean now knows what kind of named object is being introduced.

2. Code:
```lean
    swapMatrix d * swapMatrix d = 1 := by
```
This line says that a proof script begins here. Everything indented underneath is a sequence of instructions that Lean will check step by step.  `Matrix d d ℂ` means a square matrix with complex entries; the index type `d` tells Lean which rows and columns exist.

3. Code:
```lean
  ext i j
```
This line invokes extensionality. To prove two maps or matrices are equal, Lean reduces the problem to checking their values entry by entry.

4. Code:
```lean
  rw [Matrix.mul_apply]
```
This line uses rewriting. Lean replaces one expression by an equal expression using the lemmas listed in brackets.

5. Code:
```lean
  rw [Finset.sum_eq_single (i.2, i.1)]
```
This line uses rewriting. Lean replaces one expression by an equal expression using the lemmas listed in brackets.

6. Code:
```lean
  · by_cases hij : i = j
```
This bullet starts a new subgoal produced by the previous tactic. Lean is now focusing on one branch of the argument.

7. Code:
```lean
    · subst hij
```
This bullet starts a new subgoal produced by the previous tactic. Lean is now focusing on one branch of the argument.

8. Code:
```lean
      simp [swapMatrix]
```
This line simplifies the goal using definitions and known equalities. `simpa` means that, after simplification, the desired statement matches a theorem Lean already has.

9. Code:
```lean
    · have hneq : ¬ (i.2 = j.2 ∧ i.1 = j.1) := by
```
This line says that a proof script begins here. Everything indented underneath is a sequence of instructions that Lean will check step by step.

10. Code:
```lean
        intro h
```
This line introduces the variable or hypothesis named here into the proof context. In ordinary mathematical prose, it is the same as saying “let” or “assume”.

11. Code:
```lean
        apply hij
```
This line applies an existing theorem to the current goal. Lean then asks the author to prove the theorem’s hypotheses.

12. Code:
```lean
        cases i with
```
This line breaks a structured object into cases or components so that each can be handled separately.

13. Code:
```lean
        | mk a b =>
```
This line starts one branch of a pattern match or case split.

14. Code:
```lean
          cases j with
```
This line breaks a structured object into cases or components so that each can be handled separately.

15. Code:
```lean
          | mk c e =>
```
This line starts one branch of a pattern match or case split.

16. Code:
```lean
            simp only [Prod.mk.injEq] at h ⊢
```
This line simplifies the goal using definitions and known equalities. `simpa` means that, after simplification, the desired statement matches a theorem Lean already has.

17. Code:
```lean
            exact ⟨h.2, h.1⟩
```
This line finishes the current goal by giving Lean the exact theorem, lemma, or term that proves it.

18. Code:
```lean
      simp [swapMatrix, hneq, hij]
```
This line simplifies the goal using definitions and known equalities. `simpa` means that, after simplification, the desired statement matches a theorem Lean already has.

19. Code:
```lean
  · intro x _ hx
```
This bullet starts a new subgoal produced by the previous tactic. Lean is now focusing on one branch of the argument.

20. Code:
```lean
    have hzero : ¬ (i.1 = x.2 ∧ i.2 = x.1) := by
```
This line says that a proof script begins here. Everything indented underneath is a sequence of instructions that Lean will check step by step.

21. Code:
```lean
      intro h
```
This line introduces the variable or hypothesis named here into the proof context. In ordinary mathematical prose, it is the same as saying “let” or “assume”.

22. Code:
```lean
      apply hx
```
This line applies an existing theorem to the current goal. Lean then asks the author to prove the theorem’s hypotheses.

23. Code:
```lean
      ext <;> simp [h.1, h.2]
```
This line invokes extensionality. To prove two maps or matrices are equal, Lean reduces the problem to checking their values entry by entry.

24. Code:
```lean
    simp [swapMatrix, hzero]
```
This line simplifies the goal using definitions and known equalities. `simpa` means that, after simplification, the desired statement matches a theorem Lean already has.

25. Code:
```lean
  · intro hi
```
This bullet starts a new subgoal produced by the previous tactic. Lean is now focusing on one branch of the argument.

26. Code:
```lean
    simp at hi
```
This line simplifies the goal using definitions and known equalities. `simpa` means that, after simplification, the desired statement matches a theorem Lean already has.

## Mathematical summary

Restated without Lean syntax, `swapMatrix_mul_self` is the theorem or lemma written above.

- State the desired identity or inequality in Lean’s syntax.
- Introduce temporary names and intermediate claims that organize the argument.
- Use rewriting, simplification, and earlier lemmas to reduce the goal to standard matrix or norm manipulations.
- Close the remaining algebraic or order-theoretic steps with Lean’s proof tactics.

## Dependencies and downstream use

### Earlier declarations this depends on
- [`swapMatrix`](swapMatrix.md) from `PositiveGap/Lemma6.lean`

### Later declarations that use this one
- [`swapMatrix_conjTranspose_mul_self`](swapMatrix_conjTranspose_mul_self.md) in `PositiveGap/Lemma6.lean`

## Backlinks

- [Back to `INDEX.md`](../../INDEX.md)
- [Back to the `PositiveGap/Lemma6.lean` section in the index](../../INDEX.md#diamond-positivegap-lemma6-lean)
- [Previous declaration in this file](swapMatrix.md)
- [Next declaration in this file](swapMatrix_conjTranspose.md)