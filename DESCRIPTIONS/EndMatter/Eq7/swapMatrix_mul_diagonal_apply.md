# swapMatrix_mul_diagonal_apply

## Source location

- Original Lean file: `Diamond/EndMatter/Eq7.lean`
- Declaration name: `swapMatrix_mul_diagonal_apply`
- Declaration kind: `theorem`

## Why this declaration exists

Right-multiplying by a diagonal matrix keeps only the swapped diagonal entry.

 In the file `EndMatter/Eq7.lean`, it contributes to the explicit witness construction used to prove the lower bound labelled Eq. (7). Later proofs call this result by name, so documenting it makes the larger argument readable as a mathematical chain rather than as opaque proof script.

## Original code

```lean
/-- Right-multiplying by a diagonal matrix keeps only the swapped diagonal entry. -/
theorem swapMatrix_mul_diagonal_apply
    (d : ℕ) (f : Fin d × Fin d → ℂ) (a b c e : Fin d) :
    (swapMatrix d * Matrix.diagonal f) (a, b) (c, e) =
      if b = c ∧ a = e then f (c, e) else 0 := by
  rw [Matrix.mul_apply]
  rw [Finset.sum_eq_single (b, a)]
  · by_cases h : b = c ∧ a = e
    · rcases h with ⟨hbc, hae⟩
      simp [swapMatrix, hbc, hae]
    · have hcases : ¬ b = c ∨ ¬ a = e := by
        by_cases hbc : b = c
        · right
          intro hae
          apply h
          exact ⟨hbc, hae⟩
        · left
          exact hbc
      rcases hcases with hbc | hae
      · simp [swapMatrix, hbc]
      · have hea : ¬ e = a := by
          simpa [eq_comm] using hae
        simp [swapMatrix, hae]
  · intro x _ hne
    have hswap : ¬ (a = x.2 ∧ b = x.1) := by
      intro hx
      apply hne
      ext <;> simp [hx.1, hx.2]
    simp [swapMatrix, hswap]
  · intro hba
    simp at hba
```

## Line-by-line explanation

The explanation below follows the declaration one physical line at a time. For long proofs, some lines are tiny bookkeeping steps; those are still explained, but briefly.

1. Code:
```lean
/-- Right-multiplying by a diagonal matrix keeps only the swapped diagonal entry. -/
```
This is a Lean docstring. It is a human-written comment that tells readers what the declaration is meant to express before the formal code begins.

2. Code:
```lean
theorem swapMatrix_mul_diagonal_apply
```
This line starts the `swapMatrix_mul_diagonal_apply` declaration. Because it begins with `theorem`, Lean now knows what kind of named object is being introduced.

3. Code:
```lean
    (d : ℕ) (f : Fin d × Fin d → ℂ) (a b c e : Fin d) :
```
This line is one local step in the declaration. It either refines the formula being defined or advances the proof by a small algebraic or logical move.

4. Code:
```lean
    (swapMatrix d * Matrix.diagonal f) (a, b) (c, e) =
```
This line is one local step in the declaration. It either refines the formula being defined or advances the proof by a small algebraic or logical move.  `Matrix d d ℂ` means a square matrix with complex entries; the index type `d` tells Lean which rows and columns exist.

5. Code:
```lean
      if b = c ∧ a = e then f (c, e) else 0 := by
```
This line says that a proof script begins here. Everything indented underneath is a sequence of instructions that Lean will check step by step.

6. Code:
```lean
  rw [Matrix.mul_apply]
```
This line uses rewriting. Lean replaces one expression by an equal expression using the lemmas listed in brackets.

7. Code:
```lean
  rw [Finset.sum_eq_single (b, a)]
```
This line uses rewriting. Lean replaces one expression by an equal expression using the lemmas listed in brackets.

8. Code:
```lean
  · by_cases h : b = c ∧ a = e
```
This bullet starts a new subgoal produced by the previous tactic. Lean is now focusing on one branch of the argument.

9. Code:
```lean
    · rcases h with ⟨hbc, hae⟩
```
This bullet starts a new subgoal produced by the previous tactic. Lean is now focusing on one branch of the argument.

10. Code:
```lean
      simp [swapMatrix, hbc, hae]
```
This line simplifies the goal using definitions and known equalities. `simpa` means that, after simplification, the desired statement matches a theorem Lean already has.

11. Code:
```lean
    · have hcases : ¬ b = c ∨ ¬ a = e := by
```
This line says that a proof script begins here. Everything indented underneath is a sequence of instructions that Lean will check step by step.

12. Code:
```lean
        by_cases hbc : b = c
```
This line splits the proof into cases according to whether the named proposition is true or false.

13. Code:
```lean
        · right
```
This bullet starts a new subgoal produced by the previous tactic. Lean is now focusing on one branch of the argument.

14. Code:
```lean
          intro hae
```
This line introduces the variable or hypothesis named here into the proof context. In ordinary mathematical prose, it is the same as saying “let” or “assume”.

15. Code:
```lean
          apply h
```
This line applies an existing theorem to the current goal. Lean then asks the author to prove the theorem’s hypotheses.

16. Code:
```lean
          exact ⟨hbc, hae⟩
```
This line finishes the current goal by giving Lean the exact theorem, lemma, or term that proves it.

17. Code:
```lean
        · left
```
This bullet starts a new subgoal produced by the previous tactic. Lean is now focusing on one branch of the argument.

18. Code:
```lean
          exact hbc
```
This line finishes the current goal by giving Lean the exact theorem, lemma, or term that proves it.

19. Code:
```lean
      rcases hcases with hbc | hae
```
This line is one local step in the declaration. It either refines the formula being defined or advances the proof by a small algebraic or logical move.

20. Code:
```lean
      · simp [swapMatrix, hbc]
```
This bullet starts a new subgoal produced by the previous tactic. Lean is now focusing on one branch of the argument.

21. Code:
```lean
      · have hea : ¬ e = a := by
```
This line says that a proof script begins here. Everything indented underneath is a sequence of instructions that Lean will check step by step.

22. Code:
```lean
          simpa [eq_comm] using hae
```
This line simplifies the goal using definitions and known equalities. `simpa` means that, after simplification, the desired statement matches a theorem Lean already has.

23. Code:
```lean
        simp [swapMatrix, hae]
```
This line simplifies the goal using definitions and known equalities. `simpa` means that, after simplification, the desired statement matches a theorem Lean already has.

24. Code:
```lean
  · intro x _ hne
```
This bullet starts a new subgoal produced by the previous tactic. Lean is now focusing on one branch of the argument.

25. Code:
```lean
    have hswap : ¬ (a = x.2 ∧ b = x.1) := by
```
This line says that a proof script begins here. Everything indented underneath is a sequence of instructions that Lean will check step by step.

26. Code:
```lean
      intro hx
```
This line introduces the variable or hypothesis named here into the proof context. In ordinary mathematical prose, it is the same as saying “let” or “assume”.

27. Code:
```lean
      apply hne
```
This line applies an existing theorem to the current goal. Lean then asks the author to prove the theorem’s hypotheses.

28. Code:
```lean
      ext <;> simp [hx.1, hx.2]
```
This line invokes extensionality. To prove two maps or matrices are equal, Lean reduces the problem to checking their values entry by entry.

29. Code:
```lean
    simp [swapMatrix, hswap]
```
This line simplifies the goal using definitions and known equalities. `simpa` means that, after simplification, the desired statement matches a theorem Lean already has.

30. Code:
```lean
  · intro hba
```
This bullet starts a new subgoal produced by the previous tactic. Lean is now focusing on one branch of the argument.

31. Code:
```lean
    simp at hba
```
This line simplifies the goal using definitions and known equalities. `simpa` means that, after simplification, the desired statement matches a theorem Lean already has.

## Mathematical summary

Restated without Lean syntax, `swapMatrix_mul_diagonal_apply` is the theorem or lemma written above.

- State the desired identity or inequality in Lean’s syntax.
- Introduce temporary names and intermediate claims that organize the argument.
- Use rewriting, simplification, and earlier lemmas to reduce the goal to standard matrix or norm manipulations.
- Close the remaining algebraic or order-theoretic steps with Lean’s proof tactics.

## Dependencies and downstream use

### Earlier declarations this depends on
- [`swapMatrix`](../../PositiveGap/Lemma6/swapMatrix.md) from `PositiveGap/Lemma6.lean`

### Later declarations that use this one
- [`explicit_witness_eq_swap_diagonal`](explicit_witness_eq_swap_diagonal.md) in `EndMatter/Eq7.lean`

## Backlinks

- [Back to `INDEX.md`](../../INDEX.md)
- [Back to the `EndMatter/Eq7.lean` section in the index](../../INDEX.md#diamond-endmatter-eq7-lean)
- [Previous declaration in this file](ud_add_mul_star_eq.md)
- [Next declaration in this file](explicit_witness_eq_swap_diagonal.md)