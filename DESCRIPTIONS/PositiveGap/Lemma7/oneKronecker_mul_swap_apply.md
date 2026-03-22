# oneKronecker_mul_swap_apply

## Source location

- Original Lean file: `Diamond/PositiveGap/Lemma7.lean`
- Declaration name: `oneKronecker_mul_swap_apply`
- Declaration kind: `theorem`

## Why this declaration exists

This theorem records a reusable fact named `oneKronecker_mul_swap_apply`. Its role is to make the later proof flow easier to state and reuse.

 In the file `PositiveGap/Lemma7.lean`, it contributes to the partial-transpose formula for rank-one operators written in vectorized form. Later proofs call this result by name, so documenting it makes the larger argument readable as a mathematical chain rather than as opaque proof script.

## Original code

```lean
theorem oneKronecker_mul_swap_apply (d : ℕ)
    (A : Matrix (Fin d) (Fin d) ℂ) (a b c e : Fin d) :
    (((1 : Matrix (Fin d) (Fin d) ℂ) ⊗ₖ A) * swapMatrix d) (a, b) (c, e) =
      if a = e then A b c else 0 := by
  rw [Matrix.mul_apply]
  rw [Finset.sum_eq_single (e, c)]
  · simp [swapMatrix, Matrix.kroneckerMap_apply, Matrix.one_apply]
  · intro x _ hx
    have hzero : ¬ (x.1 = e ∧ x.2 = c) := by
      intro h
      apply hx
      ext <;> simp [h.1, h.2]
    simp [swapMatrix, Matrix.kroneckerMap_apply, Matrix.one_apply, hzero]
  · intro hec
    simp at hec

-- Paper: Lemma 7
```

## Block-by-block explanation

The explanation below follows the declaration block by block. Each block groups a coherent piece of the definition or proof, so the mathematical structure is easier to see than in a strictly line-oriented reading.

1. Code:
```lean
theorem oneKronecker_mul_swap_apply (d : ℕ)
```
This line starts the `oneKronecker_mul_swap_apply` declaration. Because it begins with `theorem`, Lean now knows what kind of named object is being introduced.

2. Code:
```lean
    (A : Matrix (Fin d) (Fin d) ℂ) (a b c e : Fin d) :
```
This line is one local step in the declaration. It either refines the formula being defined or advances the proof by a small algebraic or logical move.  `Matrix d d ℂ` means a square matrix with complex entries; the index type `d` tells Lean which rows and columns exist.

3. Code:
```lean
    (((1 : Matrix (Fin d) (Fin d) ℂ) ⊗ₖ A) * swapMatrix d) (a, b) (c, e) =
```
This line is one local step in the declaration. It either refines the formula being defined or advances the proof by a small algebraic or logical move.  `Matrix d d ℂ` means a square matrix with complex entries; the index type `d` tells Lean which rows and columns exist.  The symbol `⊗ₖ` is the Kronecker (tensor) product of matrices.

4. Code:
```lean
      if a = e then A b c else 0 := by
```
This line says that a proof script begins here. Everything indented underneath is a sequence of instructions that Lean will check step by step.

5. Code:
```lean
  rw [Matrix.mul_apply]
```
This line uses rewriting. Lean replaces one expression by an equal expression using the lemmas listed in brackets.

6. Code:
```lean
  rw [Finset.sum_eq_single (e, c)]
```
This line uses rewriting. Lean replaces one expression by an equal expression using the lemmas listed in brackets.

7. Code:
```lean
  · simp [swapMatrix, Matrix.kroneckerMap_apply, Matrix.one_apply]
```
This bullet starts a new subgoal produced by the previous tactic. Lean is now focusing on one branch of the argument.

8. Code:
```lean
  · intro x _ hx
```
This bullet starts a new subgoal produced by the previous tactic. Lean is now focusing on one branch of the argument.

9. Code:
```lean
    have hzero : ¬ (x.1 = e ∧ x.2 = c) := by
```
This line says that a proof script begins here. Everything indented underneath is a sequence of instructions that Lean will check step by step.

10. Code:
```lean
      intro h
```
This line introduces the variable or hypothesis named here into the proof context. In ordinary mathematical prose, it is the same as saying “let” or “assume”.

11. Code:
```lean
      apply hx
```
This line applies an existing theorem to the current goal. Lean then asks the author to prove the theorem’s hypotheses.

12. Code:
```lean
      ext <;> simp [h.1, h.2]
```
This line invokes extensionality. To prove two maps or matrices are equal, Lean reduces the problem to checking their values entry by entry.

13. Code:
```lean
    simp [swapMatrix, Matrix.kroneckerMap_apply, Matrix.one_apply, hzero]
```
This line simplifies the goal using definitions and known equalities. `simpa` means that, after simplification, the desired statement matches a theorem Lean already has.

14. Code:
```lean
  · intro hec
```
This bullet starts a new subgoal produced by the previous tactic. Lean is now focusing on one branch of the argument.

15. Code:
```lean
    simp at hec
```
This line simplifies the goal using definitions and known equalities. `simpa` means that, after simplification, the desired statement matches a theorem Lean already has.

16. Code:
```lean
-- Paper: Lemma 7
```
This line is one local step in the declaration. It either refines the formula being defined or advances the proof by a small algebraic or logical move.

## Mathematical summary

Restated without Lean syntax, `oneKronecker_mul_swap_apply` is the theorem or lemma written above.

- State the desired identity or inequality in Lean’s syntax.
- Introduce temporary names and intermediate claims that organize the argument.
- Use rewriting, simplification, and earlier lemmas to reduce the goal to standard matrix or norm manipulations.
- Close the remaining algebraic or order-theoretic steps with Lean’s proof tactics.

## Dependencies and downstream use

### Earlier declarations this depends on
- [`swapMatrix`](../Lemma6/swapMatrix.md) from `PositiveGap/Lemma6.lean`

### Later declarations that use this one
- [`lemma7`](lemma7.md) in `PositiveGap/Lemma7.lean`

## Backlinks

- [Back to `INDEX.md`](../../INDEX.md)
- [Back to the `PositiveGap/Lemma7.lean` section in the index](../../INDEX.md#diamond-positivegap-lemma7-lean)
- [Next declaration in this file](lemma7.md)