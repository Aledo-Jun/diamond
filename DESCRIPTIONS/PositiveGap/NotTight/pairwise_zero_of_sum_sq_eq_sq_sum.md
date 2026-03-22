# pairwise_zero_of_sum_sq_eq_sq_sum

## Source location

- Original Lean file: `Diamond/PositiveGap/NotTight.lean`
- Declaration name: `pairwise_zero_of_sum_sq_eq_sq_sum`
- Declaration kind: `lemma`

## Why this declaration exists

Equality in `∑ p_i^2 ≤ (∑ p_i)^2` forces all mixed terms to vanish.

 In the file `PositiveGap/NotTight.lean`, it contributes to the finite-dimensional non-tightness argument and the equality-case analysis behind it. Later proofs call this result by name, so documenting it makes the larger argument readable as a mathematical chain rather than as opaque proof script.

## Original code

```lean
/-- Equality in `∑ p_i^2 ≤ (∑ p_i)^2` forces all mixed terms to vanish. -/
private lemma pairwise_zero_of_sum_sq_eq_sq_sum
    {ι : Type u} [Fintype ι] {p : ι → ℝ}
    (hp : ∀ i, 0 ≤ p i)
    (heq : (∑ i, (p i) ^ 2) = (∑ i, p i) ^ 2) :
    ∀ i j, i ≠ j → p i = 0 ∨ p j = 0 := by
  classical
  have hoffDiag_zero : ∑ x ∈ (Finset.univ : Finset ι).offDiag, p x.1 * p x.2 = 0 := by
    have hexpand := sq_sum_expand_offDiag p
    linarith
  have hpair_zero :
      ∀ x ∈ (Finset.univ : Finset ι).offDiag, p x.1 * p x.2 = 0 := by
    exact
      (Finset.sum_eq_zero_iff_of_nonneg
        (fun x hx => mul_nonneg (hp x.1) (hp x.2))).1 hoffDiag_zero
  intro i j hij
  have hmem : (i, j) ∈ (Finset.univ : Finset ι).offDiag := by
    exact Finset.mem_offDiag.2 ⟨Finset.mem_univ i, Finset.mem_univ j, hij⟩
  have hmul : p i * p j = 0 := hpair_zero (i, j) hmem
  by_cases hi : p i = 0
  · exact Or.inl hi
  · right
    exact mul_eq_zero.mp hmul |>.resolve_left hi
```

## Block-by-block explanation

The explanation below follows the declaration block by block. Each block groups a coherent piece of the definition or proof, so the mathematical structure is easier to see than in a strictly line-oriented reading.

1. Code:
```lean
/-- Equality in `∑ p_i^2 ≤ (∑ p_i)^2` forces all mixed terms to vanish. -/
```
This is a Lean docstring. It is a human-written comment that tells readers what the declaration is meant to express before the formal code begins.

2. Code:
```lean
private lemma pairwise_zero_of_sum_sq_eq_sq_sum
```
This line starts the `pairwise_zero_of_sum_sq_eq_sq_sum` declaration. Because it begins with `lemma`, Lean now knows what kind of named object is being introduced.

3. Code:
```lean
    {ι : Type u} [Fintype ι] {p : ι → ℝ}
```
This line is one local step in the declaration. It either refines the formula being defined or advances the proof by a small algebraic or logical move.  A bracket such as `[Fintype d]` tells Lean that the index set `d` is finite, so sums over all indices make sense.

4. Code:
```lean
    (hp : ∀ i, 0 ≤ p i)
```
This line is one local step in the declaration. It either refines the formula being defined or advances the proof by a small algebraic or logical move.

5. Code:
```lean
    (heq : (∑ i, (p i) ^ 2) = (∑ i, p i) ^ 2) :
```
This line is one local step in the declaration. It either refines the formula being defined or advances the proof by a small algebraic or logical move.

6. Code:
```lean
    ∀ i j, i ≠ j → p i = 0 ∨ p j = 0 := by
```
This line says that a proof script begins here. Everything indented underneath is a sequence of instructions that Lean will check step by step.

7. Code:
```lean
  classical
```
This line is one local step in the declaration. It either refines the formula being defined or advances the proof by a small algebraic or logical move.

8. Code:
```lean
  have hoffDiag_zero : ∑ x ∈ (Finset.univ : Finset ι).offDiag, p x.1 * p x.2 = 0 := by
```
This line says that a proof script begins here. Everything indented underneath is a sequence of instructions that Lean will check step by step.

9. Code:
```lean
    have hexpand := sq_sum_expand_offDiag p
```
This line introduces an intermediate claim. The proof pauses to establish a fact that will be used shortly afterwards.

10. Code:
```lean
    linarith
```
This line solves the current numerical inequality by combining the equalities and inequalities already available in the context.

11. Code:
```lean
  have hpair_zero :
```
This line introduces an intermediate claim. The proof pauses to establish a fact that will be used shortly afterwards.

12. Code:
```lean
      ∀ x ∈ (Finset.univ : Finset ι).offDiag, p x.1 * p x.2 = 0 := by
```
This line says that a proof script begins here. Everything indented underneath is a sequence of instructions that Lean will check step by step.

13. Code:
```lean
    exact
```
This line finishes the current goal by giving Lean the exact theorem, lemma, or term that proves it.

14. Code:
```lean
      (Finset.sum_eq_zero_iff_of_nonneg
```
This line is one local step in the declaration. It either refines the formula being defined or advances the proof by a small algebraic or logical move.

15. Code:
```lean
        (fun x hx => mul_nonneg (hp x.1) (hp x.2))).1 hoffDiag_zero
```
This line is one local step in the declaration. It either refines the formula being defined or advances the proof by a small algebraic or logical move.

16. Code:
```lean
  intro i j hij
```
This line introduces the variable or hypothesis named here into the proof context. In ordinary mathematical prose, it is the same as saying “let” or “assume”.

17. Code:
```lean
  have hmem : (i, j) ∈ (Finset.univ : Finset ι).offDiag := by
```
This line says that a proof script begins here. Everything indented underneath is a sequence of instructions that Lean will check step by step.

18. Code:
```lean
    exact Finset.mem_offDiag.2 ⟨Finset.mem_univ i, Finset.mem_univ j, hij⟩
```
This line finishes the current goal by giving Lean the exact theorem, lemma, or term that proves it.

19. Code:
```lean
  have hmul : p i * p j = 0 := hpair_zero (i, j) hmem
```
This line introduces an intermediate claim. The proof pauses to establish a fact that will be used shortly afterwards.

20. Code:
```lean
  by_cases hi : p i = 0
```
This line splits the proof into cases according to whether the named proposition is true or false.

21. Code:
```lean
  · exact Or.inl hi
```
This bullet starts a new subgoal produced by the previous tactic. Lean is now focusing on one branch of the argument.

22. Code:
```lean
  · right
```
This bullet starts a new subgoal produced by the previous tactic. Lean is now focusing on one branch of the argument.

23. Code:
```lean
    exact mul_eq_zero.mp hmul |>.resolve_left hi
```
This line finishes the current goal by giving Lean the exact theorem, lemma, or term that proves it.

## Mathematical summary

Restated without Lean syntax, `pairwise_zero_of_sum_sq_eq_sq_sum` is the theorem or lemma written above.

- State the desired identity or inequality in Lean’s syntax.
- Introduce temporary names and intermediate claims that organize the argument.
- Use rewriting, simplification, and earlier lemmas to reduce the goal to standard matrix or norm manipulations.
- Close the remaining algebraic or order-theoretic steps with Lean’s proof tactics.

## Dependencies and downstream use

### Earlier declarations this depends on
- [`sq_sum_expand_offDiag`](sq_sum_expand_offDiag.md) from `PositiveGap/NotTight.lean`

### Later declarations that use this one
- [`lemma1_eq_imp_rank_two`](lemma1_eq_imp_rank_two.md) in `PositiveGap/NotTight.lean`

## Backlinks

- [Back to `INDEX.md`](../../INDEX.md)
- [Back to the `PositiveGap/NotTight.lean` section in the index](../../INDEX.md#diamond-positivegap-nottight-lean)
- [Previous declaration in this file](sq_sum_expand_offDiag.md)
- [Next declaration in this file](existsUnique_nonzero_of_pairwise_zero.md)