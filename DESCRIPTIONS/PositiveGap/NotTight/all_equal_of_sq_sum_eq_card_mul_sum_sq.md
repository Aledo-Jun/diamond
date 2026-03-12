# all_equal_of_sq_sum_eq_card_mul_sum_sq

## Source location

- Original Lean file: `Diamond/PositiveGap/NotTight.lean`
- Declaration name: `all_equal_of_sq_sum_eq_card_mul_sum_sq`
- Declaration kind: `lemma`

## Why this declaration exists

Equality in Cauchy--Schwarz for a finite real family forces all entries to be equal.

 In the file `PositiveGap/NotTight.lean`, it contributes to the finite-dimensional non-tightness argument and the equality-case analysis behind it. Later proofs call this result by name, so documenting it makes the larger argument readable as a mathematical chain rather than as opaque proof script.

## Original code

```lean
/-- Equality in Cauchy--Schwarz for a finite real family forces all entries to be equal. -/
private lemma all_equal_of_sq_sum_eq_card_mul_sum_sq
    {ι : Type u} [Fintype ι] [Nonempty ι] {a : ι → ℝ}
    (heq : (∑ i, a i) ^ 2 = (Fintype.card ι : ℝ) * ∑ i, (a i) ^ 2) :
    ∀ i j, a i = a j := by
  let avg : ℝ := (∑ i, a i) / (Fintype.card ι : ℝ)
  have hzero : ∑ i, (a i - avg) ^ 2 = 0 := by
    rw [sum_sq_sub_avg_eq]
    have hcard_ne : (Fintype.card ι : ℝ) ≠ 0 := by
      positivity
    have hdiv : (∑ i, a i) ^ 2 / (Fintype.card ι : ℝ) = ∑ i, (a i) ^ 2 := by
      exact (div_eq_iff hcard_ne).2 (by simpa [mul_comm] using heq)
    linarith
  have hsq_zero' := (Finset.sum_eq_zero_iff_of_nonneg (fun i hi => sq_nonneg _)).1 hzero
  intro i j
  have hi : a i = avg := by
    have hsq : (a i - avg) ^ 2 = 0 := hsq_zero' i (by simp)
    nlinarith
  have hj : a j = avg := by
    have hsq : (a j - avg) ^ 2 = 0 := hsq_zero' j (by simp)
    nlinarith
  linarith
```

## Line-by-line explanation

The explanation below follows the declaration one physical line at a time. For long proofs, some lines are tiny bookkeeping steps; those are still explained, but briefly.

1. Code:
```lean
/-- Equality in Cauchy--Schwarz for a finite real family forces all entries to be equal. -/
```
This is a Lean docstring. It is a human-written comment that tells readers what the declaration is meant to express before the formal code begins.

2. Code:
```lean
private lemma all_equal_of_sq_sum_eq_card_mul_sum_sq
```
This line starts the `all_equal_of_sq_sum_eq_card_mul_sum_sq` declaration. Because it begins with `lemma`, Lean now knows what kind of named object is being introduced.

3. Code:
```lean
    {ι : Type u} [Fintype ι] [Nonempty ι] {a : ι → ℝ}
```
This line is one local step in the declaration. It either refines the formula being defined or advances the proof by a small algebraic or logical move.  A bracket such as `[Fintype d]` tells Lean that the index set `d` is finite, so sums over all indices make sense.

4. Code:
```lean
    (heq : (∑ i, a i) ^ 2 = (Fintype.card ι : ℝ) * ∑ i, (a i) ^ 2) :
```
This line is one local step in the declaration. It either refines the formula being defined or advances the proof by a small algebraic or logical move.  `Fintype.card` is the size of a finite index set.

5. Code:
```lean
    ∀ i j, a i = a j := by
```
This line says that a proof script begins here. Everything indented underneath is a sequence of instructions that Lean will check step by step.

6. Code:
```lean
  let avg : ℝ := (∑ i, a i) / (Fintype.card ι : ℝ)
```
This line gives a temporary name to an expression. Doing that makes later lines shorter and easier to read.  `Fintype.card` is the size of a finite index set.

7. Code:
```lean
  have hzero : ∑ i, (a i - avg) ^ 2 = 0 := by
```
This line says that a proof script begins here. Everything indented underneath is a sequence of instructions that Lean will check step by step.

8. Code:
```lean
    rw [sum_sq_sub_avg_eq]
```
This line uses rewriting. Lean replaces one expression by an equal expression using the lemmas listed in brackets.

9. Code:
```lean
    have hcard_ne : (Fintype.card ι : ℝ) ≠ 0 := by
```
This line says that a proof script begins here. Everything indented underneath is a sequence of instructions that Lean will check step by step.  `Fintype.card` is the size of a finite index set.

10. Code:
```lean
      positivity
```
This line asks Lean to prove that the displayed quantity is positive or nonnegative using standard positivity rules.

11. Code:
```lean
    have hdiv : (∑ i, a i) ^ 2 / (Fintype.card ι : ℝ) = ∑ i, (a i) ^ 2 := by
```
This line says that a proof script begins here. Everything indented underneath is a sequence of instructions that Lean will check step by step.  `Fintype.card` is the size of a finite index set.

12. Code:
```lean
      exact (div_eq_iff hcard_ne).2 (by simpa [mul_comm] using heq)
```
This line finishes the current goal by giving Lean the exact theorem, lemma, or term that proves it.

13. Code:
```lean
    linarith
```
This line solves the current numerical inequality by combining the equalities and inequalities already available in the context.

14. Code:
```lean
  have hsq_zero' := (Finset.sum_eq_zero_iff_of_nonneg (fun i hi => sq_nonneg _)).1 hzero
```
This line introduces an intermediate claim. The proof pauses to establish a fact that will be used shortly afterwards.

15. Code:
```lean
  intro i j
```
This line introduces the variable or hypothesis named here into the proof context. In ordinary mathematical prose, it is the same as saying “let” or “assume”.

16. Code:
```lean
  have hi : a i = avg := by
```
This line says that a proof script begins here. Everything indented underneath is a sequence of instructions that Lean will check step by step.

17. Code:
```lean
    have hsq : (a i - avg) ^ 2 = 0 := hsq_zero' i (by simp)
```
This line introduces an intermediate claim. The proof pauses to establish a fact that will be used shortly afterwards.

18. Code:
```lean
    nlinarith
```
This line solves the current numerical inequality by combining the equalities and inequalities already available in the context.

19. Code:
```lean
  have hj : a j = avg := by
```
This line says that a proof script begins here. Everything indented underneath is a sequence of instructions that Lean will check step by step.

20. Code:
```lean
    have hsq : (a j - avg) ^ 2 = 0 := hsq_zero' j (by simp)
```
This line introduces an intermediate claim. The proof pauses to establish a fact that will be used shortly afterwards.

21. Code:
```lean
    nlinarith
```
This line solves the current numerical inequality by combining the equalities and inequalities already available in the context.

22. Code:
```lean
  linarith
```
This line solves the current numerical inequality by combining the equalities and inequalities already available in the context.

## Mathematical summary

Restated without Lean syntax, `all_equal_of_sq_sum_eq_card_mul_sum_sq` is the theorem or lemma written above.

- State the desired identity or inequality in Lean’s syntax.
- Introduce temporary names and intermediate claims that organize the argument.
- Use rewriting, simplification, and earlier lemmas to reduce the goal to standard matrix or norm manipulations.
- Close the remaining algebraic or order-theoretic steps with Lean’s proof tactics.

## Dependencies and downstream use

### Earlier declarations this depends on
- [`sum_sq_sub_avg_eq`](sum_sq_sub_avg_eq.md) from `PositiveGap/NotTight.lean`

### Later declarations that use this one
- [`lemma2_eq_imp_full_rank`](lemma2_eq_imp_full_rank.md) in `PositiveGap/NotTight.lean`

## Backlinks

- [Back to `INDEX.md`](../../INDEX.md)
- [Back to the `PositiveGap/NotTight.lean` section in the index](../../INDEX.md#diamond-positivegap-nottight-lean)
- [Previous declaration in this file](sum_sq_sub_avg_eq.md)
- [Next declaration in this file](lemma1_eq_imp_rank_two.md)