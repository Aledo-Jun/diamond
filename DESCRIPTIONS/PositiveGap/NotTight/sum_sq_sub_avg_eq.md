# sum_sq_sub_avg_eq

## Source location

- Original Lean file: `Diamond/PositiveGap/NotTight.lean`
- Declaration name: `sum_sq_sub_avg_eq`
- Declaration kind: `lemma`

## Why this declaration exists

The sum of squared deviations from the average.

 In the file `PositiveGap/NotTight.lean`, it contributes to the finite-dimensional non-tightness argument and the equality-case analysis behind it. Later proofs call this result by name, so documenting it makes the larger argument readable as a mathematical chain rather than as opaque proof script.

## Original code

```lean
/-- The sum of squared deviations from the average. -/
private lemma sum_sq_sub_avg_eq
    {ι : Type u} [Fintype ι] [Nonempty ι] {a : ι → ℝ} :
    let avg : ℝ := (∑ i, a i) / (Fintype.card ι : ℝ)
    ∑ i, (a i - avg) ^ 2 =
      ∑ i, (a i) ^ 2 - (∑ i, a i) ^ 2 / (Fintype.card ι : ℝ) := by
  let avg : ℝ := (∑ i, a i) / (Fintype.card ι : ℝ)
  calc
    ∑ i, (a i - avg) ^ 2 =
        ∑ i, (a i) ^ 2 - 2 * avg * ∑ i, a i + (Fintype.card ι : ℝ) * avg ^ 2 := by
          calc
            ∑ i, (a i - avg) ^ 2 = ∑ i, ((a i) ^ 2 - 2 * a i * avg + avg ^ 2) := by
              refine Finset.sum_congr rfl ?_
              intro i hi
              ring
            _ = ∑ i, (a i) ^ 2 - 2 * avg * ∑ i, a i + (Fintype.card ι : ℝ) * avg ^ 2 := by
              simp [Finset.sum_sub_distrib, Finset.sum_add_distrib, Finset.sum_mul,
                mul_comm, mul_left_comm]
    _ = ∑ i, (a i) ^ 2 - (∑ i, a i) ^ 2 / (Fintype.card ι : ℝ) := by
      simpa using (sum_sq_sub_avg_eq_aux (a := a))
```

## Block-by-block explanation

The explanation below follows the declaration block by block. Each block groups a coherent piece of the definition or proof, so the mathematical structure is easier to see than in a strictly line-oriented reading.

1. Code:
```lean
/-- The sum of squared deviations from the average. -/
```
This is a Lean docstring. It is a human-written comment that tells readers what the declaration is meant to express before the formal code begins.

2. Code:
```lean
private lemma sum_sq_sub_avg_eq
```
This line starts the `sum_sq_sub_avg_eq` declaration. Because it begins with `lemma`, Lean now knows what kind of named object is being introduced.

3. Code:
```lean
    {ι : Type u} [Fintype ι] [Nonempty ι] {a : ι → ℝ} :
```
This line is one local step in the declaration. It either refines the formula being defined or advances the proof by a small algebraic or logical move.  A bracket such as `[Fintype d]` tells Lean that the index set `d` is finite, so sums over all indices make sense.

4. Code:
```lean
    let avg : ℝ := (∑ i, a i) / (Fintype.card ι : ℝ)
```
This line gives a temporary name to an expression. Doing that makes later lines shorter and easier to read.  `Fintype.card` is the size of a finite index set.

5. Code:
```lean
    ∑ i, (a i - avg) ^ 2 =
```
This line is one local step in the declaration. It either refines the formula being defined or advances the proof by a small algebraic or logical move.

6. Code:
```lean
      ∑ i, (a i) ^ 2 - (∑ i, a i) ^ 2 / (Fintype.card ι : ℝ) := by
```
This line says that a proof script begins here. Everything indented underneath is a sequence of instructions that Lean will check step by step.  `Fintype.card` is the size of a finite index set.

7. Code:
```lean
  let avg : ℝ := (∑ i, a i) / (Fintype.card ι : ℝ)
```
This line gives a temporary name to an expression. Doing that makes later lines shorter and easier to read.  `Fintype.card` is the size of a finite index set.

8. Code:
```lean
  calc
```
This line begins a chained calculation. Each displayed step that follows must be justified by the indented proof after `:= by`.

9. Code:
```lean
    ∑ i, (a i - avg) ^ 2 =
```
This line is one local step in the declaration. It either refines the formula being defined or advances the proof by a small algebraic or logical move.

10. Code:
```lean
        ∑ i, (a i) ^ 2 - 2 * avg * ∑ i, a i + (Fintype.card ι : ℝ) * avg ^ 2 := by
```
This line says that a proof script begins here. Everything indented underneath is a sequence of instructions that Lean will check step by step.  `Fintype.card` is the size of a finite index set.

11. Code:
```lean
          calc
```
This line begins a chained calculation. Each displayed step that follows must be justified by the indented proof after `:= by`.

12. Code:
```lean
            ∑ i, (a i - avg) ^ 2 = ∑ i, ((a i) ^ 2 - 2 * a i * avg + avg ^ 2) := by
```
This line says that a proof script begins here. Everything indented underneath is a sequence of instructions that Lean will check step by step.

13. Code:
```lean
              refine Finset.sum_congr rfl ?_
```
This line is a more controlled version of `apply`. It sets up the proof with a partly specified argument and leaves smaller goals to solve next.

14. Code:
```lean
              intro i hi
```
This line introduces the variable or hypothesis named here into the proof context. In ordinary mathematical prose, it is the same as saying “let” or “assume”.

15. Code:
```lean
              ring
```
This line normalizes an algebraic identity in a commutative ring, just as one would expand and collect like terms by hand.

16. Code:
```lean
            _ = ∑ i, (a i) ^ 2 - 2 * avg * ∑ i, a i + (Fintype.card ι : ℝ) * avg ^ 2 := by
```
This line says that a proof script begins here. Everything indented underneath is a sequence of instructions that Lean will check step by step.  `Fintype.card` is the size of a finite index set.

17. Code:
```lean
              simp [Finset.sum_sub_distrib, Finset.sum_add_distrib, Finset.sum_mul,
```
This line simplifies the goal using definitions and known equalities. `simpa` means that, after simplification, the desired statement matches a theorem Lean already has.

18. Code:
```lean
                mul_comm, mul_left_comm]
```
This line is one local step in the declaration. It either refines the formula being defined or advances the proof by a small algebraic or logical move.

19. Code:
```lean
    _ = ∑ i, (a i) ^ 2 - (∑ i, a i) ^ 2 / (Fintype.card ι : ℝ) := by
```
This line says that a proof script begins here. Everything indented underneath is a sequence of instructions that Lean will check step by step.  `Fintype.card` is the size of a finite index set.

20. Code:
```lean
      simpa using (sum_sq_sub_avg_eq_aux (a := a))
```
This line simplifies the goal using definitions and known equalities. `simpa` means that, after simplification, the desired statement matches a theorem Lean already has.

## Mathematical summary

Restated without Lean syntax, `sum_sq_sub_avg_eq` is the theorem or lemma written above.

- State the desired identity or inequality in Lean’s syntax.
- Introduce temporary names and intermediate claims that organize the argument.
- Use rewriting, simplification, and earlier lemmas to reduce the goal to standard matrix or norm manipulations.
- Close the remaining algebraic or order-theoretic steps with Lean’s proof tactics.

## Dependencies and downstream use

### Earlier declarations this depends on
- [`sum_sq_sub_avg_eq_aux`](sum_sq_sub_avg_eq_aux.md) from `PositiveGap/NotTight.lean`

### Later declarations that use this one
- [`all_equal_of_sq_sum_eq_card_mul_sum_sq`](all_equal_of_sq_sum_eq_card_mul_sum_sq.md) in `PositiveGap/NotTight.lean`

## Backlinks

- [Back to `INDEX.md`](../../INDEX.md)
- [Back to the `PositiveGap/NotTight.lean` section in the index](../../INDEX.md#diamond-positivegap-nottight-lean)
- [Previous declaration in this file](sum_sq_sub_avg_eq_aux.md)
- [Next declaration in this file](all_equal_of_sq_sum_eq_card_mul_sum_sq.md)