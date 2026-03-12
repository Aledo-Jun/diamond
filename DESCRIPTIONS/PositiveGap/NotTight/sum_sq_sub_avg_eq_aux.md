# sum_sq_sub_avg_eq_aux

## Source location

- Original Lean file: `Diamond/PositiveGap/NotTight.lean`
- Declaration name: `sum_sq_sub_avg_eq_aux`
- Declaration kind: `lemma`

## Why this declaration exists

Algebraic variance identity for finite real families.

 In the file `PositiveGap/NotTight.lean`, it contributes to the finite-dimensional non-tightness argument and the equality-case analysis behind it. Later proofs call this result by name, so documenting it makes the larger argument readable as a mathematical chain rather than as opaque proof script.

## Original code

```lean
/-- Algebraic variance identity for finite real families. -/
private lemma sum_sq_sub_avg_eq_aux
    {ι : Type u} [Fintype ι] [Nonempty ι] {a : ι → ℝ} :
    let avg : ℝ := (∑ i, a i) / (Fintype.card ι : ℝ)
    ∑ i, (a i) ^ 2 - 2 * avg * ∑ i, a i + (Fintype.card ι : ℝ) * avg ^ 2 =
      ∑ i, (a i) ^ 2 - (∑ i, a i) ^ 2 / (Fintype.card ι : ℝ) := by
  let avg : ℝ := (∑ i, a i) / (Fintype.card ι : ℝ)
  have hcard_ne : (Fintype.card ι : ℝ) ≠ 0 := by
    positivity
  field_simp [avg, hcard_ne]
  ring
```

## Line-by-line explanation

The explanation below follows the declaration one physical line at a time. For long proofs, some lines are tiny bookkeeping steps; those are still explained, but briefly.

1. Code:
```lean
/-- Algebraic variance identity for finite real families. -/
```
This is a Lean docstring. It is a human-written comment that tells readers what the declaration is meant to express before the formal code begins.

2. Code:
```lean
private lemma sum_sq_sub_avg_eq_aux
```
This line starts the `sum_sq_sub_avg_eq_aux` declaration. Because it begins with `lemma`, Lean now knows what kind of named object is being introduced.

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
    ∑ i, (a i) ^ 2 - 2 * avg * ∑ i, a i + (Fintype.card ι : ℝ) * avg ^ 2 =
```
This line is one local step in the declaration. It either refines the formula being defined or advances the proof by a small algebraic or logical move.  `Fintype.card` is the size of a finite index set.

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
  have hcard_ne : (Fintype.card ι : ℝ) ≠ 0 := by
```
This line says that a proof script begins here. Everything indented underneath is a sequence of instructions that Lean will check step by step.  `Fintype.card` is the size of a finite index set.

9. Code:
```lean
    positivity
```
This line asks Lean to prove that the displayed quantity is positive or nonnegative using standard positivity rules.

10. Code:
```lean
  field_simp [avg, hcard_ne]
```
This line is one local step in the declaration. It either refines the formula being defined or advances the proof by a small algebraic or logical move.

11. Code:
```lean
  ring
```
This line normalizes an algebraic identity in a commutative ring, just as one would expand and collect like terms by hand.

## Mathematical summary

Restated without Lean syntax, `sum_sq_sub_avg_eq_aux` is the theorem or lemma written above.

- State the desired identity or inequality in Lean’s syntax.
- Introduce temporary names and intermediate claims that organize the argument.
- Use rewriting, simplification, and earlier lemmas to reduce the goal to standard matrix or norm manipulations.
- Close the remaining algebraic or order-theoretic steps with Lean’s proof tactics.

## Dependencies and downstream use

### Earlier declarations this depends on
- This declaration does not explicitly cite an earlier named declaration from the documented tree; it mostly uses Lean primitives or local algebraic steps.

### Later declarations that use this one
- [`sum_sq_sub_avg_eq`](sum_sq_sub_avg_eq.md) in `PositiveGap/NotTight.lean`

## Backlinks

- [Back to `INDEX.md`](../../INDEX.md)
- [Back to the `PositiveGap/NotTight.lean` section in the index](../../INDEX.md#diamond-positivegap-nottight-lean)
- [Previous declaration in this file](existsUnique_nonzero_of_pairwise_zero.md)
- [Next declaration in this file](sum_sq_sub_avg_eq.md)