# sqrt_card_prod_self

## Source location

- Original Lean file: `Diamond/StandardFacts.lean`
- Declaration name: `sqrt_card_prod_self`
- Declaration kind: `theorem`

## Why this declaration exists

Card-product square-root identity used for dimension reduction.

 In the file `StandardFacts.lean`, it contributes to helper facts and background axioms that the paper treats as standard or external input. Later proofs call this result by name, so documenting it makes the larger argument readable as a mathematical chain rather than as opaque proof script.

## Original code

```lean
/-- Card-product square-root identity used for dimension reduction. -/
theorem sqrt_card_prod_self
    {d k : Type u} [Fintype d] [Fintype k] :
    Real.sqrt (Fintype.card (d × k) : ℝ) =
      Real.sqrt (Fintype.card d : ℝ) * Real.sqrt (Fintype.card k : ℝ) := by
  rw [Fintype.card_prod]
  rw [Nat.cast_mul]
  rw [Real.sqrt_mul (show (0 : ℝ) ≤ Fintype.card d by positivity)]
  -- no further simplification needed
```

## Line-by-line explanation

The explanation below follows the declaration one physical line at a time. For long proofs, some lines are tiny bookkeeping steps; those are still explained, but briefly.

1. Code:
```lean
/-- Card-product square-root identity used for dimension reduction. -/
```
This is a Lean docstring. It is a human-written comment that tells readers what the declaration is meant to express before the formal code begins.

2. Code:
```lean
theorem sqrt_card_prod_self
```
This line starts the `sqrt_card_prod_self` declaration. Because it begins with `theorem`, Lean now knows what kind of named object is being introduced.

3. Code:
```lean
    {d k : Type u} [Fintype d] [Fintype k] :
```
This line is one local step in the declaration. It either refines the formula being defined or advances the proof by a small algebraic or logical move.  A bracket such as `[Fintype d]` tells Lean that the index set `d` is finite, so sums over all indices make sense.

4. Code:
```lean
    Real.sqrt (Fintype.card (d × k) : ℝ) =
```
This line is one local step in the declaration. It either refines the formula being defined or advances the proof by a small algebraic or logical move.  `Fintype.card` is the size of a finite index set.

5. Code:
```lean
      Real.sqrt (Fintype.card d : ℝ) * Real.sqrt (Fintype.card k : ℝ) := by
```
This line says that a proof script begins here. Everything indented underneath is a sequence of instructions that Lean will check step by step.  `Fintype.card` is the size of a finite index set.

6. Code:
```lean
  rw [Fintype.card_prod]
```
This line uses rewriting. Lean replaces one expression by an equal expression using the lemmas listed in brackets.  A bracket such as `[Fintype d]` tells Lean that the index set `d` is finite, so sums over all indices make sense.  `Fintype.card` is the size of a finite index set.

7. Code:
```lean
  rw [Nat.cast_mul]
```
This line uses rewriting. Lean replaces one expression by an equal expression using the lemmas listed in brackets.

8. Code:
```lean
  rw [Real.sqrt_mul (show (0 : ℝ) ≤ Fintype.card d by positivity)]
```
This line uses rewriting. Lean replaces one expression by an equal expression using the lemmas listed in brackets.  `Fintype.card` is the size of a finite index set.

9. Code:
```lean
  -- no further simplification needed
```
This line is one local step in the declaration. It either refines the formula being defined or advances the proof by a small algebraic or logical move.

## Mathematical summary

Restated without Lean syntax, `sqrt_card_prod_self` is the theorem or lemma written above.

- State the desired identity or inequality in Lean’s syntax.
- Introduce temporary names and intermediate claims that organize the argument.
- Use rewriting, simplification, and earlier lemmas to reduce the goal to standard matrix or norm manipulations.
- Close the remaining algebraic or order-theoretic steps with Lean’s proof tactics.

## Dependencies and downstream use

### Earlier declarations this depends on
- This declaration does not explicitly cite an earlier named declaration from the documented tree; it mostly uses Lean primitives or local algebraic steps.

### Later declarations that use this one
- No later documented declaration mentions this name explicitly.

## Backlinks

- [Back to `INDEX.md`](../INDEX.md)
- [Back to the `StandardFacts.lean` section in the index](../INDEX.md#diamond-standardfacts-lean)
- [Previous declaration in this file](tensorWithIdentity_hermitian.md)