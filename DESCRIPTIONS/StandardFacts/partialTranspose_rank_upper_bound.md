# partialTranspose_rank_upper_bound

## Source location

- Original Lean file: `Diamond/StandardFacts.lean`
- Declaration name: `partialTranspose_rank_upper_bound`
- Declaration kind: `axiom`

## Why this declaration exists

This axiom packages the Uhlmann/vectorization rank estimate used late in the positive-gap contradiction.

 In the file `StandardFacts.lean`, it contributes to helper facts and background axioms that the paper treats as standard or external input. Later proofs call this result by name, so documenting it makes the larger argument readable as a mathematical chain rather than as opaque proof script.

## Original code

```lean
/-- Background rank bound coming from the Uhlmann/vectorization part of the positive-gap proof. -/
axiom partialTranspose_rank_upper_bound
    {d : Type u} [Fintype d] [DecidableEq d] [Nonempty d]
    {X : Matrix (d × d) (d × d) ℂ} :
    X ≠ 0 →
    Matrix.IsHermitian X →
    Matrix.trace X = 0 →
    partialTraceLeft d d X = 0 →
    X.rank = 2 →
    (partialTransposeMap d d X).rank ≤ Fintype.card (d × d) - Fintype.card d
```

## Line-by-line explanation

The explanation below follows the declaration one physical line at a time. For long proofs, some lines are tiny bookkeeping steps; those are still explained, but briefly.

1. Code:
```lean
/-- Background rank bound coming from the Uhlmann/vectorization part of the positive-gap proof. -/
```
This is a Lean docstring. It is a human-written comment that tells readers what the declaration is meant to express before the formal code begins.

2. Code:
```lean
axiom partialTranspose_rank_upper_bound
```
This line starts the `partialTranspose_rank_upper_bound` declaration. Because it begins with `axiom`, Lean now knows what kind of named object is being introduced.

3. Code:
```lean
    {d : Type u} [Fintype d] [DecidableEq d] [Nonempty d]
```
This line is one local step in the declaration. It either refines the formula being defined or advances the proof by a small algebraic or logical move.  A bracket such as `[Fintype d]` tells Lean that the index set `d` is finite, so sums over all indices make sense.  A bracket such as `[DecidableEq d]` tells Lean that it can decide whether two indices are equal.

4. Code:
```lean
    {X : Matrix (d × d) (d × d) ℂ} :
```
This line is one local step in the declaration. It either refines the formula being defined or advances the proof by a small algebraic or logical move.  `Matrix d d ℂ` means a square matrix with complex entries; the index type `d` tells Lean which rows and columns exist.

5. Code:
```lean
    X ≠ 0 →
```
This line is one local step in the declaration. It either refines the formula being defined or advances the proof by a small algebraic or logical move.

6. Code:
```lean
    Matrix.IsHermitian X →
```
This line is one local step in the declaration. It either refines the formula being defined or advances the proof by a small algebraic or logical move.

7. Code:
```lean
    Matrix.trace X = 0 →
```
This line is one local step in the declaration. It either refines the formula being defined or advances the proof by a small algebraic or logical move.

8. Code:
```lean
    partialTraceLeft d d X = 0 →
```
This line is one local step in the declaration. It either refines the formula being defined or advances the proof by a small algebraic or logical move.

9. Code:
```lean
    X.rank = 2 →
```
This line is one local step in the declaration. It either refines the formula being defined or advances the proof by a small algebraic or logical move.

10. Code:
```lean
    (partialTransposeMap d d X).rank ≤ Fintype.card (d × d) - Fintype.card d
```
This line is one local step in the declaration. It either refines the formula being defined or advances the proof by a small algebraic or logical move.  `Fintype.card` is the size of a finite index set.

## Mathematical summary

Restated without Lean syntax, `partialTranspose_rank_upper_bound` is the theorem or lemma written above.

- State the desired identity or inequality in Lean’s syntax.
- Introduce temporary names and intermediate claims that organize the argument.
- Use rewriting, simplification, and earlier lemmas to reduce the goal to standard matrix or norm manipulations.
- Close the remaining algebraic or order-theoretic steps with Lean’s proof tactics.

## Dependencies and downstream use

### Earlier declarations this depends on
- [`partialTransposeMap`](../Setups/partialTransposeMap.md) from `Setups.lean`
- [`partialTraceLeft`](../Setups/partialTraceLeft.md) from `Setups.lean`

### Later declarations that use this one
- [`theorem_not_tight`](../PositiveGap/NotTight/theorem_not_tight.md) in `PositiveGap/NotTight.lean`

## Backlinks

- [Back to `INDEX.md`](../INDEX.md)
- [Back to the `StandardFacts.lean` section in the index](../INDEX.md#diamond-standardfacts-lean)
- [Previous declaration in this file](exists_maximizing_state.md)
- [Next declaration in this file](asymptotic_cotangent_lower_bound.md)