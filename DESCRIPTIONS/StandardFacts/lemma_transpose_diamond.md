# lemma_transpose_diamond

## Source location

- Original Lean file: `Diamond/StandardFacts.lean`
- Declaration name: `lemma_transpose_diamond`
- Declaration kind: `axiom`

## Why this declaration exists

This axiom records the known value of the transpose map's diamond norm.

 In the file `StandardFacts.lean`, it contributes to helper facts and background axioms that the paper treats as standard or external input. Later proofs call this result by name, so documenting it makes the larger argument readable as a mathematical chain rather than as opaque proof script.

## Original code

```lean
axiom lemma_transpose_diamond
    {d : Type u} [Fintype d] [DecidableEq d] [Nonempty d] :
    diamondOp (transposeMap d) = Real.sqrt (Fintype.card (d × d) : ℝ)
```

## Line-by-line explanation

The explanation below follows the declaration one physical line at a time. For long proofs, some lines are tiny bookkeeping steps; those are still explained, but briefly.

1. Code:
```lean
axiom lemma_transpose_diamond
```
This line starts the `lemma_transpose_diamond` declaration. Because it begins with `axiom`, Lean now knows what kind of named object is being introduced.

2. Code:
```lean
    {d : Type u} [Fintype d] [DecidableEq d] [Nonempty d] :
```
This line is one local step in the declaration. It either refines the formula being defined or advances the proof by a small algebraic or logical move.  A bracket such as `[Fintype d]` tells Lean that the index set `d` is finite, so sums over all indices make sense.  A bracket such as `[DecidableEq d]` tells Lean that it can decide whether two indices are equal.

3. Code:
```lean
    diamondOp (transposeMap d) = Real.sqrt (Fintype.card (d × d) : ℝ)
```
This line is one local step in the declaration. It either refines the formula being defined or advances the proof by a small algebraic or logical move.  `Fintype.card` is the size of a finite index set.

## Mathematical summary

Restated without Lean syntax, `lemma_transpose_diamond` is the theorem or lemma written above.

- State the desired identity or inequality in Lean’s syntax.
- Introduce temporary names and intermediate claims that organize the argument.
- Use rewriting, simplification, and earlier lemmas to reduce the goal to standard matrix or norm manipulations.
- Close the remaining algebraic or order-theoretic steps with Lean’s proof tactics.

## Dependencies and downstream use

### Earlier declarations this depends on
- [`transposeMap`](../Setups/transposeMap.md) from `Setups.lean`
- [`diamondOp`](../Setups/diamondOp.md) from `Setups.lean`

### Later declarations that use this one
- [`theorem1`](../Theorem/Theorem1/theorem1.md) in `Theorem/Theorem1.lean`
- [`remark1`](../Theorem/Remark1/remark1.md) in `Theorem/Remark1.lean`
- [`theorem_not_tight`](../PositiveGap/NotTight/theorem_not_tight.md) in `PositiveGap/NotTight.lean`
- [`alpha_lower_bound`](../EndMatter/Eq8/alpha_lower_bound.md) in `EndMatter/Eq8.lean`
- [`corollary2_linear_bound`](../EndMatter/Corollary2/corollary2_linear_bound.md) in `EndMatter/Corollary2.lean`

## Backlinks

- [Back to `INDEX.md`](../INDEX.md)
- [Back to the `StandardFacts.lean` section in the index](../INDEX.md#diamond-standardfacts-lean)
- [Previous declaration in this file](traceNorm_apply_le_diamond.md)
- [Next declaration in this file](unitary_channel_diamond_distance_eq_two_of_trace_zero.md)