# diamondOp

## Source location

- Original Lean file: `Diamond/Setups.lean`
- Declaration name: `diamondOp`
- Declaration kind: `abbrev`

## Why this declaration exists

This abbreviation is the same-size stabilization used throughout the project as the working diamond norm.

 In the file `Setups.lean`, it contributes to foundational objects and notational definitions for operators, channels, norms, and the maps studied in the paper. Later declarations use this name instead of repeatedly expanding the underlying matrix formula.

## Original code

```lean
/-- Same-size stabilization.
It agrees with the full diamond norm by the standard restriction to `k = d`. -/
abbrev diamondOp
    {d : Type u} [Fintype d] [DecidableEq d] (Φ : Channel d) : ℝ :=
  diamondNormAt (d := d) (k := d) Φ
```

## Block-by-block explanation

The explanation below follows the declaration block by block. Each block groups a coherent piece of the definition or proof, so the mathematical structure is easier to see than in a strictly line-oriented reading.

1. Code:
```lean
/-- Same-size stabilization.
```
This is a Lean docstring. It is a human-written comment that tells readers what the declaration is meant to express before the formal code begins.

2. Code:
```lean
It agrees with the full diamond norm by the standard restriction to `k = d`. -/
```
This line is one local step in the declaration. It either refines the formula being defined or advances the proof by a small algebraic or logical move.

3. Code:
```lean
abbrev diamondOp
```
This line starts the `diamondOp` declaration. Because it begins with `abbrev`, Lean now knows what kind of named object is being introduced.

4. Code:
```lean
    {d : Type u} [Fintype d] [DecidableEq d] (Φ : Channel d) : ℝ :=
```
This line is one local step in the declaration. It either refines the formula being defined or advances the proof by a small algebraic or logical move.  `Channel d` is an abbreviation for a complex-linear map from operators on `d` to operators on `d`.  A bracket such as `[Fintype d]` tells Lean that the index set `d` is finite, so sums over all indices make sense.  A bracket such as `[DecidableEq d]` tells Lean that it can decide whether two indices are equal.

5. Code:
```lean
  diamondNormAt (d := d) (k := d) Φ
```
This line is one local step in the declaration. It either refines the formula being defined or advances the proof by a small algebraic or logical move.

## Mathematical summary

In ordinary mathematical language, `diamondOp` is the project's formal Lean name for the object introduced in this declaration.

## Dependencies and downstream use

### Earlier declarations this depends on
- [`Channel`](Channel.md) from `Setups.lean`
- [`diamondNormAt`](diamondNormAt.md) from `Setups.lean`

### Later declarations that use this one
- [`diamond_le_of_pointwise`](../StandardFacts/diamond_le_of_pointwise.md) in `StandardFacts.lean`
- [`lemma_transpose_diamond`](../StandardFacts/lemma_transpose_diamond.md) in `StandardFacts.lean`
- [`unitary_channel_diamond_distance_eq_two_of_trace_zero`](../StandardFacts/unitary_channel_diamond_distance_eq_two_of_trace_zero.md) in `StandardFacts.lean`
- [`exists_maximizing_state`](../StandardFacts/exists_maximizing_state.md) in `StandardFacts.lean`
- [`theorem1`](../Theorem/Theorem1/theorem1.md) in `Theorem/Theorem1.lean`
- [`remark1`](../Theorem/Remark1/remark1.md) in `Theorem/Remark1.lean`
- [`theorem_not_tight`](../PositiveGap/NotTight/theorem_not_tight.md) in `PositiveGap/NotTight.lean`
- [`theorem_eq7_witness_bound`](../EndMatter/Eq7/theorem_eq7_witness_bound.md) in `EndMatter/Eq7.lean`
- [`theorem_eq7_witness_bound_explicit`](../EndMatter/Eq7/theorem_eq7_witness_bound_explicit.md) in `EndMatter/Eq7.lean`
- [`theorem_eq7`](../EndMatter/Eq7/theorem_eq7.md) in `EndMatter/Eq7.lean`
- [`theorem_eq8`](../EndMatter/Eq8/theorem_eq8.md) in `EndMatter/Eq8.lean`
- [`alpha_lower_bound`](../EndMatter/Eq8/alpha_lower_bound.md) in `EndMatter/Eq8.lean`
- [`corollary2_linear_bound`](../EndMatter/Corollary2/corollary2_linear_bound.md) in `EndMatter/Corollary2.lean`
- [`corollary2`](../EndMatter/Corollary2/corollary2.md) in `EndMatter/Corollary2.lean`

## Backlinks

- [Back to `INDEX.md`](../INDEX.md)
- [Back to the `Setups.lean` section in the index](../INDEX.md#diamond-setups-lean)
- [Previous declaration in this file](diamondNormAt.md)
- [Next declaration in this file](partialTraceLeft.md)