# traceNorm_apply_le_diamond

## Source location

- Original Lean file: `Diamond/StandardFacts.lean`
- Declaration name: `traceNorm_apply_le_diamond`
- Declaration kind: `axiom`

## Why this declaration exists

This axiom is the obvious “a single test state gives a lower witness for the supremum” fact for the diamond norm.

 In the file `StandardFacts.lean`, it contributes to helper facts and background axioms that the paper treats as standard or external input. Later proofs call this result by name, so documenting it makes the larger argument readable as a mathematical chain rather than as opaque proof script.

## Original code

```lean
axiom traceNorm_apply_le_diamond
    {d : Type u} [Fintype d] [DecidableEq d] {k : Type u}
    [Fintype k] [DecidableEq k]
    (Φ : Channel d) (ρ : DensityState (d × k)) :
    traceNormOp (tensorWithIdentity d k Φ ρ.1) ≤ diamondNormAt (d := d) (k := k) Φ

/-- Transposition norm identity `‖Θ‖⋄ = √(d²) = d`. -/
-- Background theorem about the transposition channel norm.
```

## Line-by-line explanation

The explanation below follows the declaration one physical line at a time. For long proofs, some lines are tiny bookkeeping steps; those are still explained, but briefly.

1. Code:
```lean
axiom traceNorm_apply_le_diamond
```
This line starts the `traceNorm_apply_le_diamond` declaration. Because it begins with `axiom`, Lean now knows what kind of named object is being introduced.

2. Code:
```lean
    {d : Type u} [Fintype d] [DecidableEq d] {k : Type u}
```
This line is one local step in the declaration. It either refines the formula being defined or advances the proof by a small algebraic or logical move.  A bracket such as `[Fintype d]` tells Lean that the index set `d` is finite, so sums over all indices make sense.  A bracket such as `[DecidableEq d]` tells Lean that it can decide whether two indices are equal.

3. Code:
```lean
    [Fintype k] [DecidableEq k]
```
This line is one local step in the declaration. It either refines the formula being defined or advances the proof by a small algebraic or logical move.  A bracket such as `[Fintype d]` tells Lean that the index set `d` is finite, so sums over all indices make sense.  A bracket such as `[DecidableEq d]` tells Lean that it can decide whether two indices are equal.

4. Code:
```lean
    (Φ : Channel d) (ρ : DensityState (d × k)) :
```
This line is one local step in the declaration. It either refines the formula being defined or advances the proof by a small algebraic or logical move.  `Channel d` is an abbreviation for a complex-linear map from operators on `d` to operators on `d`.

5. Code:
```lean
    traceNormOp (tensorWithIdentity d k Φ ρ.1) ≤ diamondNormAt (d := d) (k := k) Φ
```
This line is one local step in the declaration. It either refines the formula being defined or advances the proof by a small algebraic or logical move.

6. Code:
```lean
/-- Transposition norm identity `‖Θ‖⋄ = √(d²) = d`. -/
```
This is a Lean docstring. It is a human-written comment that tells readers what the declaration is meant to express before the formal code begins.

7. Code:
```lean
-- Background theorem about the transposition channel norm.
```
This line is one local step in the declaration. It either refines the formula being defined or advances the proof by a small algebraic or logical move.

## Mathematical summary

Restated without Lean syntax, `traceNorm_apply_le_diamond` is the theorem or lemma written above.

- State the desired identity or inequality in Lean’s syntax.
- Introduce temporary names and intermediate claims that organize the argument.
- Use rewriting, simplification, and earlier lemmas to reduce the goal to standard matrix or norm manipulations.
- Close the remaining algebraic or order-theoretic steps with Lean’s proof tactics.

## Dependencies and downstream use

### Earlier declarations this depends on
- [`Channel`](../Setups/Channel.md) from `Setups.lean`
- [`traceNormOp`](../Setups/traceNormOp.md) from `Setups.lean`
- [`DensityState`](../Setups/DensityState.md) from `Setups.lean`
- [`tensorWithIdentity`](../Setups/tensorWithIdentity.md) from `Setups.lean`
- [`diamondNormAt`](../Setups/diamondNormAt.md) from `Setups.lean`

### Later declarations that use this one
- [`theorem1`](../Theorem/Theorem1/theorem1.md) in `Theorem/Theorem1.lean`
- [`remark1`](../Theorem/Remark1/remark1.md) in `Theorem/Remark1.lean`
- [`theorem_not_tight`](../PositiveGap/NotTight/theorem_not_tight.md) in `PositiveGap/NotTight.lean`
- [`theorem_eq7_witness_bound`](../EndMatter/Eq7/theorem_eq7_witness_bound.md) in `EndMatter/Eq7.lean`

## Backlinks

- [Back to `INDEX.md`](../INDEX.md)
- [Back to the `StandardFacts.lean` section in the index](../INDEX.md#diamond-standardfacts-lean)
- [Previous declaration in this file](diamond_le_of_pointwise_nonempty.md)
- [Next declaration in this file](lemma_transpose_diamond.md)
