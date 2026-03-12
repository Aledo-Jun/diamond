# diamond_le_of_pointwise

## Source location

- Original Lean file: `Diamond/StandardFacts.lean`
- Declaration name: `diamond_le_of_pointwise`
- Declaration kind: `axiom`

## Why this declaration exists

This axiom lets later proofs turn a uniform pointwise estimate on states into a diamond-norm estimate.

 In the file `StandardFacts.lean`, it contributes to helper facts and background axioms that the paper treats as standard or external input. Later proofs call this result by name, so documenting it makes the larger argument readable as a mathematical chain rather than as opaque proof script.

## Original code

```lean
axiom diamond_le_of_pointwise
    {d : Type u} [Fintype d] [DecidableEq d]
    (Φ : Channel d) (b : ℝ)
    (hbound : ∀ ρ : DensityState (d × d),
      traceNormOp (tensorWithIdentity d d Φ ρ.1) ≤ b) :
    diamondOp Φ ≤ b

/-- Concrete witness bound for the diamond norm defined in `Setups`. -/
-- Immediate from the definition of `diamondNormAt`; kept as an explicit axiom in this split
-- to avoid introducing an auxiliary compactness/attainment argument at this layer.
```

## Line-by-line explanation

The explanation below follows the declaration one physical line at a time. For long proofs, some lines are tiny bookkeeping steps; those are still explained, but briefly.

1. Code:
```lean
axiom diamond_le_of_pointwise
```
This line starts the `diamond_le_of_pointwise` declaration. Because it begins with `axiom`, Lean now knows what kind of named object is being introduced.

2. Code:
```lean
    {d : Type u} [Fintype d] [DecidableEq d]
```
This line is one local step in the declaration. It either refines the formula being defined or advances the proof by a small algebraic or logical move.  A bracket such as `[Fintype d]` tells Lean that the index set `d` is finite, so sums over all indices make sense.  A bracket such as `[DecidableEq d]` tells Lean that it can decide whether two indices are equal.

3. Code:
```lean
    (Φ : Channel d) (b : ℝ)
```
This line is one local step in the declaration. It either refines the formula being defined or advances the proof by a small algebraic or logical move.  `Channel d` is an abbreviation for a complex-linear map from operators on `d` to operators on `d`.

4. Code:
```lean
    (hbound : ∀ ρ : DensityState (d × d),
```
This line is one local step in the declaration. It either refines the formula being defined or advances the proof by a small algebraic or logical move.

5. Code:
```lean
      traceNormOp (tensorWithIdentity d d Φ ρ.1) ≤ b) :
```
This line is one local step in the declaration. It either refines the formula being defined or advances the proof by a small algebraic or logical move.

6. Code:
```lean
    diamondOp Φ ≤ b
```
This line is one local step in the declaration. It either refines the formula being defined or advances the proof by a small algebraic or logical move.

7. Code:
```lean
/-- Concrete witness bound for the diamond norm defined in `Setups`. -/
```
This is a Lean docstring. It is a human-written comment that tells readers what the declaration is meant to express before the formal code begins.

8. Code:
```lean
-- Immediate from the definition of `diamondNormAt`; kept as an explicit axiom in this split
```
This line is one local step in the declaration. It either refines the formula being defined or advances the proof by a small algebraic or logical move.

9. Code:
```lean
-- to avoid introducing an auxiliary compactness/attainment argument at this layer.
```
This line is one local step in the declaration. It either refines the formula being defined or advances the proof by a small algebraic or logical move.

## Mathematical summary

Restated without Lean syntax, `diamond_le_of_pointwise` is the theorem or lemma written above.

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
- [`diamondOp`](../Setups/diamondOp.md) from `Setups.lean`

### Later declarations that use this one
- [`theorem1`](../Theorem/Theorem1/theorem1.md) in `Theorem/Theorem1.lean`
- [`remark1`](../Theorem/Remark1/remark1.md) in `Theorem/Remark1.lean`

## Backlinks

- [Back to `INDEX.md`](../INDEX.md)
- [Back to the `StandardFacts.lean` section in the index](../INDEX.md#diamond-standardfacts-lean)
- [Previous declaration in this file](adMap_isQuantumChannel.md)
- [Next declaration in this file](traceNorm_apply_le_diamond.md)