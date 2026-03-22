# IsQuantumChannel

## Source location

- Original Lean file: `Diamond/Setups.lean`
- Declaration name: `IsQuantumChannel`
- Declaration kind: `structure`

## Why this declaration exists

This structure records exactly the channel properties the later proofs need: trace preservation and Hermiticity preservation.

 In the file `Setups.lean`, it contributes to foundational objects and notational definitions for operators, channels, norms, and the maps studied in the paper. Later declarations use this name instead of repeatedly expanding the underlying matrix formula.

## Original code

```lean
structure IsQuantumChannel
    {d : Type u} [Fintype d] [DecidableEq d] (T : Channel d) where
  trace_preserving : ∀ X, Matrix.trace (T X) = Matrix.trace X
  hermiticity_preserving : IsHermiticityPreserving T
```

## Block-by-block explanation

The explanation below follows the declaration block by block. Each block groups a coherent piece of the definition or proof, so the mathematical structure is easier to see than in a strictly line-oriented reading.

1. Code:
```lean
structure IsQuantumChannel
```
This line starts the `IsQuantumChannel` declaration. Because it begins with `structure`, Lean now knows what kind of named object is being introduced.

2. Code:
```lean
    {d : Type u} [Fintype d] [DecidableEq d] (T : Channel d) where
```
This line starts a `where` block. In Lean, a `where` block lists the fields of a structure or bundled map.

3. Code:
```lean
  trace_preserving : ∀ X, Matrix.trace (T X) = Matrix.trace X
```
This line is one local step in the declaration. It either refines the formula being defined or advances the proof by a small algebraic or logical move.

4. Code:
```lean
  hermiticity_preserving : IsHermiticityPreserving T
```
This line is one local step in the declaration. It either refines the formula being defined or advances the proof by a small algebraic or logical move.

## Mathematical summary

In ordinary mathematical language, `IsQuantumChannel` is the project's formal Lean name for the object introduced in this declaration. A `structure` is Lean's way of bundling several named fields together, so one should think of it as a small record of data and properties.

## Dependencies and downstream use

### Earlier declarations this depends on
- [`Channel`](Channel.md) from `Setups.lean`
- [`IsHermiticityPreserving`](IsHermiticityPreserving.md) from `Setups.lean`

### Later declarations that use this one
- [`quantumChannel_has_kraus`](../StandardFacts/quantumChannel_has_kraus.md) in `StandardFacts.lean`
- [`idMinus_isHermiticityPreserving`](../StandardFacts/idMinus_isHermiticityPreserving.md) in `StandardFacts.lean`
- [`idMinus_isTraceAnnihilating`](../StandardFacts/idMinus_isTraceAnnihilating.md) in `StandardFacts.lean`
- [`adMap_isQuantumChannel`](../StandardFacts/adMap_isQuantumChannel.md) in `StandardFacts.lean`
- [`exists_maximizing_state`](../StandardFacts/exists_maximizing_state.md) in `StandardFacts.lean`
- [`theorem1`](../Theorem/Theorem1/theorem1.md) in `Theorem/Theorem1.lean`
- [`lemma4`](../PositiveGap/Lemma4/lemma4.md) in `PositiveGap/Lemma4.lean`
- [`corollary1`](../PositiveGap/Corollary1/corollary1.md) in `PositiveGap/Corollary1.lean`
- [`theorem_not_tight`](../PositiveGap/NotTight/theorem_not_tight.md) in `PositiveGap/NotTight.lean`
- [`alpha_lower_bound`](../EndMatter/Eq8/alpha_lower_bound.md) in `EndMatter/Eq8.lean`
- [`corollary2_linear_bound`](../EndMatter/Corollary2/corollary2_linear_bound.md) in `EndMatter/Corollary2.lean`
- [`corollary2`](../EndMatter/Corollary2/corollary2.md) in `EndMatter/Corollary2.lean`

## Backlinks

- [Back to `INDEX.md`](../INDEX.md)
- [Back to the `Setups.lean` section in the index](../INDEX.md#diamond-setups-lean)
- [Previous declaration in this file](IsHermiticityPreserving.md)
- [Next declaration in this file](IsTraceAnnihilating.md)