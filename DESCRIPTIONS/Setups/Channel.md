# Channel

## Source location

- Original Lean file: `Diamond/Setups.lean`
- Declaration name: `Channel`
- Declaration kind: `abbrev`

## Why this declaration exists

This abbreviation says that a channel is represented as a complex-linear map from operators to operators. It packages “a map acting on matrices” into one reusable Lean name.

 In the file `Setups.lean`, it contributes to foundational objects and notational definitions for operators, channels, norms, and the maps studied in the paper. Later declarations use this name instead of repeatedly expanding the underlying matrix formula.

## Original code

```lean
abbrev Channel (d : Type u) [Fintype d] [DecidableEq d] :=
  Operator d →ₗ[ℂ] Operator d
```

## Block-by-block explanation

The explanation below follows the declaration block by block. Each block groups a coherent piece of the definition or proof, so the mathematical structure is easier to see than in a strictly line-oriented reading.

1. Code:
```lean
abbrev Channel (d : Type u) [Fintype d] [DecidableEq d] :=
```
This line starts the `Channel` declaration. Because it begins with `abbrev`, Lean now knows what kind of named object is being introduced. The bracketed assumptions tell Lean that the relevant index sets are finite and that equality of indices can be checked mechanically. The type information on this line explains what sort of mathematical object the declaration talks about.  `Channel d` is an abbreviation for a complex-linear map from operators on `d` to operators on `d`.  A bracket such as `[Fintype d]` tells Lean that the index set `d` is finite, so sums over all indices make sense.  A bracket such as `[DecidableEq d]` tells Lean that it can decide whether two indices are equal.

2. Code:
```lean
  Operator d →ₗ[ℂ] Operator d
```
This line is one local step in the declaration. It either refines the formula being defined or advances the proof by a small algebraic or logical move.  The arrow `→ₗ[ℂ]` means “complex-linear map”.

## Mathematical summary

In ordinary mathematical language, `Channel` is the project's formal Lean name for the object introduced in this declaration.

## Dependencies and downstream use

### Earlier declarations this depends on
- [`Operator`](Operator.md) from `Setups.lean`

### Later declarations that use this one
- [`IsHermiticityPreserving`](IsHermiticityPreserving.md) in `Setups.lean`
- [`IsQuantumChannel`](IsQuantumChannel.md) in `Setups.lean`
- [`IsTraceAnnihilating`](IsTraceAnnihilating.md) in `Setups.lean`
- [`transposeMap`](transposeMap.md) in `Setups.lean`
- [`tensorWithIdentity`](tensorWithIdentity.md) in `Setups.lean`
- [`partialTransposeMap`](partialTransposeMap.md) in `Setups.lean`
- [`diamondNorm`](diamondNorm.md) in `Setups.lean`
- [`diamondNormAt`](diamondNormAt.md) in `Setups.lean`
- [`diamondOp`](diamondOp.md) in `Setups.lean`
- [`idMinus`](idMinus.md) in `Setups.lean`
- [`adMap`](adMap.md) in `Setups.lean`
- [`Lambda`](Lambda.md) in `Setups.lean`
- [`quantumChannel_has_kraus`](../StandardFacts/quantumChannel_has_kraus.md) in `StandardFacts.lean`
- [`tensorWithIdentity_comp_transpose`](../StandardFacts/tensorWithIdentity_comp_transpose.md) in `StandardFacts.lean`
- [`idMinus_isHermiticityPreserving`](../StandardFacts/idMinus_isHermiticityPreserving.md) in `StandardFacts.lean`
- [`idMinus_isTraceAnnihilating`](../StandardFacts/idMinus_isTraceAnnihilating.md) in `StandardFacts.lean`
- [`diamond_le_of_pointwise`](../StandardFacts/diamond_le_of_pointwise.md) in `StandardFacts.lean`
- [`traceNorm_apply_le_diamond`](../StandardFacts/traceNorm_apply_le_diamond.md) in `StandardFacts.lean`
- [`exists_maximizing_state`](../StandardFacts/exists_maximizing_state.md) in `StandardFacts.lean`
- [`partialTraceLeft_tensor_zero`](../StandardFacts/partialTraceLeft_tensor_zero.md) in `StandardFacts.lean`
- [`tensorWithIdentity_trace_zero`](../StandardFacts/tensorWithIdentity_trace_zero.md) in `StandardFacts.lean`
- [`tensorWithIdentity_hermitian`](../StandardFacts/tensorWithIdentity_hermitian.md) in `StandardFacts.lean`
- [`theorem1`](../Theorem/Theorem1/theorem1.md) in `Theorem/Theorem1.lean`
- [`remark1`](../Theorem/Remark1/remark1.md) in `Theorem/Remark1.lean`
- [`lemma4`](../PositiveGap/Lemma4/lemma4.md) in `PositiveGap/Lemma4.lean`
- [`corollary1`](../PositiveGap/Corollary1/corollary1.md) in `PositiveGap/Corollary1.lean`
- [`theorem_not_tight`](../PositiveGap/NotTight/theorem_not_tight.md) in `PositiveGap/NotTight.lean`
- [`effectiveChannel`](../EndMatter/Corollary2/effectiveChannel.md) in `EndMatter/Corollary2.lean`
- [`corollary2_linear_bound`](../EndMatter/Corollary2/corollary2_linear_bound.md) in `EndMatter/Corollary2.lean`
- [`corollary2`](../EndMatter/Corollary2/corollary2.md) in `EndMatter/Corollary2.lean`

## Backlinks

- [Back to `INDEX.md`](../INDEX.md)
- [Back to the `Setups.lean` section in the index](../INDEX.md#diamond-setups-lean)
- [Previous declaration in this file](Operator.md)
- [Next declaration in this file](hsNorm.md)