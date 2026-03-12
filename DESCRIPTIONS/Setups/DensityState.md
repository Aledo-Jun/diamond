# DensityState

## Source location

- Original Lean file: `Diamond/Setups.lean`
- Declaration name: `DensityState`
- Declaration kind: `abbrev`

## Why this declaration exists

This abbreviation packages a matrix together with a proof that it is a density state. Lean uses this bundled form whenever later results want both the matrix and its state properties at the same time.

 In the file `Setups.lean`, it contributes to foundational objects and notational definitions for operators, channels, norms, and the maps studied in the paper. Later declarations use this name instead of repeatedly expanding the underlying matrix formula.

## Original code

```lean
abbrev DensityState (d : Type u) [Fintype d] [DecidableEq d] :=
  {ρ : Matrix d d ℂ // IsDensityState ρ}
```

## Line-by-line explanation

The explanation below follows the declaration one physical line at a time. For long proofs, some lines are tiny bookkeeping steps; those are still explained, but briefly.

1. Code:
```lean
abbrev DensityState (d : Type u) [Fintype d] [DecidableEq d] :=
```
This line starts the `DensityState` declaration. Because it begins with `abbrev`, Lean now knows what kind of named object is being introduced. The bracketed assumptions tell Lean that the relevant index sets are finite and that equality of indices can be checked mechanically.  A bracket such as `[Fintype d]` tells Lean that the index set `d` is finite, so sums over all indices make sense.  A bracket such as `[DecidableEq d]` tells Lean that it can decide whether two indices are equal.

2. Code:
```lean
  {ρ : Matrix d d ℂ // IsDensityState ρ}
```
This line is one local step in the declaration. It either refines the formula being defined or advances the proof by a small algebraic or logical move.  `Matrix d d ℂ` means a square matrix with complex entries; the index type `d` tells Lean which rows and columns exist.

## Mathematical summary

In ordinary mathematical language, `DensityState` is the project's formal Lean name for the object introduced in this declaration.

## Dependencies and downstream use

### Earlier declarations this depends on
- [`IsDensityState`](IsDensityState.md) from `Setups.lean`

### Later declarations that use this one
- [`diamondNorm`](diamondNorm.md) in `Setups.lean`
- [`diamondNormAt`](diamondNormAt.md) in `Setups.lean`
- [`diamond_le_of_pointwise`](../StandardFacts/diamond_le_of_pointwise.md) in `StandardFacts.lean`
- [`traceNorm_apply_le_diamond`](../StandardFacts/traceNorm_apply_le_diamond.md) in `StandardFacts.lean`
- [`exists_maximizing_state`](../StandardFacts/exists_maximizing_state.md) in `StandardFacts.lean`

## Backlinks

- [Back to `INDEX.md`](../INDEX.md)
- [Back to the `Setups.lean` section in the index](../INDEX.md#diamond-setups-lean)
- [Previous declaration in this file](IsDensityState.md)
- [Next declaration in this file](IsHermiticityPreserving.md)