# Lambda

## Source location

- Original Lean file: `Diamond/Setups.lean`
- Declaration name: `Lambda`
- Declaration kind: `def`

## Why this declaration exists

This is the map $\Lambda_d = \Theta \circ (\mathrm{id} - \mathrm{Ad}_{U_d})$ used in Eq. (7).

 In the file `Setups.lean`, it contributes to foundational objects and notational definitions for operators, channels, norms, and the maps studied in the paper. Later declarations use this name instead of repeatedly expanding the underlying matrix formula.

## Original code

```lean
def Lambda (d : ℕ) [Fact (1 < d)] : Channel (Fin d) :=
  (transposeMap (Fin d)).comp (idMinus (adMap (Fin d) (Ud d)))
```

## Line-by-line explanation

The explanation below follows the declaration one physical line at a time. For long proofs, some lines are tiny bookkeeping steps; those are still explained, but briefly.

1. Code:
```lean
def Lambda (d : ℕ) [Fact (1 < d)] : Channel (Fin d) :=
```
This line starts the `Lambda` declaration. Because it begins with `def`, Lean now knows what kind of named object is being introduced. The type information on this line explains what sort of mathematical object the declaration talks about.  `Channel d` is an abbreviation for a complex-linear map from operators on `d` to operators on `d`.

2. Code:
```lean
  (transposeMap (Fin d)).comp (idMinus (adMap (Fin d) (Ud d)))
```
This line is one local step in the declaration. It either refines the formula being defined or advances the proof by a small algebraic or logical move.  `comp` means composition of maps: one map is applied after another.

## Mathematical summary

In ordinary mathematical language, `Lambda` is the project's formal Lean name for the object introduced in this declaration.

## Dependencies and downstream use

### Earlier declarations this depends on
- [`Channel`](Channel.md) from `Setups.lean`
- [`transposeMap`](transposeMap.md) from `Setups.lean`
- [`idMinus`](idMinus.md) from `Setups.lean`
- [`adMap`](adMap.md) from `Setups.lean`
- [`Ud`](Ud.md) from `Setups.lean`

### Later declarations that use this one
- [`lambda_phiState_eq`](../EndMatter/Eq7/lambda_phiState_eq.md) in `EndMatter/Eq7.lean`
- [`theorem_eq7_witness_bound`](../EndMatter/Eq7/theorem_eq7_witness_bound.md) in `EndMatter/Eq7.lean`
- [`theorem_eq7_witness_bound_explicit`](../EndMatter/Eq7/theorem_eq7_witness_bound_explicit.md) in `EndMatter/Eq7.lean`
- [`theorem_eq7`](../EndMatter/Eq7/theorem_eq7.md) in `EndMatter/Eq7.lean`
- [`alpha_lower_bound`](../EndMatter/Eq8/alpha_lower_bound.md) in `EndMatter/Eq8.lean`

## Backlinks

- [Back to `INDEX.md`](../INDEX.md)
- [Back to the `Setups.lean` section in the index](../INDEX.md#diamond-setups-lean)
- [Previous declaration in this file](Ud.md)