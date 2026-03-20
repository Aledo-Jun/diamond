# diamond_le_of_pointwise

## Source location

- Original Lean file: `Diamond/StandardFacts.lean`
- Declaration name: `diamond_le_of_pointwise`
- Declaration kind: `axiom`

## Why this declaration exists

This axiom is the strongest abstract pointwise-to-diamond reduction retained in the file. It covers
degenerate empty-index edge cases as well as the ordinary nonempty situation.

The core proof path of Theorem 1 and Remark 1 no longer uses this axiom directly. Those proofs now
use the proved theorem [`diamond_le_of_pointwise_nonempty`](diamond_le_of_pointwise_nonempty.md),
which is the exact supremum step appearing in `docs/diamond.md`.

## Current code

```lean
axiom diamond_le_of_pointwise
    {d : Type u} [Fintype d] [DecidableEq d]
    (Φ : Channel d) (b : ℝ)
    (hbound : ∀ ρ : DensityState (d × d),
      traceNormOp (tensorWithIdentity d d Φ ρ.1) ≤ b) :
    diamondOp Φ ≤ b
```

## Mathematical summary

This declaration says: if every ancilla-`d` density operator gives an output trace norm at most
`b`, then the stabilized supremum `diamondOp Φ` is also at most `b`.

## Dependencies and downstream use

### Earlier declarations this depends on
- [`Channel`](../Setups/Channel.md) from `Setups.lean`
- [`traceNormOp`](../Setups/traceNormOp.md) from `Setups.lean`
- [`DensityState`](../Setups/DensityState.md) from `Setups.lean`
- [`tensorWithIdentity`](../Setups/tensorWithIdentity.md) from `Setups.lean`
- [`diamondOp`](../Setups/diamondOp.md) from `Setups.lean`

### Related declaration
- [`diamond_le_of_pointwise_nonempty`](diamond_le_of_pointwise_nonempty.md) in `StandardFacts.lean`

## Backlinks

- [Back to `INDEX.md`](../INDEX.md)
- [Back to the `StandardFacts.lean` section in the index](../INDEX.md#diamond-standardfacts-lean)
- [Previous declaration in this file](adMap_isQuantumChannel.md)
- [Next declaration in this file](diamond_le_of_pointwise_nonempty.md)
