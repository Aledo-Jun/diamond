# diamond_le_of_pointwise

## Source location

- Original Lean file: `Diamond/StandardFacts.lean`
- Declaration name: `diamond_le_of_pointwise`
- Declaration kind: `theorem`

## Why this declaration exists

This theorem is the abstract pointwise-to-diamond reduction used throughout the project.

Earlier versions of the repository treated this step as background input. The current theorem proves
it directly in the nonempty finite-dimensional setting by showing the supremum set is nonempty and
then applying `csSup_le`.

## Current code

```lean
theorem diamond_le_of_pointwise
    {d : Type u} [Fintype d] [DecidableEq d] [Nonempty d]
    (Φ : Channel d) (b : ℝ)
    (hbound : ∀ ρ : DensityState (d × d),
      traceNormOp (tensorWithIdentity d d Φ ρ.1) ≤ b) :
    diamondOp Φ ≤ b := by
  ...
```

## Block-by-block explanation

1. Unfold `diamondOp` into the `sSup` defining `diamondNormAt`.
2. Build one explicit density state `ρ0` from a basis vector so the witness set is nonempty.
3. Apply `csSup_le`.
4. Use the hypothesis `hbound` to show every witness value is at most `b`.

## Mathematical summary

The statement is the standard supremum argument:

- if every stabilized test state gives output trace norm at most `b`,
- then the stabilized supremum defining the diamond norm is also at most `b`.

The `Nonempty d` hypothesis is essential here because the proof needs one explicit density state to
show the supremum is taken over a nonempty set.

## Dependencies and downstream use

### Earlier declarations this depends on
- [`Channel`](../Setups/Channel.md) from `Setups.lean`
- [`DensityState`](../Setups/DensityState.md) from `Setups.lean`
- [`traceNormOp`](../Setups/traceNormOp.md) from `Setups.lean`
- [`tensorWithIdentity`](../Setups/tensorWithIdentity.md) from `Setups.lean`
- [`diamondNormAt`](../Setups/diamondNormAt.md) from `Setups.lean`
- [`diamondOp`](../Setups/diamondOp.md) from `Setups.lean`

### Related declaration
- [`diamond_le_of_pointwise_nonempty`](diamond_le_of_pointwise_nonempty.md) in `StandardFacts.lean`

## Backlinks

- [Back to `INDEX.md`](../INDEX.md)
- [Back to the `StandardFacts.lean` section in the index](../INDEX.md#diamond-standardfacts-lean)
