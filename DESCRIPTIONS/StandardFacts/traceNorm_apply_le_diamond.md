# traceNorm_apply_le_diamond

## Source location

- Original Lean file: `Diamond/StandardFacts.lean`
- Declaration name: `traceNorm_apply_le_diamond`
- Declaration kind: `theorem`

## Why this declaration exists

This theorem is the basic witness bound for the fixed-ancilla diamond norm.

For any particular density state `ρ`, the trace norm of `(Φ ⊗ id)(ρ)` must be bounded by the
supremum `diamondNormAt Φ`. The proof is no longer assumed as an axiom; it is carried out in
finite dimension using a Hilbert--Schmidt bound for `tensorWithIdentity` and the fact that density
states have Hilbert--Schmidt norm at most `1`.

## Current code

```lean
theorem traceNorm_apply_le_diamond
    {d : Type u} [Fintype d] [DecidableEq d] {k : Type u}
    [Fintype k] [DecidableEq k]
    (Φ : Channel d) (ρ : DensityState (d × k)) :
    traceNormOp (tensorWithIdentity d k Φ ρ.1) ≤ diamondNormAt (d := d) (k := k) Φ := by
  ...
```

## Block-by-block explanation

1. Rename `tensorWithIdentity d k Φ` to a single map `Ψ`.
2. Bound `Ψ X` in Hilbert--Schmidt norm by a finite-dimensional operator constant built from the
   images of matrix basis elements.
3. Use `lemma2` to pass from trace norm to Hilbert--Schmidt norm.
4. Use the density-state estimate `‖ρ‖₂ ≤ 1` to remove dependence on the chosen witness.
5. Conclude with the definition of `diamondNormAt` as a supremum over all density states.

## Mathematical summary

This is the formal version of the obvious supremum inequality:

- one particular test state gives one candidate value in the defining set for `diamondNormAt`,
- so its trace norm can never exceed the supremum.

The Lean proof is longer only because it makes the boundedness of the stabilized map explicit.

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
