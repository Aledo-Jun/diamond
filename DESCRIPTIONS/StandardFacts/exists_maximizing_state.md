# exists_maximizing_state

## Source location

- Original Lean file: `Diamond/StandardFacts.lean`
- Declaration name: `exists_maximizing_state`
- Declaration kind: `theorem`

## Why this declaration exists

This theorem packages the finite-dimensional attainment statement used in the non-tightness
argument.

It is now proved internally. The Lean proof avoids treating `traceNormOp` continuity as a black box
by maximizing a continuous real-valued pairing over the compact product of unitary matrices and
density states, then recovering the trace norm through the Hermitian variational formula added in
`StandardFacts.lean`.

## Current code

```lean
/-- Finite-dimensional attainment of the left-hand diamond norm in the positive-gap argument.
    This compactness/maximizer step is background to the paper's main flow. -/
theorem exists_maximizing_state
    {d : Type u} [Fintype d] [DecidableEq d] [Nonempty d]
    (T : Channel d) (hT : IsQuantumChannel T) (hΦ : idMinus T ≠ 0) :
    ∃ ρ : DensityState (d × d),
      traceNormOp
          (tensorWithIdentity d d ((transposeMap d).comp (idMinus T)) ρ.1) =
        diamondOp ((transposeMap d).comp (idMinus T)) ∧
      tensorWithIdentity d d (idMinus T) ρ.1 ≠ 0 := by
  ...
```

## Block-by-block explanation

1. Rename the channel difference `Φ := idMinus T`, its transposed version `LΦ`, and the stabilized
   partially transposed map `Ψ`.
2. Put the unitary matrices and density states into a compact product set.
3. Define the continuous objective
   `f(U, ρ) = Re(trace(U * Ψ ρ))`.
4. Use compactness to choose a maximizing pair `(U₀, ρ₀)`.
5. For each fixed `ρ`, apply the Hermitian variational trace-norm formula to compare
   `traceNormOp (Ψ ρ)` with `f(U₀, ρ₀)`.
6. Convert that comparison into equality
   `traceNormOp ((LΦ ⊗ id)(ρ₀)) = diamondOp LΦ`.
7. Use the explicit `phiStateGen` witness and `idMinus T ≠ 0` to show the maximizing state is not a
   zero witness for `Φ ⊗ id`.

## Mathematical summary

This is the exact finite-dimensional “the supremum is attained” statement needed by
`theorem_not_tight`. The proof combines:

- compactness of density states,
- compactness of the unitary group,
- a continuous bilinear pairing,
- and a unitary variational formula for the trace norm of Hermitian matrices.

## Dependencies and downstream use

### Earlier declarations this depends on
- [`Channel`](../Setups/Channel.md) from `Setups.lean`
- [`traceNormOp`](../Setups/traceNormOp.md) from `Setups.lean`
- [`DensityState`](../Setups/DensityState.md) from `Setups.lean`
- [`IsQuantumChannel`](../Setups/IsQuantumChannel.md) from `Setups.lean`
- [`transposeMap`](../Setups/transposeMap.md) from `Setups.lean`
- [`tensorWithIdentity`](../Setups/tensorWithIdentity.md) from `Setups.lean`
- [`diamondOp`](../Setups/diamondOp.md) from `Setups.lean`
- [`idMinus`](../Setups/idMinus.md) from `Setups.lean`

### Later declarations that use this one
- [`theorem_not_tight`](../PositiveGap/NotTight/theorem_not_tight.md) in `PositiveGap/NotTight.lean`

## Backlinks

- [Back to `INDEX.md`](../INDEX.md)
- [Back to the `StandardFacts.lean` section in the index](../INDEX.md#diamond-standardfacts-lean)
