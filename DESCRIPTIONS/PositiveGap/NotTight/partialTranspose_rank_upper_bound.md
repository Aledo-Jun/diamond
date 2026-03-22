# partialTranspose_rank_upper_bound

## Source location

- Original Lean file: `Diamond/PositiveGap/NotTight.lean`
- Declaration name: `partialTranspose_rank_upper_bound`
- Declaration kind: `theorem`

## Why this declaration exists

This theorem packages the Uhlmann/vectorization rank estimate used in the final contradiction of
`theorem_not_tight`.

It no longer lives in `StandardFacts.lean`. The argument is now proved locally inside
`PositiveGap/NotTight.lean`, where it naturally belongs with the equality-case analysis.

## Current code

```lean
private theorem partialTranspose_rank_upper_bound
    {d : Type u} [Fintype d] [DecidableEq d] [Nonempty d]
    {X : Matrix (d × d) (d × d) ℂ} :
    X ≠ 0 →
    Matrix.IsHermitian X →
    Matrix.trace X = 0 →
    partialTraceLeft d d X = 0 →
    X.rank = 2 →
    (partialTransposeMap d d X).rank ≤ Fintype.card (d × d) - Fintype.card d := by
  ...
```

## Block-by-block explanation

1. Use `rank_two_traceless_hermitian_decomposition` to write `X` as a difference of two rank-one
   projectors.
2. Use the vanishing partial trace hypothesis to identify the two reduced states.
3. Apply the matrix form of Uhlmann’s theorem to compare the two vectors by a unitary.
4. Rewrite the partial transpose of `X` into the explicit tensor-difference form handled by the
   earlier rank lemmas.
5. Conclude the rank bound from the explicit diagonal/tensor estimate.

## Mathematical summary

This is the internal rank estimate that drives the contradiction in the finite-dimensional
non-tightness proof. It is one of the deepest local ingredients in `PositiveGap/NotTight.lean`.

## Dependencies and downstream use

### Earlier declarations this depends on
- [`partialTraceLeft`](../../Setups/partialTraceLeft.md) from `Setups.lean`
- [`partialTransposeMap`](../../Setups/partialTransposeMap.md) from `Setups.lean`
- `rank_two_traceless_hermitian_decomposition` from `StandardFacts.lean`

### Later declarations that use this one
- [`theorem_not_tight`](theorem_not_tight.md) in `PositiveGap/NotTight.lean`

## Backlinks

- [Back to `INDEX.md`](../../INDEX.md)
- [Back to the `PositiveGap/NotTight.lean` section in the index](../../INDEX.md#diamond-positivegap-nottight-lean)
