# lemma_transpose_diamond

## Source location

- Original Lean file: `Diamond/StandardFacts.lean`
- Declaration name: `lemma_transpose_diamond`
- Declaration kind: `theorem`

## Why this declaration exists

This theorem proves the exact diamond norm of transposition:

\[
\|\Theta\|_\diamond = \sqrt{\mathrm{card}(d \times d)} = \mathrm{card}(d).
\]

It used to be treated as background input. The current proof is internal: the upper bound comes
from the generic pointwise estimate plus `lemma2` and `lemma3`, while the lower bound comes from
the explicit maximally entangled witness `phiStateGen`.

## Current code

```lean
theorem lemma_transpose_diamond
    {d : Type u} [Fintype d] [DecidableEq d] [Nonempty d] :
    diamondOp (transposeMap d) = Real.sqrt (Fintype.card (d × d) : ℝ) := by
  ...
```

## Block-by-block explanation

1. Rewrite the target dimension factor as `card(d)` via `sqrt_card_prod_self`.
2. Prove the upper bound with `diamond_le_of_pointwise_nonempty`, `lemma2`, and `lemma3`.
3. Choose the explicit density witness `phiStateGen d`.
4. Compute its image under transposition and identify it with the swap operator.
5. Evaluate the trace norm of that witness exactly to get the lower bound.

## Mathematical summary

The theorem is the project’s formal version of the standard transposition-norm computation. It is
used repeatedly to replace the dimension factor by `diamondOp (transposeMap d)` in later arguments.

## Dependencies and downstream use

### Earlier declarations this depends on
- [`transposeMap`](../Setups/transposeMap.md) from `Setups.lean`
- [`diamondOp`](../Setups/diamondOp.md) from `Setups.lean`

### Later declarations that use this one
- [`theorem1`](../Theorem/Theorem1/theorem1.md) in `Theorem/Theorem1.lean`
- [`remark1`](../Theorem/Remark1/remark1.md) in `Theorem/Remark1.lean`
- [`theorem_not_tight`](../PositiveGap/NotTight/theorem_not_tight.md) in `PositiveGap/NotTight.lean`
- [`alpha_lower_bound`](../EndMatter/Eq8/alpha_lower_bound.md) in `EndMatter/Eq8.lean`
- [`corollary2_linear_bound`](../EndMatter/Corollary2/corollary2_linear_bound.md) in `EndMatter/Corollary2.lean`

## Backlinks

- [Back to `INDEX.md`](../INDEX.md)
- [Back to the `StandardFacts.lean` section in the index](../INDEX.md#diamond-standardfacts-lean)
