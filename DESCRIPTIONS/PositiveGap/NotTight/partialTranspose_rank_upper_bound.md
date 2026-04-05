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

## How To Read This Declaration

This page now uses a concise reading guide instead of a line-by-line Lean walkthrough.
The best way to read the declaration is:

1. read the **Why this declaration exists** section for the mathematical role,
2. read the **Original code** block as the exact formal statement or construction,
3. treat the proof as a small number of conceptual moves rather than a commentary on each Lean line.

## Proof / Construction Shape

Most declarations in this repository follow the same pattern:

- **setup**: introduce the ambient spaces, matrices, channels, or witnesses,
- **reduction**: rewrite the goal into a standard matrix, trace, or diamond-norm form,
- **core step**: apply previously proved lemmas from the same module or an earlier one,
- **finish**: simplify the remaining algebra with `rw`, `simp`, `calc`, or `ext`.

## Lean Cues

- `let` names an intermediate mathematical object.
- `have` records a useful subclaim.
- `calc` is a displayed derivation written as a chain of equalities or inequalities.
- `rw` rewrites using an identity.
- `simp` performs controlled simplification.
- `ext` means the proof is reduced to entrywise or pointwise equality.

For the math-first reading path, start from `DESCRIPTIONS/INDEX.md` and use the module overviews and flagship theorem pages before coming back to individual declaration pages.
