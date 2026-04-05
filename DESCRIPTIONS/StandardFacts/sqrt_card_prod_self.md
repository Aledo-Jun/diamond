---
layout: default
---

# sqrt_card_prod_self

## Source location

- Original Lean file: `Diamond/StandardFacts.lean`
- Declaration name: `sqrt_card_prod_self`
- Declaration kind: `theorem`

## Why this declaration exists

Card-product square-root identity used for dimension reduction.

 In the file `StandardFacts.lean`, it contributes to helper facts and background reductions that later proofs use directly. Later proofs call this result by name, so documenting it makes the larger argument readable as a mathematical chain rather than as opaque proof script.

## Original code

```lean
/-- Card-product square-root identity used for dimension reduction. -/
theorem sqrt_card_prod_self
    {d k : Type u} [Fintype d] [Fintype k] :
    Real.sqrt (Fintype.card (d × k) : ℝ) =
      Real.sqrt (Fintype.card d : ℝ) * Real.sqrt (Fintype.card k : ℝ) := by
  rw [Fintype.card_prod]
  rw [Nat.cast_mul]
  rw [Real.sqrt_mul (show (0 : ℝ) ≤ Fintype.card d by positivity)]
  -- no further simplification needed
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
