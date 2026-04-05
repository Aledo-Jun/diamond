---
layout: default
---

# asymptotic_cotangent_lower_bound

## Source location

- Original Lean file: `Diamond/StandardFacts.lean`
- Declaration name: `asymptotic_cotangent_lower_bound`
- Declaration kind: `theorem`

## Why this declaration exists

This theorem passes from finite-dimensional cotangent bounds to the universal lower bound
\[
2 / \pi \le \alpha.
\]

It is no longer assumed. The proof is now internal and works by constructing an explicit sequence
whose limit is `2 / π`, then applying the uniform finite-dimensional hypothesis along that
sequence.

## Current code

```lean
theorem asymptotic_cotangent_lower_bound
    {α : ℝ} :
    (∀ d : ℕ, 2 ≤ d → Real.cot (Real.pi / (2 * (d : ℝ))) / (d : ℝ) ≤ α) →
      (2 : ℝ) / Real.pi ≤ α := by
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
