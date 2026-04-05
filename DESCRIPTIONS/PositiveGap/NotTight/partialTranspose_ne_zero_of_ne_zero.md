---
layout: default
---

# partialTranspose_ne_zero_of_ne_zero

## Source location

- Original Lean file: `Diamond/PositiveGap/NotTight.lean`
- Declaration name: `partialTranspose_ne_zero_of_ne_zero`
- Declaration kind: `lemma`

## Why this declaration exists

Partial transpose preserves nonzeroness because it preserves the Hilbert--Schmidt norm.

 In the file `PositiveGap/NotTight.lean`, it contributes to the finite-dimensional non-tightness argument and the equality-case analysis behind it. Later proofs call this result by name, so documenting it makes the larger argument readable as a mathematical chain rather than as opaque proof script.

## Original code

```lean
/-- Partial transpose preserves nonzeroness because it preserves the Hilbert--Schmidt norm. -/
private lemma partialTranspose_ne_zero_of_ne_zero
    {d k : Type u} [Fintype d] [DecidableEq d] [Fintype k] [DecidableEq k]
    {X : Matrix (d × k) (d × k) ℂ} (hX : X ≠ 0) :
    partialTransposeMap d k X ≠ 0 := by
  intro hzero
  have hnormY : hsNormOp (partialTransposeMap d k X) = 0 := by
    exact (hsNormOp_eq_zero_iff).2 hzero
  have hnormX : hsNormOp X = 0 := by
    rw [lemma3 (d := d) (k := k) X] at hnormY
    exact hnormY
  exact hX ((hsNormOp_eq_zero_iff).1 hnormX)
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
