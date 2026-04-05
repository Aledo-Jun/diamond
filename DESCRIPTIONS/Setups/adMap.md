---
layout: default
---

# adMap

## Source location

- Original Lean file: `Diamond/Setups.lean`
- Declaration name: `adMap`
- Declaration kind: `def`

## Why this declaration exists

This definition packages unitary conjugation $X \mapsto UXU^\dagger$ as a channel.

 In the file `Setups.lean`, it contributes to foundational objects and notational definitions for operators, channels, norms, and the maps studied in the paper. Later declarations use this name instead of repeatedly expanding the underlying matrix formula.

## Original code

```lean
/-- Unitary conjugation. -/
def adMap (d : Type u) [Fintype d] [DecidableEq d]
    (U : Matrix d d ℂ) : Channel d where
  toFun := fun X => U * X * Uᴴ
  map_add' := by
    intro X Y
    simp [Matrix.mul_add, Matrix.add_mul, Matrix.mul_assoc]
  map_smul' := by
    intro c X
    simp [Matrix.mul_assoc]
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
