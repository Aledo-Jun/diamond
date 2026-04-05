---
layout: default
---

# lemma3

## Source location

- Original Lean file: `Diamond/Theorem/Lemma3.lean`
- Declaration name: `lemma3`
- Declaration kind: `theorem`

## Why this declaration exists

Lemma 3: partial transpose preserves the Hilbert--Schmidt norm.

 In the file `Theorem/Lemma3.lean`, it contributes to the Hilbert--Schmidt invariance of partial transpose. Later proofs call this result by name, so documenting it makes the larger argument readable as a mathematical chain rather than as opaque proof script.

## Original code

```lean
/-- Lemma 3: partial transpose preserves the Hilbert--Schmidt norm. -/
theorem lemma3
    {d k : Type u} [Fintype d] [DecidableEq d] [Fintype k] [DecidableEq k]
    (X : Matrix (d × k) (d × k) ℂ) :
    hsNormOp (partialTransposeMap d k X) = hsNormOp X := by
  change ‖partialTransposeMap d k X‖ = ‖X‖
  let e : (d × k) × (d × k) ≃ (d × k) × (d × k) :=
    { toFun := fun p => ((p.2.1, p.1.2), (p.1.1, p.2.2))
      invFun := fun p => ((p.2.1, p.1.2), (p.1.1, p.2.2))
      left_inv := by
        intro p
        aesop
      right_inv := by
        intro p
        aesop }
  have hEq :
      (∑ p : (d × k) × (d × k), ‖X (e p).1 (e p).2‖ ^ (2 : ℝ)) =
        ∑ p : (d × k) × (d × k), ‖X p.1 p.2‖ ^ (2 : ℝ) := by
    exact Equiv.sum_comp e (g := fun p => ‖X p.1 p.2‖ ^ (2 : ℝ))
  calc
    ‖partialTransposeMap d k X‖
      = (∑ p : (d × k) × (d × k), ‖X (e p).1 (e p).2‖ ^ (2 : ℝ)) ^ (1 / 2 : ℝ) := by
          simp [partialTransposeMap, Matrix.frobenius_norm_def, e, Fintype.sum_prod_type]
    _ = (∑ p : (d × k) × (d × k), ‖X p.1 p.2‖ ^ (2 : ℝ)) ^ (1 / 2 : ℝ) := by
          rw [hEq]
    _ = ‖X‖ := by
          simp [Matrix.frobenius_norm_def, Fintype.sum_prod_type]
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
