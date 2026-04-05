---
layout: default
---

# traceNormOp_mul_left_isometry

## Source location

- Original Lean file: `Diamond/Theorem/Lemma1.lean`
- Declaration name: `traceNormOp_mul_left_isometry`
- Declaration kind: `theorem`

## Why this declaration exists

Left multiplication by an isometry preserves the concrete trace norm.

 In the file `Theorem/Lemma1.lean`, it contributes to the proof infrastructure for the first norm inequality and the public theorem `lemma1`. Later proofs call this result by name, so documenting it makes the larger argument readable as a mathematical chain rather than as opaque proof script.

## Original code

```lean
/-- Left multiplication by an isometry preserves the concrete trace norm. -/
theorem traceNormOp_mul_left_isometry
    {d : Type u} [Fintype d] [DecidableEq d]
    (U X : Matrix d d ℂ) (hU : Uᴴ * U = 1) :
    traceNormOp (U * X) = traceNormOp X := by
  have hmul : (U * X)ᴴ * (U * X) = Xᴴ * X := by
    calc
      (U * X)ᴴ * (U * X) = Xᴴ * (Uᴴ * U) * X := by
        simp [Matrix.conjTranspose_mul, Matrix.mul_assoc]
      _ = Xᴴ * X := by
        simp [hU]
  dsimp [traceNormOp, traceNorm]
  have hEig :
      (Matrix.isHermitian_conjTranspose_mul_self (U * X)).eigenvalues =
        (Matrix.isHermitian_conjTranspose_mul_self X).eigenvalues := by
    apply
      (Matrix.IsHermitian.eigenvalues_eq_eigenvalues_iff
        (Matrix.isHermitian_conjTranspose_mul_self (U * X))
        (Matrix.isHermitian_conjTranspose_mul_self X)).2
    exact congrArg Matrix.charpoly hmul
  rw [hEig]
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
