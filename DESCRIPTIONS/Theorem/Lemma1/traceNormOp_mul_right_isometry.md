# traceNormOp_mul_right_isometry

## Source location

- Original Lean file: `Diamond/Theorem/Lemma1.lean`
- Declaration name: `traceNormOp_mul_right_isometry`
- Declaration kind: `theorem`

## Why this declaration exists

Right multiplication by an isometry preserves the concrete trace norm.

 In the file `Theorem/Lemma1.lean`, it contributes to the proof infrastructure for the first norm inequality and the public theorem `lemma1`. Later proofs call this result by name, so documenting it makes the larger argument readable as a mathematical chain rather than as opaque proof script.

## Original code

```lean
/-- Right multiplication by an isometry preserves the concrete trace norm. -/
theorem traceNormOp_mul_right_isometry
    {d : Type u} [Fintype d] [DecidableEq d]
    (X U : Matrix d d ℂ) (hU : U * Uᴴ = 1) :
    traceNormOp (X * U) = traceNormOp X := by
  have hU' : (Uᴴ)ᴴ * Uᴴ = 1 := by
    simpa using hU
  calc
    traceNormOp (X * U) = traceNormOp ((X * U)ᴴ) := by
      symm
      exact traceNormOp_conjTranspose (X := X * U)
    _ = traceNormOp (Uᴴ * Xᴴ) := by
      rw [Matrix.conjTranspose_mul]
    _ = traceNormOp Xᴴ := by
      exact traceNormOp_mul_left_isometry (U := Uᴴ) (X := Xᴴ) hU'
    _ = traceNormOp X := by
      exact traceNormOp_conjTranspose (X := X)
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
