# traceNormOp_hermitian_eq_sum_abs_eigenvalues

## Source location

- Original Lean file: `Diamond/Theorem/Lemma1.lean`
- Declaration name: `traceNormOp_hermitian_eq_sum_abs_eigenvalues`
- Declaration kind: `theorem`

## Why this declaration exists

For Hermitian matrices, the concrete trace norm is the sum of the absolute eigenvalues.

 In the file `Theorem/Lemma1.lean`, it contributes to the proof infrastructure for the first norm inequality and the public theorem `lemma1`. Later proofs call this result by name, so documenting it makes the larger argument readable as a mathematical chain rather than as opaque proof script.

## Original code

```lean
/-- For Hermitian matrices, the concrete trace norm is the sum of the absolute eigenvalues. -/
theorem traceNormOp_hermitian_eq_sum_abs_eigenvalues
    {d : Type u} [Fintype d] [DecidableEq d]
    {A : Matrix d d ℂ} (hA : Matrix.IsHermitian A) :
    traceNormOp A = ∑ i, |hA.eigenvalues i| := by
  let U : Matrix d d ℂ := hA.eigenvectorUnitary
  let Ustar : Matrix d d ℂ := star hA.eigenvectorUnitary
  let D : Matrix d d ℂ := Matrix.diagonal (fun i => ((hA.eigenvalues i : ℝ) : ℂ))
  have hU_left : Uᴴ * U = 1 := by
    exact (Matrix.mem_unitaryGroup_iff').1 hA.eigenvectorUnitary.property
  have hUstar_right : Ustar * Ustarᴴ = 1 := by
    exact (Matrix.mem_unitaryGroup_iff).1 (star hA.eigenvectorUnitary).property
  calc
    traceNormOp A = traceNormOp (U * (D * Ustar)) := by
      simpa [Unitary.conjStarAlgAut_apply, U, Ustar, D, Matrix.mul_assoc] using
        congrArg traceNormOp hA.spectral_theorem
    _ = traceNormOp (D * Ustar) := by
      exact traceNormOp_mul_left_isometry (U := U) (X := D * Ustar) hU_left
    _ = traceNormOp D := by
      exact traceNormOp_mul_right_isometry (X := D) (U := Ustar) hUstar_right
    _ = ∑ i, |hA.eigenvalues i| := by
      simp [D, traceNormOp_diagonal]
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
