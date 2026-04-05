# traceNormOp_sub_density_le_two

## Source location

- Original Lean file: `Diamond/Theorem/Lemma1.lean`
- Declaration name: `traceNormOp_sub_density_le_two`
- Declaration kind: `theorem`

## Why this declaration exists

The concrete trace distance between density states is at most `2`.

 In the file `Theorem/Lemma1.lean`, it contributes to the proof infrastructure for the first norm inequality and the public theorem `lemma1`. Later proofs call this result by name, so documenting it makes the larger argument readable as a mathematical chain rather than as opaque proof script.

## Original code

```lean
/-- The concrete trace distance between density states is at most `2`. -/
private theorem traceNormOp_sub_density_le_two
    {d : Type u} [Fintype d] [DecidableEq d]
    {ρ σ : Matrix d d ℂ} (hρ : IsDensityState ρ) (hσ : IsDensityState σ) :
    traceNormOp (ρ - σ) ≤ 2 := by
  let X : Matrix d d ℂ := ρ - σ
  have hX : Matrix.IsHermitian X := hρ.1.isHermitian.sub hσ.1.isHermitian
  let U : Matrix d d ℂ := hX.eigenvectorUnitary
  let Ustar : Matrix d d ℂ := star hX.eigenvectorUnitary
  let D : Matrix d d ℂ := Matrix.diagonal (fun i => ((hX.eigenvalues i : ℝ) : ℂ))
  let P : Matrix d d ℂ := Ustar * ρ * U
  let Q : Matrix d d ℂ := Ustar * σ * U
  have hU_right : U * Ustar = 1 := by
    exact (Matrix.mem_unitaryGroup_iff).1 hX.eigenvectorUnitary.property
  have hP_pos : P.PosSemidef := by
    simpa [P, U, Ustar, Matrix.mul_assoc] using hρ.1.conjTranspose_mul_mul_same U
  have hQ_pos : Q.PosSemidef := by
    simpa [Q, U, Ustar, Matrix.mul_assoc] using hσ.1.conjTranspose_mul_mul_same U
  have hP_trace : Matrix.trace P = 1 := by
    calc
      Matrix.trace P = Matrix.trace ((U * Ustar) * ρ) := by
        dsimp [P]
        rw [Matrix.trace_mul_cycle Ustar ρ U, Matrix.mul_assoc]
      _ = Matrix.trace ρ := by
        rw [hU_right, one_mul]
      _ = 1 := hρ.2
  have hQ_trace : Matrix.trace Q = 1 := by
    calc
      Matrix.trace Q = Matrix.trace ((U * Ustar) * σ) := by
        dsimp [Q]
        rw [Matrix.trace_mul_cycle Ustar σ U, Matrix.mul_assoc]
      _ = Matrix.trace σ := by
        rw [hU_right, one_mul]
      _ = 1 := hσ.2
  have hdiag :
      P - Q = D := by
    simpa [X, U, Ustar, D, P, Q, Unitary.conjStarAlgAut_apply, Matrix.mul_assoc,
      Matrix.mul_sub, Matrix.sub_mul] using hX.conjStarAlgAut_star_eigenvectorUnitary
  have hbound :
      ∀ i : d, |hX.eigenvalues i| ≤ Complex.re (P i i) + Complex.re (Q i i) := by
    intro i
    have hPiC : 0 ≤ P i i := hP_pos.diag_nonneg
    have hQiC : 0 ≤ Q i i := hQ_pos.diag_nonneg
    have hPi : 0 ≤ Complex.re (P i i) := by
      exact (RCLike.nonneg_iff.mp hPiC).1
    have hQi : 0 ≤ Complex.re (Q i i) := by
      exact (RCLike.nonneg_iff.mp hQiC).1
    have hpoint :
        Complex.re (P i i) - Complex.re (Q i i) = hX.eigenvalues i := by
      have hpointC := congrArg (fun M : Matrix d d ℂ => M i i) hdiag
      simpa [D] using congrArg Complex.re hpointC
    calc
      |hX.eigenvalues i| = |Complex.re (P i i) - Complex.re (Q i i)| := by
        rw [← hpoint]
      _ = |Complex.re (P i i) + (-Complex.re (Q i i))| := by
        rw [sub_eq_add_neg]
      _ ≤ |Complex.re (P i i)| + |-Complex.re (Q i i)| := abs_add_le _ _
      _ = Complex.re (P i i) + Complex.re (Q i i) := by
        rw [abs_of_nonneg hPi, abs_neg, abs_of_nonneg hQi]
  calc
    traceNormOp X = ∑ i, |hX.eigenvalues i| := by
      simpa [X] using traceNormOp_hermitian_eq_sum_abs_eigenvalues hX
    _ ≤ ∑ i, (Complex.re (P i i) + Complex.re (Q i i)) := by
      exact Finset.sum_le_sum (fun i hi => hbound i)
    _ = (∑ i, Complex.re (P i i)) + ∑ i, Complex.re (Q i i) := by
      rw [Finset.sum_add_distrib]
    _ = Complex.re (Matrix.trace P) + Complex.re (Matrix.trace Q) := by
      simp [Matrix.trace]
    _ = 2 := by
      rw [hP_trace, hQ_trace]
      norm_num
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
