---
layout: default
---

# hermitian_re_trace_conjTranspose_mul_self_eq_sum_sq_eigenvalues

## Source location

- Original Lean file: `Diamond/Theorem/Lemma1.lean`
- Declaration name: `hermitian_re_trace_conjTranspose_mul_self_eq_sum_sq_eigenvalues`
- Declaration kind: `theorem`

## Why this declaration exists

This theorem records a reusable fact named `hermitian_re_trace_conjTranspose_mul_self_eq_sum_sq_eigenvalues`. Its role is to make the later proof flow easier to state and reuse.

 In the file `Theorem/Lemma1.lean`, it contributes to the proof infrastructure for the first norm inequality and the public theorem `lemma1`. Later proofs call this result by name, so documenting it makes the larger argument readable as a mathematical chain rather than as opaque proof script.

## Original code

```lean
theorem hermitian_re_trace_conjTranspose_mul_self_eq_sum_sq_eigenvalues
    {d : Type u} [Fintype d] [DecidableEq d]
    {A : Matrix d d ℂ} (hA : Matrix.IsHermitian A) :
    Complex.re (Matrix.trace (Aᴴ * A)) = ∑ i, (hA.eigenvalues i) ^ 2 := by
  let U : Matrix d d ℂ := hA.eigenvectorUnitary
  let D : Matrix d d ℂ := Matrix.diagonal (fun i => ((hA.eigenvalues i : ℝ) : ℂ))
  let e := Unitary.conjStarAlgAut ℂ (Matrix d d ℂ) (star hA.eigenvectorUnitary)
  have hdiag : e A = D := by
    simpa [e, D] using hA.conjStarAlgAut_star_eigenvectorUnitary
  have hmul : e (A * A) = e A * e A := by
    exact map_mul e A A
  have hDsq : D * D = (star hA.eigenvectorUnitary : Matrix d d ℂ) * (A * A) * U := by
    calc
      D * D = e (A * A) := by
        rw [← hdiag]
        simpa [hdiag] using hmul.symm
      _ = (star hA.eigenvectorUnitary : Matrix d d ℂ) * (A * A) * U := by
        simp [e, U, Unitary.conjStarAlgAut_apply]
  have hUright : U * (star hA.eigenvectorUnitary : Matrix d d ℂ) = 1 := by
    simpa [U] using (Matrix.mem_unitaryGroup_iff).1 hA.eigenvectorUnitary.property
  have hAA : Aᴴ * A = A * A := by
    simpa [hA.eq]
  calc
    Complex.re (Matrix.trace (Aᴴ * A)) = Complex.re (Matrix.trace (A * A)) := by
      rw [hAA]
    _ = Complex.re (Matrix.trace ((star hA.eigenvectorUnitary : Matrix d d ℂ) * (A * A) * U)) := by
          rw [Matrix.trace_mul_cycle (star hA.eigenvectorUnitary : Matrix d d ℂ) (A * A) U]
          simp [hUright]
    _ = Complex.re (Matrix.trace (D * D)) := by
          rw [hDsq]
    _ = ∑ i, (hA.eigenvalues i) ^ 2 := by
          simp [D, Matrix.trace, pow_two]
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
