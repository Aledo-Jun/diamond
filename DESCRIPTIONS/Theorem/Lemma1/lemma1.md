---
layout: default
---

# lemma1

## Source location

- Original Lean file: `Diamond/Theorem/Lemma1.lean`
- Declaration name: `lemma1`
- Declaration kind: `theorem`

## Why this declaration exists

Lemma 1: For traceless Hermitian `X`, `‖X‖₂ ≤ (1 / √2) ‖X‖₁`.

 In the file `Theorem/Lemma1.lean`, it contributes to the proof infrastructure for the first norm inequality and the public theorem `lemma1`. Later proofs call this result by name, so documenting it makes the larger argument readable as a mathematical chain rather than as opaque proof script.

## Original code

```lean
/-- Lemma 1: For traceless Hermitian `X`, `‖X‖₂ ≤ (1 / √2) ‖X‖₁`. -/
theorem lemma1
    {d : Type u} [Fintype d] [DecidableEq d]
    (X : Matrix d d ℂ) (hHerm : Matrix.IsHermitian X) (hTrace : Matrix.trace X = 0) :
    hsNormOp X ≤ (1 / Real.sqrt 2) * traceNormOp X := by
  let p : d → ℝ := fun i => max (hHerm.eigenvalues i) 0
  let q : d → ℝ := fun i => max (-hHerm.eigenvalues i) 0
  have hp_nonneg : ∀ i, 0 ≤ p i := by
    intro i
    simp [p]
  have hq_nonneg : ∀ i, 0 ≤ q i := by
    intro i
    simp [q]
  have habs : ∀ i, |hHerm.eigenvalues i| = p i + q i := by
    intro i
    by_cases hi : 0 ≤ hHerm.eigenvalues i
    · simp [p, q, hi, abs_of_nonneg hi]
    · have hi' : hHerm.eigenvalues i < 0 := lt_of_not_ge hi
      simp [p, q, hi'.le, abs_of_neg hi']
  have hsub : ∀ i, hHerm.eigenvalues i = p i - q i := by
    intro i
    by_cases hi : 0 ≤ hHerm.eigenvalues i
    · simp [p, q, hi]
    · have hi' : hHerm.eigenvalues i < 0 := lt_of_not_ge hi
      simp [p, q, hi'.le]
  have hsq : ∀ i, (hHerm.eigenvalues i) ^ 2 = (p i) ^ 2 + (q i) ^ 2 := by
    intro i
    by_cases hi : 0 ≤ hHerm.eigenvalues i
    · simp [p, q, hi, pow_two]
    · have hi' : hHerm.eigenvalues i < 0 := lt_of_not_ge hi
      simp [p, q, hi'.le, pow_two]
  have hsum_zero : ∑ i, hHerm.eigenvalues i = 0 := by
    have htraceC : (∑ i, ((hHerm.eigenvalues i : ℝ) : ℂ)) = 0 := by
      simpa [hHerm.trace_eq_sum_eigenvalues] using hTrace
    exact_mod_cast congrArg Complex.re htraceC
  have hpq : ∑ i, p i = ∑ i, q i := by
    have hsum_sub : ∑ i, (p i - q i) = 0 := by
      simpa [hsub] using hsum_zero
    rw [Finset.sum_sub_distrib] at hsum_sub
    linarith
  have hsumsq_le : ∑ i, (hHerm.eigenvalues i) ^ 2 ≤ 2 * (∑ i, p i) ^ 2 := by
    calc
      ∑ i, (hHerm.eigenvalues i) ^ 2 = ∑ i, (p i) ^ 2 + ∑ i, (q i) ^ 2 := by
        simp [hsq, Finset.sum_add_distrib]
      _ ≤ (∑ i, p i) ^ 2 + (∑ i, q i) ^ 2 := by
        gcongr
        · exact Finset.sum_sq_le_sq_sum_of_nonneg (fun i _ => hp_nonneg i)
        · exact Finset.sum_sq_le_sq_sum_of_nonneg (fun i _ => hq_nonneg i)
      _ = 2 * (∑ i, p i) ^ 2 := by
        rw [hpq]
        ring
  have htraceNorm :
      (∑ i, |hHerm.eigenvalues i|) = 2 * ∑ i, p i := by
    calc
      (∑ i, |hHerm.eigenvalues i|) = ∑ i, (p i + q i) := by
        simp [habs]
      _ = ∑ i, p i + ∑ i, q i := by
        rw [Finset.sum_add_distrib]
      _ = 2 * ∑ i, p i := by
        rw [hpq]
        ring
  have hsqrt2_ne : Real.sqrt 2 ≠ 0 := by
    positivity
  have hrhs :
      ((1 / Real.sqrt 2) * (2 * ∑ i, p i)) ^ 2 = 2 * (∑ i, p i) ^ 2 := by
    field_simp [pow_two, hsqrt2_ne]
    nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 2 by positivity)]
  have hsqineq : hsNormOp X ^ 2 ≤ ((1 / Real.sqrt 2) * (∑ i, |hHerm.eigenvalues i|)) ^ 2 := by
    rw [hsNorm_sq_eq_re_trace_conjTranspose_mul_self,
      hermitian_re_trace_conjTranspose_mul_self_eq_sum_sq_eigenvalues hHerm]
    rw [htraceNorm, hrhs]
    exact hsumsq_le
  have hleft : 0 ≤ hsNormOp X := norm_nonneg _
  have hright : 0 ≤ (1 / Real.sqrt 2) * (∑ i, |hHerm.eigenvalues i|) := by
    positivity
  have hle_abs : hsNormOp X ≤ |(1 / Real.sqrt 2) * (∑ i, |hHerm.eigenvalues i|)| := by
    simpa [abs_of_nonneg hleft] using (sq_le_sq.mp hsqineq)
  calc
    hsNormOp X ≤ |(1 / Real.sqrt 2) * (∑ i, |hHerm.eigenvalues i|)| := hle_abs
    _ = (1 / Real.sqrt 2) * (∑ i, |hHerm.eigenvalues i|) := abs_of_nonneg hright
    _ = (1 / Real.sqrt 2) * traceNormOp X := by
      rw [traceNormOp_hermitian_eq_sum_abs_eigenvalues hHerm]
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
