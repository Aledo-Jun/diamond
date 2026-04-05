---
layout: default
---

# lemma2

## Source location

- Original Lean file: `Diamond/Theorem/Lemma2.lean`
- Declaration name: `lemma2`
- Declaration kind: `theorem`

## Why this declaration exists

Lemma 2: `‖Y‖₁ ≤ √N ‖Y‖₂` on an `N`-dimensional space.

 In the file `Theorem/Lemma2.lean`, it contributes to the Hilbert--Schmidt versus trace norm bound `lemma2`. Later proofs call this result by name, so documenting it makes the larger argument readable as a mathematical chain rather than as opaque proof script.

## Original code

```lean
/-- Lemma 2: `‖Y‖₁ ≤ √N ‖Y‖₂` on an `N`-dimensional space. -/
theorem lemma2
    {ι : Type u} [Fintype ι] [DecidableEq ι]
    (Y : Matrix ι ι ℂ) :
    traceNormOp Y ≤ Real.sqrt (Fintype.card ι : ℝ) * hsNormOp Y := by
  let μ : ι → ℝ := (Matrix.isHermitian_conjTranspose_mul_self Y).eigenvalues
  have hμ_nonneg : ∀ i, 0 ≤ μ i := by
    intro i
    exact Matrix.eigenvalues_conjTranspose_mul_self_nonneg Y i
  have hsum_sq :
      (∑ i, Real.sqrt (μ i)) ^ 2 ≤ (Fintype.card ι : ℝ) * ∑ i, μ i := by
    calc
      (∑ i, Real.sqrt (μ i)) ^ 2 ≤
          (Fintype.card ι : ℝ) * ∑ i, (Real.sqrt (μ i)) ^ 2 := by
            simpa using
              sq_sum_le_card_mul_sum_sq
                (s := (Finset.univ : Finset ι))
                (f := fun i => Real.sqrt (μ i))
      _ = (Fintype.card ι : ℝ) * ∑ i, μ i := by
            refine congrArg ((Fintype.card ι : ℝ) * ·) ?_
            refine Finset.sum_congr rfl ?_
            intro i hi
            exact Real.sq_sqrt (hμ_nonneg i)
  have hnorm_sq : hsNormOp Y ^ 2 = ∑ i, μ i := by
    calc
      hsNormOp Y ^ 2 = Complex.re (Matrix.trace (Yᴴ * Y)) := by
        exact hsNorm_sq_eq_re_trace_conjTranspose_mul_self Y
      _ = ∑ i, μ i := by
        rw [(Matrix.isHermitian_conjTranspose_mul_self Y).trace_eq_sum_eigenvalues]
        simp [μ]
  have hrhs_sq :
      (Real.sqrt (Fintype.card ι : ℝ) * hsNormOp Y) ^ 2 =
        (Fintype.card ι : ℝ) * ∑ i, μ i := by
    calc
      (Real.sqrt (Fintype.card ι : ℝ) * hsNormOp Y) ^ 2
        = (Real.sqrt (Fintype.card ι : ℝ)) ^ 2 * (hsNormOp Y) ^ 2 := by
            ring
      _ = (Fintype.card ι : ℝ) * ∑ i, μ i := by
            rw [Real.sq_sqrt (by positivity), hnorm_sq]
  have hsqineq :
      (∑ i, Real.sqrt (μ i)) ^ 2 ≤ (Real.sqrt (Fintype.card ι : ℝ) * hsNormOp Y) ^ 2 := by
    rw [hrhs_sq]
    exact hsum_sq
  have hleft : 0 ≤ ∑ i, Real.sqrt (μ i) := by
    exact Finset.sum_nonneg (fun i _ => Real.sqrt_nonneg _)
  have hright : 0 ≤ Real.sqrt (Fintype.card ι : ℝ) * hsNormOp Y := by
    exact mul_nonneg (Real.sqrt_nonneg _) (norm_nonneg _)
  have hle_abs : ∑ i, Real.sqrt (μ i) ≤ |Real.sqrt (Fintype.card ι : ℝ) * hsNormOp Y| := by
    simpa [abs_of_nonneg hleft] using (sq_le_sq.mp hsqineq)
  calc
    traceNormOp Y = ∑ i, Real.sqrt (μ i) := by
      rfl
    _ ≤ |Real.sqrt (Fintype.card ι : ℝ) * hsNormOp Y| := hle_abs
    _ = Real.sqrt (Fintype.card ι : ℝ) * hsNormOp Y := abs_of_nonneg hright
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
