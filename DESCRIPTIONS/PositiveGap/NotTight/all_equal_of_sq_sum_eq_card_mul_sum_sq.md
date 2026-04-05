---
layout: default
---

# all_equal_of_sq_sum_eq_card_mul_sum_sq

## Source location

- Original Lean file: `Diamond/PositiveGap/NotTight.lean`
- Declaration name: `all_equal_of_sq_sum_eq_card_mul_sum_sq`
- Declaration kind: `lemma`

## Why this declaration exists

Equality in Cauchy--Schwarz for a finite real family forces all entries to be equal.

 In the file `PositiveGap/NotTight.lean`, it contributes to the finite-dimensional non-tightness argument and the equality-case analysis behind it. Later proofs call this result by name, so documenting it makes the larger argument readable as a mathematical chain rather than as opaque proof script.

## Original code

```lean
/-- Equality in Cauchy--Schwarz for a finite real family forces all entries to be equal. -/
private lemma all_equal_of_sq_sum_eq_card_mul_sum_sq
    {ι : Type u} [Fintype ι] [Nonempty ι] {a : ι → ℝ}
    (heq : (∑ i, a i) ^ 2 = (Fintype.card ι : ℝ) * ∑ i, (a i) ^ 2) :
    ∀ i j, a i = a j := by
  let avg : ℝ := (∑ i, a i) / (Fintype.card ι : ℝ)
  have hzero : ∑ i, (a i - avg) ^ 2 = 0 := by
    rw [sum_sq_sub_avg_eq]
    have hcard_ne : (Fintype.card ι : ℝ) ≠ 0 := by
      positivity
    have hdiv : (∑ i, a i) ^ 2 / (Fintype.card ι : ℝ) = ∑ i, (a i) ^ 2 := by
      exact (div_eq_iff hcard_ne).2 (by simpa [mul_comm] using heq)
    linarith
  have hsq_zero' := (Finset.sum_eq_zero_iff_of_nonneg (fun i hi => sq_nonneg _)).1 hzero
  intro i j
  have hi : a i = avg := by
    have hsq : (a i - avg) ^ 2 = 0 := hsq_zero' i (by simp)
    nlinarith
  have hj : a j = avg := by
    have hsq : (a j - avg) ^ 2 = 0 := hsq_zero' j (by simp)
    nlinarith
  linarith
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
