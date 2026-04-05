---
layout: default
---

# sum_sq_sub_avg_eq

## Source location

- Original Lean file: `Diamond/PositiveGap/NotTight.lean`
- Declaration name: `sum_sq_sub_avg_eq`
- Declaration kind: `lemma`

## Why this declaration exists

The sum of squared deviations from the average.

 In the file `PositiveGap/NotTight.lean`, it contributes to the finite-dimensional non-tightness argument and the equality-case analysis behind it. Later proofs call this result by name, so documenting it makes the larger argument readable as a mathematical chain rather than as opaque proof script.

## Original code

```lean
/-- The sum of squared deviations from the average. -/
private lemma sum_sq_sub_avg_eq
    {ι : Type u} [Fintype ι] [Nonempty ι] {a : ι → ℝ} :
    let avg : ℝ := (∑ i, a i) / (Fintype.card ι : ℝ)
    ∑ i, (a i - avg) ^ 2 =
      ∑ i, (a i) ^ 2 - (∑ i, a i) ^ 2 / (Fintype.card ι : ℝ) := by
  let avg : ℝ := (∑ i, a i) / (Fintype.card ι : ℝ)
  calc
    ∑ i, (a i - avg) ^ 2 =
        ∑ i, (a i) ^ 2 - 2 * avg * ∑ i, a i + (Fintype.card ι : ℝ) * avg ^ 2 := by
          calc
            ∑ i, (a i - avg) ^ 2 = ∑ i, ((a i) ^ 2 - 2 * a i * avg + avg ^ 2) := by
              refine Finset.sum_congr rfl ?_
              intro i hi
              ring
            _ = ∑ i, (a i) ^ 2 - 2 * avg * ∑ i, a i + (Fintype.card ι : ℝ) * avg ^ 2 := by
              simp [Finset.sum_sub_distrib, Finset.sum_add_distrib, Finset.sum_mul,
                mul_comm, mul_left_comm]
    _ = ∑ i, (a i) ^ 2 - (∑ i, a i) ^ 2 / (Fintype.card ι : ℝ) := by
      simpa using (sum_sq_sub_avg_eq_aux (a := a))
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
