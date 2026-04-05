---
layout: default
---

# shifted_sine_sum_eq_cot

## Source location

- Original Lean file: `Diamond/EndMatter/Eq7.lean`
- Declaration name: `shifted_sine_sum_eq_cot`
- Declaration kind: `theorem`

## Why this declaration exists

Telescoping evaluation of the shifted finite sine sum.

 In the file `EndMatter/Eq7.lean`, it contributes to the explicit witness construction used to prove the lower bound labelled Eq. (7). Later proofs call this result by name, so documenting it makes the larger argument readable as a mathematical chain rather than as opaque proof script.

## Original code

```lean
/-- Telescoping evaluation of the shifted finite sine sum. -/
theorem shifted_sine_sum_eq_cot (d : ℕ) [Fact (1 < d)] :
    (∑ k ∈ Finset.range (d - 1), Real.sin (Real.pi * (k + 1) / d)) =
      Real.cot (Real.pi / (2 * d)) := by
  have hd_pos : 0 < d := lt_trans Nat.zero_lt_one ‹Fact (1 < d)›.out
  have hd_ne : (d : ℝ) ≠ 0 := by
    exact_mod_cast hd_pos.ne'
  let g : ℕ → ℝ := fun k => Real.cos (Real.pi * (2 * k + 1) / (2 * d))
  have htel :
      (2 * Real.sin (Real.pi / (2 * d))) *
        (∑ k ∈ Finset.range (d - 1), Real.sin (Real.pi * (k + 1) / d)) =
      ∑ k ∈ Finset.range (d - 1), (g k - g (k + 1)) := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl ?_
    intro k hk
    dsimp [g]
    have h := Real.two_mul_sin_mul_sin (Real.pi / (2 * d)) (Real.pi * (k + 1) / d)
    have harg1 :
        Real.pi / (2 * d) - Real.pi * (k + 1) / d =
          -(Real.pi * (2 * k + 1) / (2 * d)) := by
      field_simp [hd_ne]
      ring
    have harg2 :
        Real.pi / (2 * d) + Real.pi * (k + 1) / d =
          Real.pi * (2 * ↑(k + 1) + 1) / (2 * d) := by
      field_simp [hd_ne]
      norm_num [Nat.cast_add, Nat.cast_mul]
      ring
    calc
      2 * Real.sin (Real.pi / (2 * d)) * Real.sin (Real.pi * (k + 1) / d)
        = Real.cos (Real.pi / (2 * d) - Real.pi * (k + 1) / d) -
            Real.cos (Real.pi / (2 * d) + Real.pi * (k + 1) / d) := h
      _ = Real.cos (Real.pi * (2 * k + 1) / (2 * d)) -
            Real.cos (Real.pi * (2 * ↑(k + 1) + 1) / (2 * d)) := by
            rw [harg1, Real.cos_neg, harg2]
  have hsum :
      ∑ k ∈ Finset.range (d - 1), (g k - g (k + 1)) = g 0 - g (d - 1) := by
    simpa using (Finset.sum_range_sub' g (d - 1))
  have hend : g 0 - g (d - 1) = 2 * Real.cos (Real.pi / (2 * d)) := by
    dsimp [g]
    have h0 : Real.pi * (2 * (0 : ℕ) + 1) / (2 * d) = Real.pi / (2 * d) := by
      ring
    have hd_le : 1 ≤ d := Nat.succ_le_of_lt hd_pos
    have harg : Real.pi * (2 * ↑(d - 1) + 1) / (2 * d) = Real.pi - Real.pi / (2 * d) := by
      field_simp [hd_ne]
      norm_num [Nat.cast_sub hd_le, Nat.cast_mul, Nat.cast_add]
      ring
    rw [h0, harg, Real.cos_pi_sub]
    ring
  have hsin_pos : 0 < Real.sin (Real.pi / (2 * d)) := by
    apply Real.sin_pos_of_pos_of_lt_pi
    · positivity
    · have hd_gt_one : (1 : ℝ) < d := by
        exact_mod_cast ‹Fact (1 < d)›.out
      have htwo_d_gt_one : (1 : ℝ) < 2 * d := by
        nlinarith
      have hpos : (0 : ℝ) < 2 * d := by
        positivity
      rw [div_lt_iff₀ hpos]
      nlinarith [Real.pi_pos, htwo_d_gt_one]
  have hmain :
      (2 * Real.sin (Real.pi / (2 * d))) *
        (∑ k ∈ Finset.range (d - 1), Real.sin (Real.pi * (k + 1) / d)) =
      2 * Real.cos (Real.pi / (2 * d)) := by
    rw [htel, hsum, hend]
  rw [Real.cot_eq_cos_div_sin]
  apply (eq_div_iff hsin_pos.ne').2
  nlinarith [hmain]
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
