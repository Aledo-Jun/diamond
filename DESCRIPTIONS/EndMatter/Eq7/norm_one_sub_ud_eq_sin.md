# norm_one_sub_ud_eq_sin

## Source location

- Original Lean file: `Diamond/EndMatter/Eq7.lean`
- Declaration name: `norm_one_sub_ud_eq_sin`
- Declaration kind: `theorem`

## Why this declaration exists

Each phase difference contributes the corresponding sine term.

 In the file `EndMatter/Eq7.lean`, it contributes to the explicit witness construction used to prove the lower bound labelled Eq. (7). Later proofs call this result by name, so documenting it makes the larger argument readable as a mathematical chain rather than as opaque proof script.

## Original code

```lean
/-- Each phase difference contributes the corresponding sine term. -/
theorem norm_one_sub_ud_eq_sin (d : ℕ) [Fact (1 < d)] (k : Fin d) :
    ‖1 - Ud d k k‖ = 2 * Real.sin (Real.pi * (k : ℝ) / d) := by
  have hd_pos : 0 < d := lt_trans Nat.zero_lt_one ‹Fact (1 < d)›.out
  have hnorm := Complex.norm_exp_I_mul_ofReal_sub_one ((2 * Real.pi * (k : ℝ)) / d)
  have hsin_nonneg : 0 ≤ Real.sin (Real.pi * (k : ℝ) / d) := by
    apply Real.sin_nonneg_of_nonneg_of_le_pi
    · positivity
    · have hk_lt : (k : ℝ) < d := by
        exact_mod_cast k.is_lt
      have hk_le : (k : ℝ) ≤ d := le_of_lt hk_lt
      have hd_posR : (0 : ℝ) < d := by
        exact_mod_cast hd_pos
      have hdiv_le : (k : ℝ) / d ≤ 1 := by
        rw [div_le_iff₀ hd_posR]
        linarith
      have harg_le : Real.pi * (k : ℝ) / d ≤ Real.pi := by
        have htmp : Real.pi * ((k : ℝ) / d) ≤ Real.pi := by
          nlinarith [Real.pi_pos, hdiv_le]
        simpa [div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using htmp
      exact harg_le
  calc
    ‖1 - Ud d k k‖ = ‖Ud d k k - 1‖ := by
      rw [norm_sub_rev]
    _ = ‖2 * Real.sin (((2 * Real.pi * (k : ℝ)) / d) / 2)‖ := by
      simpa [Ud, div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using hnorm
    _ = ‖2 * Real.sin (Real.pi * (k : ℝ) / d)‖ := by
      congr 2
      have hd_ne : (d : ℝ) ≠ 0 := by
        exact_mod_cast hd_pos.ne'
      field_simp [hd_ne]
    _ = 2 * Real.sin (Real.pi * (k : ℝ) / d) := by
      rw [Real.norm_eq_abs, abs_of_nonneg]
      exact mul_nonneg (by positivity) hsin_nonneg
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
