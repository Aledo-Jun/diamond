# norm_one_sub_ud_sum_eq_cot

## Source location

- Original Lean file: `Diamond/EndMatter/Eq7.lean`
- Declaration name: `norm_one_sub_ud_sum_eq_cot`
- Declaration kind: `theorem`

## Why this declaration exists

The one-dimensional phase sum evaluates to the cotangent expression in Eq. (7).

 In the file `EndMatter/Eq7.lean`, it contributes to the explicit witness construction used to prove the lower bound labelled Eq. (7). Later proofs call this result by name, so documenting it makes the larger argument readable as a mathematical chain rather than as opaque proof script.

## Original code

```lean
/-- The one-dimensional phase sum evaluates to the cotangent expression in Eq. (7). -/
theorem norm_one_sub_ud_sum_eq_cot (d : ℕ) [Fact (1 < d)] :
    (∑ k : Fin d, ‖1 - Ud d k k‖) = 2 * Real.cot (Real.pi / (2 * d)) := by
  calc
    (∑ k : Fin d, ‖1 - Ud d k k‖)
      = ∑ k : Fin d, 2 * Real.sin (Real.pi * (k : ℝ) / d) := by
          refine Finset.sum_congr rfl ?_
          intro k hk
          exact norm_one_sub_ud_eq_sin d k
    _ = ∑ k ∈ Finset.range d, 2 * Real.sin (Real.pi * k / d) := by
          simpa using (Fin.sum_univ_eq_sum_range (fun k => 2 * Real.sin (Real.pi * k / d)) d)
    _ = 2 * Real.cot (Real.pi / (2 * d)) := by
          have hd_pos : 0 < d := lt_trans Nat.zero_lt_one ‹Fact (1 < d)›.out
          have hd_eq : d = (d - 1) + 1 := by
            simpa [Nat.succ_eq_add_one, Nat.add_comm] using
              (Nat.succ_pred_eq_of_pos hd_pos).symm
          have hd_eqR : (((d - 1 : ℕ) : ℝ) + 1) = d := by
            exact_mod_cast hd_eq.symm
          rw [hd_eq, Finset.sum_range_succ']
          simp only [Nat.cast_add, Nat.cast_one, CharP.cast_eq_zero, mul_zero, zero_div,
            Real.sin_zero, add_zero]
          rw [hd_eqR]
          have hs2 :
              2 * (∑ k ∈ Finset.range (d - 1), Real.sin (Real.pi * (k + 1) / d)) =
                2 * Real.cot (Real.pi / (2 * d)) := by
            nlinarith [shifted_sine_sum_eq_cot d]
          simpa [Finset.mul_sum] using hs2
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
