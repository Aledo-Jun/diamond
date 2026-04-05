---
layout: default
---

# ud_add_eq_mul

## Source location

- Original Lean file: `Diamond/EndMatter/Eq7.lean`
- Declaration name: `ud_add_eq_mul`
- Declaration kind: `theorem`

## Why this declaration exists

The phase diagonal satisfies the expected addition law on `Fin d`.

 In the file `EndMatter/Eq7.lean`, it contributes to the explicit witness construction used to prove the lower bound labelled Eq. (7). Later proofs call this result by name, so documenting it makes the larger argument readable as a mathematical chain rather than as opaque proof script.

## Original code

```lean
/-- The phase diagonal satisfies the expected addition law on `Fin d`. -/
theorem ud_add_eq_mul (d : ℕ) [Fact (1 < d)] (a b : Fin d) :
    Ud d (a + b) (a + b) = Ud d a a * Ud d b b := by
  have hd_pos : 0 < d := lt_trans Nat.zero_lt_one ‹Fact (1 < d)›.out
  have hd_ne : (d : ℂ) ≠ 0 := by
    exact_mod_cast hd_pos.ne'
  let q : ℕ := ((a : ℕ) + (b : ℕ)) / d
  let A : ℂ := (2 * Real.pi * Complex.I * (a : ℂ)) / (d : ℂ)
  let B : ℂ := (2 * Real.pi * Complex.I * (b : ℂ)) / (d : ℂ)
  let Q : ℂ := (q : ℂ) * (2 * Real.pi * Complex.I)
  have hcast :
      (((a + b : Fin d) : ℕ) : ℂ) = (a : ℂ) + (b : ℂ) - (d : ℂ) * (q : ℂ) := by
    have hnat : ((a + b : Fin d) : ℕ) = (a : ℕ) + (b : ℕ) - d * q := by
      simp [Fin.val_add, Nat.mod_eq_sub_mul_div, q]
    have hle : d * q ≤ (a : ℕ) + (b : ℕ) := by
      dsimp [q]
      exact Nat.mul_div_le _ _
    calc
      (((a + b : Fin d) : ℕ) : ℂ)
          = (((a : ℕ) + (b : ℕ) - d * q : ℕ) : ℂ) := by
              exact congrArg (fun n : ℕ => (n : ℂ)) hnat
      _ = (a : ℂ) + (b : ℂ) - (d : ℂ) * (q : ℂ) := by
            norm_num [Nat.cast_sub hle, Nat.cast_add, Nat.cast_mul]
  have hexp :
      (2 * Real.pi * Complex.I * (((a + b : Fin d) : ℕ) : ℂ)) / (d : ℂ) = A + B - Q := by
    rw [hcast]
    dsimp [A, B, Q]
    field_simp [hd_ne]
  have hperiod : Complex.exp (-Q) = 1 := by
    dsimp [Q]
    have h :
        -(↑q * (2 * Real.pi * Complex.I)) =
          (((-(q : ℤ)) : ℂ) * (2 * Real.pi * Complex.I)) := by
      norm_num
    rw [h]
    simpa using (Complex.exp_int_mul_two_pi_mul_I (-(q : ℤ)))
  unfold Ud
  simp only [Matrix.diagonal_apply_eq]
  rw [hexp, sub_eq_add_neg, Complex.exp_add, Complex.exp_add, hperiod]
  simp [A, B, mul_assoc]
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
