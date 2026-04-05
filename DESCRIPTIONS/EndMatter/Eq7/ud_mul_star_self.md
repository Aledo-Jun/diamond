---
layout: default
---

# ud_mul_star_self

## Source location

- Original Lean file: `Diamond/EndMatter/Eq7.lean`
- Declaration name: `ud_mul_star_self`
- Declaration kind: `theorem`

## Why this declaration exists

The phase diagonal has unit-modulus entries.

 In the file `EndMatter/Eq7.lean`, it contributes to the explicit witness construction used to prove the lower bound labelled Eq. (7). Later proofs call this result by name, so documenting it makes the larger argument readable as a mathematical chain rather than as opaque proof script.

## Original code

```lean
/-- The phase diagonal has unit-modulus entries. -/
theorem ud_mul_star_self (d : ℕ) [Fact (1 < d)] (b : Fin d) :
    Ud d b b * star (Ud d b b) = 1 := by
  have hd_pos : 0 < d := lt_trans Nat.zero_lt_one ‹Fact (1 < d)›.out
  have hd_ne : (d : ℂ) ≠ 0 := by
    exact_mod_cast hd_pos.ne'
  have hrew :
      Ud d b b = Complex.exp ((((2 * Real.pi * (b : ℝ)) / d : ℝ) : ℂ) * Complex.I) := by
    simp [Ud]
    congr 1
    field_simp [hd_ne]
  rw [hrew]
  change Complex.exp (↑((2 * Real.pi * ↑b) / d) * Complex.I) *
      (starRingEnd ℂ) (Complex.exp (↑((2 * Real.pi * ↑b) / d) * Complex.I)) = 1
  rw [Complex.mul_conj, Complex.normSq_eq_norm_sq, Complex.norm_exp_ofReal_mul_I]
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
