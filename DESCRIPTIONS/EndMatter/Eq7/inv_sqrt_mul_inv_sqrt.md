---
layout: default
---

# inv_sqrt_mul_inv_sqrt

## Source location

- Original Lean file: `Diamond/EndMatter/Eq7.lean`
- Declaration name: `inv_sqrt_mul_inv_sqrt`
- Declaration kind: `theorem`

## Why this declaration exists

This theorem records a reusable fact named `inv_sqrt_mul_inv_sqrt`. Its role is to make the later proof flow easier to state and reuse.

 In the file `EndMatter/Eq7.lean`, it contributes to the explicit witness construction used to prove the lower bound labelled Eq. (7). Later proofs call this result by name, so documenting it makes the larger argument readable as a mathematical chain rather than as opaque proof script.

## Original code

```lean
theorem inv_sqrt_mul_inv_sqrt (d : ℕ) [Fact (1 < d)] :
    ((Real.sqrt d : ℂ)⁻¹) * ((Real.sqrt d : ℂ)⁻¹) = (d : ℂ)⁻¹ := by
  have hd_pos_nat : 0 < d := lt_trans Nat.zero_lt_one ‹Fact (1 < d)›.out
  have hd_pos : (0 : ℝ) < d := by
    exact_mod_cast hd_pos_nat
  have hsqrt_neR : (Real.sqrt d : ℝ) ≠ 0 := by
    exact (Real.sqrt_ne_zero').2 hd_pos
  have hsqrt_ne : (Real.sqrt d : ℂ) ≠ 0 := by
    exact_mod_cast hsqrt_neR
  calc
    ((Real.sqrt d : ℂ)⁻¹) * ((Real.sqrt d : ℂ)⁻¹)
        = ((Real.sqrt d : ℂ) ^ 2)⁻¹ := by
          field_simp [hsqrt_ne]
    _ = (d : ℂ)⁻¹ := by
      congr 1
      exact_mod_cast Real.sq_sqrt (show 0 ≤ (d : ℝ) by positivity)
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
