---
layout: default
---

# trace_Ud_eq_zero

## Source location

- Original Lean file: `Diamond/StandardFacts.lean`
- Declaration name: `trace_Ud_eq_zero`
- Declaration kind: `theorem`

## Why this declaration exists

This theorem proves the roots-of-unity trace identity for the phase unitary `U_d`. It is the Lean
formalization of the sentence in the end matter of `docs/diamond.md` saying that the diagonal phases
sum to zero.

## Current code

```lean
/-- The phase-unitary trace vanishes because it is the full sum of the nontrivial `d`th
roots of unity. This mirrors the end-matter proof in `diamond/docs/diamond.md`: rewrite
the trace as a geometric sum and apply the primitive-root vanishing identity. -/
theorem trace_Ud_eq_zero (d : ℕ) [Fact (1 < d)] :
    Matrix.trace (Ud d) = 0 := by
  have hd_ne_zero : d ≠ 0 := Nat.ne_of_gt (lt_trans Nat.zero_lt_one ‹Fact (1 < d)›.out)
  let ζ : ℂ := Complex.exp ((2 * Real.pi * Complex.I) / (d : ℂ))
  have hprim : IsPrimitiveRoot ζ d := by
    simpa [ζ] using Complex.isPrimitiveRoot_exp d hd_ne_zero
  have hpow :
      ∀ i : Fin d,
        Complex.exp ((2 * Real.pi * Complex.I * (i : ℂ)) / (d : ℂ)) = ζ ^ (i : ℕ) := by
    intro i
    calc
      Complex.exp ((2 * Real.pi * Complex.I * (i : ℂ)) / (d : ℂ))
        = Complex.exp (((i : ℕ) : ℂ) * ((2 * Real.pi * Complex.I) / (d : ℂ))) := by
            ring_nf
      _ = ζ ^ (i : ℕ) := by
            rw [Complex.exp_nat_mul]
  have htrace :
      Matrix.trace (Ud d) = ∑ i : Fin d, ζ ^ (i : ℕ) := by
    simp [Ud, Matrix.trace_diagonal, hpow]
  have hsum :
      (∑ i : Fin d, ζ ^ (i : ℕ)) = Finset.sum (Finset.range d) (fun i : ℕ => ζ ^ i) := by
    simpa using (Fin.sum_univ_eq_sum_range (fun i : ℕ => ζ ^ i) d)
  calc
    Matrix.trace (Ud d) = ∑ i : Fin d, ζ ^ (i : ℕ) := htrace
    _ = Finset.sum (Finset.range d) (fun i : ℕ => ζ ^ i) := hsum
    _ = 0 := by
          simpa using hprim.geom_sum_eq_zero ‹Fact (1 < d)›.out
```

## Mathematical summary

The proof has exactly the same structure as the paper:

1. Define the primitive root of unity `ζ = exp(2π i / d)`.
2. Rewrite each diagonal entry of `Ud d` as `ζ^i`.
3. Rewrite the trace as the full geometric sum `∑_{i=0}^{d-1} ζ^i`.
4. Apply the standard primitive-root identity saying that this sum is zero for `d > 1`.

## Dependencies and downstream use

### Earlier declarations this depends on
- [`Ud`](../Setups/Ud/) from `Setups.lean`

### Later declarations that use this one
- [`theorem_eq8`](../EndMatter/Eq8/theorem_eq8/) in `EndMatter/Eq8.lean`

## Backlinks

- [Back to `INDEX.md`](../INDEX/)
- [Back to the `StandardFacts.lean` section in the index](../INDEX/#diamond-standardfacts-lean)
- [Previous declaration in this file](unitary_channel_diamond_distance_eq_two_of_trace_zero/)
- [Next declaration in this file](exists_maximizing_state/)
