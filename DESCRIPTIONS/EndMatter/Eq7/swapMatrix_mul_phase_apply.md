# swapMatrix_mul_phase_apply

## Source location

- Original Lean file: `Diamond/EndMatter/Eq7.lean`
- Declaration name: `swapMatrix_mul_phase_apply`
- Declaration kind: `theorem`

## Why this declaration exists

This theorem records a reusable fact named `swapMatrix_mul_phase_apply`. Its role is to make the later proof flow easier to state and reuse.

 In the file `EndMatter/Eq7.lean`, it contributes to the explicit witness construction used to prove the lower bound labelled Eq. (7). Later proofs call this result by name, so documenting it makes the larger argument readable as a mathematical chain rather than as opaque proof script.

## Original code

```lean
theorem swapMatrix_mul_phase_apply (d : ℕ) [Fact (1 < d)] (a b c e : Fin d) :
    (swapMatrix d * ((Ud d)ᵀ ⊗ₖ star (Ud d))) (a, b) (c, e) =
      if b = c ∧ a = e then Ud d b b * star (Ud d e e) else 0 := by
  classical
  rw [Matrix.mul_apply]
  rw [Finset.sum_eq_single (b, a)]
  · by_cases hae : a = e
    · simp [swapMatrix, Ud, Matrix.diagonal_apply, hae, and_comm]
    · have hea : ¬ e = a := by
        simpa [eq_comm] using hae
      simp [swapMatrix, Ud, Matrix.diagonal_apply, hae, hea, and_comm]
  · intro x _ hne
    have hswap : ¬ (a = x.2 ∧ b = x.1) := by
      intro hx
      apply hne
      ext <;> simp [hx.1, hx.2]
    simp [swapMatrix, hswap]
  · intro hba
    simp at hba
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
