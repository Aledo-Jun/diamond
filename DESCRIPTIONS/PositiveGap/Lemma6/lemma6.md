# lemma6

## Source location

- Original Lean file: `Diamond/PositiveGap/Lemma6.lean`
- Declaration name: `lemma6`
- Declaration kind: `theorem`

## Why this declaration exists

This lemma proves the basic commutation rule between the swap operator and Kronecker products.

 In the file `PositiveGap/Lemma6.lean`, it contributes to the swap operator and its algebraic interaction with tensor products. Later proofs call this result by name, so documenting it makes the larger argument readable as a mathematical chain rather than as opaque proof script.

## Original code

```lean
theorem lemma6 (d : ℕ)
    (X Y : Matrix (Fin d) (Fin d) ℂ) :
    swapMatrix d * (X ⊗ₖ Y) = (Y ⊗ₖ X) * swapMatrix d := by
  ext i j
  rcases i with ⟨a, b⟩
  rcases j with ⟨c, e⟩
  have hleft :
      (swapMatrix d * (X ⊗ₖ Y)) (a, b) (c, e) = X b c * Y a e := by
    rw [Matrix.mul_apply]
    rw [Finset.sum_eq_single (b, a)]
    · simp [swapMatrix, Matrix.kroneckerMap_apply]
    · intro x _ hx
      have hzero : ¬ (a = x.2 ∧ b = x.1) := by
        intro h
        apply hx
        ext <;> simp [h.1, h.2]
      simp [swapMatrix, Matrix.kroneckerMap_apply, hzero]
    · intro hba
      simp at hba
  have hright :
      ((Y ⊗ₖ X) * swapMatrix d) (a, b) (c, e) = Y a e * X b c := by
    rw [Matrix.mul_apply]
    rw [Finset.sum_eq_single (e, c)]
    · simp [swapMatrix, Matrix.kroneckerMap_apply]
    · intro x _ hx
      have hzero : ¬ (x.1 = e ∧ x.2 = c) := by
        intro h
        apply hx
        ext <;> simp [h.1, h.2]
      simp [swapMatrix, Matrix.kroneckerMap_apply, hzero]
    · intro hec
      simp at hec
  rw [hleft, hright, mul_comm]
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
