---
layout: default
---

# lemma7

## Source location

- Original Lean file: `Diamond/PositiveGap/Lemma7.lean`
- Declaration name: `lemma7`
- Declaration kind: `theorem`

## Why this declaration exists

This lemma rewrites partial transpose of a rank-one operator into the swap-matrix expression used later in the rank argument.

 In the file `PositiveGap/Lemma7.lean`, it contributes to the partial-transpose formula for rank-one operators written in vectorized form. Later proofs call this result by name, so documenting it makes the larger argument readable as a mathematical chain rather than as opaque proof script.

## Original code

```lean
theorem lemma7 (d : ℕ)
    (A B : Matrix (Fin d) (Fin d) ℂ) :
    tensorWithIdentity
        (Fin d)
        (Fin d)
        (transposeMap (Fin d))
        (Matrix.vecMulVec (vecKet d A) (star (vecKet d B))) =
      (((1 : Matrix (Fin d) (Fin d) ℂ) ⊗ₖ Aᵀ) * swapMatrix d) *
        ((1 : Matrix (Fin d) (Fin d) ℂ) ⊗ₖ B.map star) := by
  ext i j
  rcases i with ⟨p, i⟩
  rcases j with ⟨q, j⟩
  have hleft :
      tensorWithIdentity
          (Fin d)
          (Fin d)
          (transposeMap (Fin d))
          (Matrix.vecMulVec (vecKet d A) (star (vecKet d B)))
          (p, i)
          (q, j) =
        A q i * star (B p j) := by
    simp [tensorWithIdentity, transposeMap, Matrix.vecMulVec_apply, vecKet]
  have hright :
      ((((1 : Matrix (Fin d) (Fin d) ℂ) ⊗ₖ Aᵀ) * swapMatrix d) *
          ((1 : Matrix (Fin d) (Fin d) ℂ) ⊗ₖ B.map star))
          (p, i) (q, j) =
        A q i * star (B p j) := by
    rw [Matrix.mul_apply]
    rw [Finset.sum_eq_single (q, p)]
    · simp [oneKronecker_mul_swap_apply, Matrix.kroneckerMap_apply]
    · intro x _ hx
      by_cases hx1 : x.1 = q
      · by_cases hx2 : x.2 = p
        · apply (hx <| by ext <;> simp [hx1, hx2]).elim
        · have hleftzero :
              (((1 : Matrix (Fin d) (Fin d) ℂ) ⊗ₖ Aᵀ) * swapMatrix d) (p, i) x = 0 := by
            rw [oneKronecker_mul_swap_apply]
            simp [show ¬ p = x.2 by simpa [eq_comm] using hx2]
          simp [hleftzero, Matrix.kroneckerMap_apply, Matrix.one_apply, hx1]
      · have hrightzero :
            (((1 : Matrix (Fin d) (Fin d) ℂ) ⊗ₖ B.map star) x (q, j)) = 0 := by
          simp [Matrix.kroneckerMap_apply, hx1]
        rw [hrightzero]
        simp
    · intro hqp
      simp at hqp
  rw [hleft, hright]
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
