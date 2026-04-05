---
layout: default
---

# sq_sum_expand_offDiag

## Source location

- Original Lean file: `Diamond/PositiveGap/NotTight.lean`
- Declaration name: `sq_sum_expand_offDiag`
- Declaration kind: `lemma`

## Why this declaration exists

Expand a square of a finite sum into diagonal and off-diagonal parts.

 In the file `PositiveGap/NotTight.lean`, it contributes to the finite-dimensional non-tightness argument and the equality-case analysis behind it. Later proofs call this result by name, so documenting it makes the larger argument readable as a mathematical chain rather than as opaque proof script.

## Original code

```lean
/-- Expand a square of a finite sum into diagonal and off-diagonal parts. -/
private lemma sq_sum_expand_offDiag
    {ι : Type u} [Fintype ι] (p : ι → ℝ) :
    (∑ i, p i) ^ 2 =
      (∑ i, (p i) ^ 2) + ∑ x ∈ (Finset.univ : Finset ι).offDiag, p x.1 * p x.2 := by
  classical
  calc
    (∑ i, p i) ^ 2 = (∑ i, p i) * (∑ j, p j) := by
      ring
    _ = ∑ x ∈ ((Finset.univ : Finset ι) ×ˢ (Finset.univ : Finset ι)), p x.1 * p x.2 := by
      calc
        (∑ i, p i) * (∑ j, p j) = ∑ i, ∑ j, p i * p j := by
          simpa using (Fintype.sum_mul_sum p p)
        _ = ∑ x ∈ ((Finset.univ : Finset ι) ×ˢ (Finset.univ : Finset ι)), p x.1 * p x.2 := by
          rw [← Finset.sum_product']
    _ = ∑ x ∈ (Finset.univ : Finset ι).diag ∪ (Finset.univ : Finset ι).offDiag,
          p x.1 * p x.2 := by
      rw [← Finset.diag_union_offDiag]
    _ = (∑ x ∈ (Finset.univ : Finset ι).diag, p x.1 * p x.2) +
          ∑ x ∈ (Finset.univ : Finset ι).offDiag, p x.1 * p x.2 := by
      rw [Finset.sum_union (Finset.disjoint_diag_offDiag (s := (Finset.univ : Finset ι)))]
    _ = (∑ i, (p i) ^ 2) + ∑ x ∈ (Finset.univ : Finset ι).offDiag, p x.1 * p x.2 := by
      rw [Finset.sum_diag]
      simp [pow_two]
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
