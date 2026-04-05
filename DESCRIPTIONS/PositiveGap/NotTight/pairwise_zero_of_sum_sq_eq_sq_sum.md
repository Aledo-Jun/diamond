# pairwise_zero_of_sum_sq_eq_sq_sum

## Source location

- Original Lean file: `Diamond/PositiveGap/NotTight.lean`
- Declaration name: `pairwise_zero_of_sum_sq_eq_sq_sum`
- Declaration kind: `lemma`

## Why this declaration exists

Equality in `∑ p_i^2 ≤ (∑ p_i)^2` forces all mixed terms to vanish.

 In the file `PositiveGap/NotTight.lean`, it contributes to the finite-dimensional non-tightness argument and the equality-case analysis behind it. Later proofs call this result by name, so documenting it makes the larger argument readable as a mathematical chain rather than as opaque proof script.

## Original code

```lean
/-- Equality in `∑ p_i^2 ≤ (∑ p_i)^2` forces all mixed terms to vanish. -/
private lemma pairwise_zero_of_sum_sq_eq_sq_sum
    {ι : Type u} [Fintype ι] {p : ι → ℝ}
    (hp : ∀ i, 0 ≤ p i)
    (heq : (∑ i, (p i) ^ 2) = (∑ i, p i) ^ 2) :
    ∀ i j, i ≠ j → p i = 0 ∨ p j = 0 := by
  classical
  have hoffDiag_zero : ∑ x ∈ (Finset.univ : Finset ι).offDiag, p x.1 * p x.2 = 0 := by
    have hexpand := sq_sum_expand_offDiag p
    linarith
  have hpair_zero :
      ∀ x ∈ (Finset.univ : Finset ι).offDiag, p x.1 * p x.2 = 0 := by
    exact
      (Finset.sum_eq_zero_iff_of_nonneg
        (fun x hx => mul_nonneg (hp x.1) (hp x.2))).1 hoffDiag_zero
  intro i j hij
  have hmem : (i, j) ∈ (Finset.univ : Finset ι).offDiag := by
    exact Finset.mem_offDiag.2 ⟨Finset.mem_univ i, Finset.mem_univ j, hij⟩
  have hmul : p i * p j = 0 := hpair_zero (i, j) hmem
  by_cases hi : p i = 0
  · exact Or.inl hi
  · right
    exact mul_eq_zero.mp hmul |>.resolve_left hi
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
