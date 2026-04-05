# swapMatrix_conjTranspose

## Source location

- Original Lean file: `Diamond/PositiveGap/Lemma6.lean`
- Declaration name: `swapMatrix_conjTranspose`
- Declaration kind: `theorem`

## Why this declaration exists

This theorem records a reusable fact named `swapMatrix_conjTranspose`. Its role is to make the later proof flow easier to state and reuse.

 In the file `PositiveGap/Lemma6.lean`, it contributes to the swap operator and its algebraic interaction with tensor products. Later proofs call this result by name, so documenting it makes the larger argument readable as a mathematical chain rather than as opaque proof script.

## Original code

```lean
theorem swapMatrix_conjTranspose (d : ℕ) :
    (swapMatrix d)ᴴ = swapMatrix d := by
  ext i j
  by_cases h : i.1 = j.2 ∧ i.2 = j.1
  · rcases h with ⟨h1, h2⟩
    have h' : j.1 = i.2 ∧ j.2 = i.1 := ⟨h2.symm, h1.symm⟩
    change
      star (if j.1 = i.2 ∧ j.2 = i.1 then (1 : ℂ) else 0) =
        if i.1 = j.2 ∧ i.2 = j.1 then (1 : ℂ) else 0
    simp only [if_pos h', if_pos (And.intro h1 h2), star_one]
  · have h' : ¬ (j.1 = i.2 ∧ j.2 = i.1) := by
      intro hji
      apply h
      exact ⟨hji.2.symm, hji.1.symm⟩
    change
      star (if j.1 = i.2 ∧ j.2 = i.1 then (1 : ℂ) else 0) =
        if i.1 = j.2 ∧ i.2 = j.1 then (1 : ℂ) else 0
    simp only [if_neg h', if_neg h, star_zero]
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
