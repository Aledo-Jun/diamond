---
layout: default
---

# corollary1

## Source location

- Original Lean file: `Diamond/PositiveGap/Corollary1.lean`
- Declaration name: `corollary1`
- Declaration kind: `theorem`

## Why this declaration exists

This corollary applies Lemma 4 to the difference map `idMinus T` and gets a vanishing partial trace.

 In the file `PositiveGap/Corollary1.lean`, it contributes to the immediate zero-partial-trace consequence for `idMinus T`. Later proofs call this result by name, so documenting it makes the larger argument readable as a mathematical chain rather than as opaque proof script.

## Original code

```lean
/-- Paper Corollary 1. -/
theorem corollary1
    {d : Type u} [Fintype d] [DecidableEq d]
    (T : Channel d) (hT : IsQuantumChannel T)
    (ρ : Matrix (d × d) (d × d) ℂ) :
    partialTraceLeft d d (tensorWithIdentity d d (idMinus T) ρ) = 0 := by
  ext i j
  calc
    partialTraceLeft d d (tensorWithIdentity d d (idMinus T) ρ) i j
      = partialTraceLeft d d ρ i j -
          partialTraceLeft d d (tensorWithIdentity d d T ρ) i j := by
            simp [partialTraceLeft, tensorWithIdentity, idMinus, Finset.sum_sub_distrib]
    _ = 0 := by
          rw [lemma4 T hT ρ]
          ring
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
