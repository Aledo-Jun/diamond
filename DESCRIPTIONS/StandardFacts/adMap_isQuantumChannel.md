---
layout: default
---

# adMap_isQuantumChannel

## Source location

- Original Lean file: `Diamond/StandardFacts.lean`
- Declaration name: `adMap_isQuantumChannel`
- Declaration kind: `theorem`

## Why this declaration exists

Unitary conjugation is a quantum channel.

 In the file `StandardFacts.lean`, it contributes to helper facts and background reductions that later proofs use directly. Later proofs call this result by name, so documenting it makes the larger argument readable as a mathematical chain rather than as opaque proof script.

## Original code

```lean
/-- Unitary conjugation is a quantum channel. -/
theorem adMap_isQuantumChannel
    {d : Type u} [Fintype d] [DecidableEq d]
    (U : Matrix d d ℂ) (hU : Uᴴ * U = 1) :
    IsQuantumChannel (adMap d U) := by
  refine ⟨?_, ?_⟩
  · intro X
    calc
      Matrix.trace (adMap d U X) = Matrix.trace (U * X * Uᴴ) := by rfl
      _ = Matrix.trace ((Uᴴ * U) * X) := by
            simpa [Matrix.mul_assoc] using Matrix.trace_mul_cycle U X Uᴴ
      _ = Matrix.trace X := by simp [hU]
  · intro X
    simp [adMap, Matrix.conjTranspose_mul, Matrix.mul_assoc]

/-- Abstract pointwise-to-diamond reduction.

    This lemma states the standard `k = d` reduction used throughout the file. -/
-- Background functional-analytic fact (finite-dimensional attainment/compactness input).
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
