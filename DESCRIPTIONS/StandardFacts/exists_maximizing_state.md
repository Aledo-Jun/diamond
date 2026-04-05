# exists_maximizing_state

## Source location

- Original Lean file: `Diamond/StandardFacts.lean`
- Declaration name: `exists_maximizing_state`
- Declaration kind: `theorem`

## Why this declaration exists

This theorem packages the finite-dimensional attainment statement used in the non-tightness
argument.

It is now proved internally. The Lean proof avoids treating `traceNormOp` continuity as a black box
by maximizing a continuous real-valued pairing over the compact product of unitary matrices and
density states, then recovering the trace norm through the Hermitian variational formula added in
`StandardFacts.lean`.

## Current code

```lean
/-- Finite-dimensional attainment of the left-hand diamond norm in the positive-gap argument.
    This compactness/maximizer step is background to the paper's main flow. -/
theorem exists_maximizing_state
    {d : Type u} [Fintype d] [DecidableEq d] [Nonempty d]
    (T : Channel d) (hT : IsQuantumChannel T) (hΦ : idMinus T ≠ 0) :
    ∃ ρ : DensityState (d × d),
      traceNormOp
          (tensorWithIdentity d d ((transposeMap d).comp (idMinus T)) ρ.1) =
        diamondOp ((transposeMap d).comp (idMinus T)) ∧
      tensorWithIdentity d d (idMinus T) ρ.1 ≠ 0 := by
  ...
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
