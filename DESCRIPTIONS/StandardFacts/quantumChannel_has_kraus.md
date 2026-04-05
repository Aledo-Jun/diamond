---
layout: default
---

# quantumChannel_has_kraus

## Source location

- Original Lean file: `Diamond/StandardFacts.lean`
- Declaration name: `quantumChannel_has_kraus`
- Declaration kind: `theorem`

## Why this declaration exists

This theorem exposes the Kraus data stored inside the project’s current definition of
`IsQuantumChannel`.

After the channel structure was strengthened, Lean no longer needs an external Kraus-representation
axiom here. The theorem is now just the accessor that unwraps the witness already bundled with
`hT : IsQuantumChannel T`.

## Current code

```lean
/-- Background Kraus representation for finite-dimensional quantum channels. -/
theorem quantumChannel_has_kraus
    {d : Type u} [Fintype d] [DecidableEq d] {T : Channel d} :
    IsQuantumChannel T →
    ∃ (r : ℕ), ∃ (E : Fin r → Matrix d d ℂ),
      (∀ X, T X = ∑ i, E i * X * (E i)ᴴ) ∧
      (∑ i, (E i)ᴴ * E i = 1) := by
  intro hT
  exact hT.kraus
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
