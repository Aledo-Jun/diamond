# Superoperator

## Source location

- Original Lean file: `Diamond/HolevoWerner/Common.lean`
- Declaration name: `Superoperator`
- Declaration kind: `abbrev`

## Why this declaration exists

This abbreviation provides a two-space version of the channel API so that the coding theorems can mention encoder and decoder explicitly.

It now lives in the shared `HolevoWerner/Common` layer rather than in the endmatter file itself. The corollary pages still reference it because it is part of the common coding vocabulary used by the later `HolevoWerner` and `Corollary2` statements.

## Original code

```lean
/-- A finite-dimensional superoperator between possibly different input/output spaces. -/
abbrev Superoperator
    (din dout : Type u) [Fintype din] [DecidableEq din] [Fintype dout] [DecidableEq dout] :=
  Matrix din din ℂ →ₗ[ℂ] Matrix dout dout ℂ
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
