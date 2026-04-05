# traceNorm_apply_le_diamond

## Source location

- Original Lean file: `Diamond/StandardFacts.lean`
- Declaration name: `traceNorm_apply_le_diamond`
- Declaration kind: `theorem`

## Why this declaration exists

This theorem is the basic witness bound for the fixed-ancilla diamond norm.

For any particular density state `ρ`, the trace norm of `(Φ ⊗ id)(ρ)` must be bounded by the
supremum `diamondNormAt Φ`. The proof is no longer assumed as an axiom; it is carried out in
finite dimension using a Hilbert--Schmidt bound for `tensorWithIdentity` and the fact that density
states have Hilbert--Schmidt norm at most `1`.

## Current code

```lean
theorem traceNorm_apply_le_diamond
    {d : Type u} [Fintype d] [DecidableEq d] {k : Type u}
    [Fintype k] [DecidableEq k]
    (Φ : Channel d) (ρ : DensityState (d × k)) :
    traceNormOp (tensorWithIdentity d k Φ ρ.1) ≤ diamondNormAt (d := d) (k := k) Φ := by
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
