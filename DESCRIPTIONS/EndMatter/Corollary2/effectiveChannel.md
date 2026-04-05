# effectiveChannel

## Source location

- Original Lean file: `Diamond/EndMatter/Corollary2.lean`
- Declaration name: `effectiveChannel`
- Declaration kind: `abbrev`

## Why this declaration exists

This abbreviation composes encoder, channel uses, and decoder into the effective message-space channel seen by the code.

 In the file `EndMatter/Corollary2.lean`, it contributes to the coding-theoretic corollary stated in terms of encoder, decoder, and effective channel. Later declarations use this name instead of repeatedly expanding the underlying matrix formula.

## Original code

```lean
/-- The effective message-space channel induced by encoder, `m` channel uses,
    and decoder. -/
abbrev effectiveChannel
    {phys msg : Type u}
    [Fintype phys] [DecidableEq phys] [Fintype msg] [DecidableEq msg]
    (encoder : Superoperator msg phys)
    (decoder : Superoperator phys msg)
    (tensorPower : Channel phys) : Channel msg :=
  decoder.comp (tensorPower.comp encoder)
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
