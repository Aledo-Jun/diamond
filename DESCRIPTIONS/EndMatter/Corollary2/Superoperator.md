# Superoperator

## Source location

- Original Lean file: `Diamond/EndMatter/Corollary2.lean`
- Declaration name: `Superoperator`
- Declaration kind: `abbrev`

## Why this declaration exists

This abbreviation provides a two-space version of the channel API so that the coding corollary can mention encoder and decoder explicitly.

 In the file `EndMatter/Corollary2.lean`, it contributes to the coding-theoretic corollary stated in terms of encoder, decoder, and effective channel. Later declarations use this name instead of repeatedly expanding the underlying matrix formula.

## Original code

```lean
/-- A finite-dimensional superoperator between possibly different input/output spaces. -/
abbrev Superoperator
    (din dout : Type u) [Fintype din] [DecidableEq din] [Fintype dout] [DecidableEq dout] :=
  Matrix din din ℂ →ₗ[ℂ] Matrix dout dout ℂ
```

## Line-by-line explanation

The explanation below follows the declaration one physical line at a time. For long proofs, some lines are tiny bookkeeping steps; those are still explained, but briefly.

1. Code:
```lean
/-- A finite-dimensional superoperator between possibly different input/output spaces. -/
```
This is a Lean docstring. It is a human-written comment that tells readers what the declaration is meant to express before the formal code begins.

2. Code:
```lean
abbrev Superoperator
```
This line starts the `Superoperator` declaration. Because it begins with `abbrev`, Lean now knows what kind of named object is being introduced.

3. Code:
```lean
    (din dout : Type u) [Fintype din] [DecidableEq din] [Fintype dout] [DecidableEq dout] :=
```
This line is one local step in the declaration. It either refines the formula being defined or advances the proof by a small algebraic or logical move.  A bracket such as `[Fintype d]` tells Lean that the index set `d` is finite, so sums over all indices make sense.  A bracket such as `[DecidableEq d]` tells Lean that it can decide whether two indices are equal.

4. Code:
```lean
  Matrix din din ℂ →ₗ[ℂ] Matrix dout dout ℂ
```
This line is one local step in the declaration. It either refines the formula being defined or advances the proof by a small algebraic or logical move.  `Matrix d d ℂ` means a square matrix with complex entries; the index type `d` tells Lean which rows and columns exist.  The arrow `→ₗ[ℂ]` means “complex-linear map”.

## Mathematical summary

In ordinary mathematical language, `Superoperator` is the project's formal Lean name for the object introduced in this declaration.

## Dependencies and downstream use

### Earlier declarations this depends on
- This declaration does not explicitly cite an earlier named declaration from the documented tree; it mostly uses Lean primitives or local algebraic steps.

### Later declarations that use this one
- [`effectiveChannel`](effectiveChannel.md) in `EndMatter/Corollary2.lean`
- [`corollary2_linear_bound`](corollary2_linear_bound.md) in `EndMatter/Corollary2.lean`
- [`corollary2`](corollary2.md) in `EndMatter/Corollary2.lean`

## Backlinks

- [Back to `INDEX.md`](../../INDEX.md)
- [Back to the `EndMatter/Corollary2.lean` section in the index](../../INDEX.md#diamond-endmatter-corollary2-lean)
- [Next declaration in this file](effectiveChannel.md)