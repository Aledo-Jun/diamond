# Operator

## Source location

- Original Lean file: `Diamond/Setups.lean`
- Declaration name: `Operator`
- Declaration kind: `abbrev`

## Why this declaration exists

This abbreviation gives the project's basic notion of an operator: a square complex matrix indexed by a finite set. Almost every later declaration is built from this shorthand.

 In the file `Setups.lean`, it contributes to foundational objects and notational definitions for operators, channels, norms, and the maps studied in the paper. Later declarations use this name instead of repeatedly expanding the underlying matrix formula.

## Original code

```lean
abbrev Operator (d : Type u) [Fintype d] [DecidableEq d] := Matrix d d ℂ
```

## Line-by-line explanation

The explanation below follows the declaration one physical line at a time. For long proofs, some lines are tiny bookkeeping steps; those are still explained, but briefly.

1. Code:
```lean
abbrev Operator (d : Type u) [Fintype d] [DecidableEq d] := Matrix d d ℂ
```
This line starts the `Operator` declaration. Because it begins with `abbrev`, Lean now knows what kind of named object is being introduced. The bracketed assumptions tell Lean that the relevant index sets are finite and that equality of indices can be checked mechanically. The type information on this line explains what sort of mathematical object the declaration talks about.  `Matrix d d ℂ` means a square matrix with complex entries; the index type `d` tells Lean which rows and columns exist.  A bracket such as `[Fintype d]` tells Lean that the index set `d` is finite, so sums over all indices make sense.  A bracket such as `[DecidableEq d]` tells Lean that it can decide whether two indices are equal.

## Mathematical summary

In ordinary mathematical language, `Operator` is the project's formal Lean name for the object introduced in this declaration.

## Dependencies and downstream use

### Earlier declarations this depends on
- This declaration does not explicitly cite an earlier named declaration from the documented tree; it mostly uses Lean primitives or local algebraic steps.

### Later declarations that use this one
- [`Channel`](Channel.md) in `Setups.lean`
- [`tensorWithIdentity`](tensorWithIdentity.md) in `Setups.lean`

## Backlinks

- [Back to `INDEX.md`](../INDEX.md)
- [Back to the `Setups.lean` section in the index](../INDEX.md#diamond-setups-lean)
- [Next declaration in this file](Channel.md)