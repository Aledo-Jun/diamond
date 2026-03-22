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

## Block-by-block explanation

The explanation below follows the declaration block by block. Each block groups a coherent piece of the definition or proof, so the mathematical structure is easier to see than in a strictly line-oriented reading.

1. Code:
```lean
/-- The effective message-space channel induced by encoder, `m` channel uses,
```
This is a Lean docstring. It is a human-written comment that tells readers what the declaration is meant to express before the formal code begins.

2. Code:
```lean
    and decoder. -/
```
This line is one local step in the declaration. It either refines the formula being defined or advances the proof by a small algebraic or logical move.

3. Code:
```lean
abbrev effectiveChannel
```
This line starts the `effectiveChannel` declaration. Because it begins with `abbrev`, Lean now knows what kind of named object is being introduced.

4. Code:
```lean
    {phys msg : Type u}
```
This line is one local step in the declaration. It either refines the formula being defined or advances the proof by a small algebraic or logical move.

5. Code:
```lean
    [Fintype phys] [DecidableEq phys] [Fintype msg] [DecidableEq msg]
```
This line is one local step in the declaration. It either refines the formula being defined or advances the proof by a small algebraic or logical move.  A bracket such as `[Fintype d]` tells Lean that the index set `d` is finite, so sums over all indices make sense.  A bracket such as `[DecidableEq d]` tells Lean that it can decide whether two indices are equal.

6. Code:
```lean
    (encoder : Superoperator msg phys)
```
This line is one local step in the declaration. It either refines the formula being defined or advances the proof by a small algebraic or logical move.

7. Code:
```lean
    (decoder : Superoperator phys msg)
```
This line is one local step in the declaration. It either refines the formula being defined or advances the proof by a small algebraic or logical move.

8. Code:
```lean
    (tensorPower : Channel phys) : Channel msg :=
```
This line is one local step in the declaration. It either refines the formula being defined or advances the proof by a small algebraic or logical move.  `Channel d` is an abbreviation for a complex-linear map from operators on `d` to operators on `d`.

9. Code:
```lean
  decoder.comp (tensorPower.comp encoder)
```
This line is one local step in the declaration. It either refines the formula being defined or advances the proof by a small algebraic or logical move.  `comp` means composition of maps: one map is applied after another.

## Mathematical summary

In ordinary mathematical language, `effectiveChannel` is the project's formal Lean name for the object introduced in this declaration.

## Dependencies and downstream use

### Earlier declarations this depends on
- [`Channel`](../../Setups/Channel.md) from `Setups.lean`
- [`Superoperator`](Superoperator.md) from `EndMatter/Corollary2.lean`

### Later declarations that use this one
- [`corollary2_linear_bound`](corollary2_linear_bound.md) in `EndMatter/Corollary2.lean`
- [`corollary2`](corollary2.md) in `EndMatter/Corollary2.lean`

## Backlinks

- [Back to `INDEX.md`](../../INDEX.md)
- [Back to the `EndMatter/Corollary2.lean` section in the index](../../INDEX.md#diamond-endmatter-corollary2-lean)
- [Previous declaration in this file](Superoperator.md)
- [Next declaration in this file](corollary2_linear_bound.md)