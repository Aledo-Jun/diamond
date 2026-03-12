# vecKet

## Source location

- Original Lean file: `Diamond/PositiveGap/Lemma5.lean`
- Declaration name: `vecKet`
- Declaration kind: `def`

## Why this declaration exists

This definition introduces the project's vectorization map, turning a matrix into a bipartite vector.

 In the file `PositiveGap/Lemma5.lean`, it contributes to the vectorization definition and its basic compatibility with Kronecker products. Later declarations use this name instead of repeatedly expanding the underlying matrix formula.

## Original code

```lean
/-- Paper Definition 1: column-major vectorization with tensor indices ordered as in the paper. -/
def vecKet (d : ℕ) (A : Matrix (Fin d) (Fin d) ℂ) : Fin d × Fin d → ℂ :=
  Matrix.vec Aᵀ

@[simp]
```

## Line-by-line explanation

The explanation below follows the declaration one physical line at a time. For long proofs, some lines are tiny bookkeeping steps; those are still explained, but briefly.

1. Code:
```lean
/-- Paper Definition 1: column-major vectorization with tensor indices ordered as in the paper. -/
```
This is a Lean docstring. It is a human-written comment that tells readers what the declaration is meant to express before the formal code begins.

2. Code:
```lean
def vecKet (d : ℕ) (A : Matrix (Fin d) (Fin d) ℂ) : Fin d × Fin d → ℂ :=
```
This line starts the `vecKet` declaration. Because it begins with `def`, Lean now knows what kind of named object is being introduced. The type information on this line explains what sort of mathematical object the declaration talks about.  `Matrix d d ℂ` means a square matrix with complex entries; the index type `d` tells Lean which rows and columns exist.

3. Code:
```lean
  Matrix.vec Aᵀ
```
This line is one local step in the declaration. It either refines the formula being defined or advances the proof by a small algebraic or logical move.  The superscript `ᵀ` means ordinary transpose.

4. Code:
```lean
@[simp]
```
This line is one local step in the declaration. It either refines the formula being defined or advances the proof by a small algebraic or logical move.

## Mathematical summary

In ordinary mathematical language, `vecKet` is the project's formal Lean name for the object introduced in this declaration.

## Dependencies and downstream use

### Earlier declarations this depends on
- This declaration does not explicitly cite an earlier named declaration from the documented tree; it mostly uses Lean primitives or local algebraic steps.

### Later declarations that use this one
- [`vecKet_apply`](vecKet_apply.md) in `PositiveGap/Lemma5.lean`
- [`lemma5`](lemma5.md) in `PositiveGap/Lemma5.lean`
- [`lemma7`](../Lemma7/lemma7.md) in `PositiveGap/Lemma7.lean`

## Backlinks

- [Back to `INDEX.md`](../../INDEX.md)
- [Back to the `PositiveGap/Lemma5.lean` section in the index](../../INDEX.md#diamond-positivegap-lemma5-lean)
- [Next declaration in this file](vecKet_apply.md)