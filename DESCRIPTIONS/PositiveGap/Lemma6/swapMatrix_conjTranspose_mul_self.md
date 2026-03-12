# swapMatrix_conjTranspose_mul_self

## Source location

- Original Lean file: `Diamond/PositiveGap/Lemma6.lean`
- Declaration name: `swapMatrix_conjTranspose_mul_self`
- Declaration kind: `theorem`

## Why this declaration exists

This theorem records a reusable fact named `swapMatrix_conjTranspose_mul_self`. Its role is to make the later proof flow easier to state and reuse.

 In the file `PositiveGap/Lemma6.lean`, it contributes to the swap operator and its algebraic interaction with tensor products. Later proofs call this result by name, so documenting it makes the larger argument readable as a mathematical chain rather than as opaque proof script.

## Original code

```lean
theorem swapMatrix_conjTranspose_mul_self (d : ℕ) :
    (swapMatrix d)ᴴ * swapMatrix d = 1 := by
  rw [swapMatrix_conjTranspose, swapMatrix_mul_self]

-- Paper: Lemma 6
```

## Line-by-line explanation

The explanation below follows the declaration one physical line at a time. For long proofs, some lines are tiny bookkeeping steps; those are still explained, but briefly.

1. Code:
```lean
theorem swapMatrix_conjTranspose_mul_self (d : ℕ) :
```
This line starts the `swapMatrix_conjTranspose_mul_self` declaration. Because it begins with `theorem`, Lean now knows what kind of named object is being introduced.

2. Code:
```lean
    (swapMatrix d)ᴴ * swapMatrix d = 1 := by
```
This line says that a proof script begins here. Everything indented underneath is a sequence of instructions that Lean will check step by step.  `Matrix d d ℂ` means a square matrix with complex entries; the index type `d` tells Lean which rows and columns exist.  The superscript `ᴴ` means conjugate transpose (also called the adjoint).

3. Code:
```lean
  rw [swapMatrix_conjTranspose, swapMatrix_mul_self]
```
This line uses rewriting. Lean replaces one expression by an equal expression using the lemmas listed in brackets.

4. Code:
```lean
-- Paper: Lemma 6
```
This line is one local step in the declaration. It either refines the formula being defined or advances the proof by a small algebraic or logical move.

## Mathematical summary

Restated without Lean syntax, `swapMatrix_conjTranspose_mul_self` is the theorem or lemma written above.

- State the desired identity or inequality in Lean’s syntax.
- Introduce temporary names and intermediate claims that organize the argument.
- Use rewriting, simplification, and earlier lemmas to reduce the goal to standard matrix or norm manipulations.
- Close the remaining algebraic or order-theoretic steps with Lean’s proof tactics.

## Dependencies and downstream use

### Earlier declarations this depends on
- [`swapMatrix`](swapMatrix.md) from `PositiveGap/Lemma6.lean`
- [`swapMatrix_mul_self`](swapMatrix_mul_self.md) from `PositiveGap/Lemma6.lean`
- [`swapMatrix_conjTranspose`](swapMatrix_conjTranspose.md) from `PositiveGap/Lemma6.lean`

### Later declarations that use this one
- [`explicit_witness_traceNorm_eq_sum`](../../EndMatter/Eq7/explicit_witness_traceNorm_eq_sum.md) in `EndMatter/Eq7.lean`

## Backlinks

- [Back to `INDEX.md`](../../INDEX.md)
- [Back to the `PositiveGap/Lemma6.lean` section in the index](../../INDEX.md#diamond-positivegap-lemma6-lean)
- [Previous declaration in this file](swapMatrix_conjTranspose.md)
- [Next declaration in this file](lemma6.md)