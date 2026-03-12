# lemma5

## Source location

- Original Lean file: `Diamond/PositiveGap/Lemma5.lean`
- Declaration name: `lemma5`
- Declaration kind: `theorem`

## Why this declaration exists

This lemma is the standard compatibility of vectorization with Kronecker products.

 In the file `PositiveGap/Lemma5.lean`, it contributes to the vectorization definition and its basic compatibility with Kronecker products. Later proofs call this result by name, so documenting it makes the larger argument readable as a mathematical chain rather than as opaque proof script.

## Original code

```lean
theorem lemma5 (d : ℕ)
    (M A N : Matrix (Fin d) (Fin d) ℂ) :
    (M ⊗ₖ N) *ᵥ vecKet d A = vecKet d (M * A * Nᵀ) := by
  change (M ⊗ₖ N) *ᵥ Matrix.vec Aᵀ = Matrix.vec ((M * A * Nᵀ)ᵀ)
  rw [Matrix.kronecker_mulVec_vec]
  simp [Matrix.transpose_mul, Matrix.mul_assoc]
```

## Line-by-line explanation

The explanation below follows the declaration one physical line at a time. For long proofs, some lines are tiny bookkeeping steps; those are still explained, but briefly.

1. Code:
```lean
theorem lemma5 (d : ℕ)
```
This line starts the `lemma5` declaration. Because it begins with `theorem`, Lean now knows what kind of named object is being introduced.

2. Code:
```lean
    (M A N : Matrix (Fin d) (Fin d) ℂ) :
```
This line is one local step in the declaration. It either refines the formula being defined or advances the proof by a small algebraic or logical move.  `Matrix d d ℂ` means a square matrix with complex entries; the index type `d` tells Lean which rows and columns exist.

3. Code:
```lean
    (M ⊗ₖ N) *ᵥ vecKet d A = vecKet d (M * A * Nᵀ) := by
```
This line says that a proof script begins here. Everything indented underneath is a sequence of instructions that Lean will check step by step.  The symbol `⊗ₖ` is the Kronecker (tensor) product of matrices.  The superscript `ᵀ` means ordinary transpose.

4. Code:
```lean
  change (M ⊗ₖ N) *ᵥ Matrix.vec Aᵀ = Matrix.vec ((M * A * Nᵀ)ᵀ)
```
This line replaces the current goal by a definitionally equal goal that is easier to manipulate.  The symbol `⊗ₖ` is the Kronecker (tensor) product of matrices.  The superscript `ᵀ` means ordinary transpose.

5. Code:
```lean
  rw [Matrix.kronecker_mulVec_vec]
```
This line uses rewriting. Lean replaces one expression by an equal expression using the lemmas listed in brackets.

6. Code:
```lean
  simp [Matrix.transpose_mul, Matrix.mul_assoc]
```
This line simplifies the goal using definitions and known equalities. `simpa` means that, after simplification, the desired statement matches a theorem Lean already has.

## Mathematical summary

Restated without Lean syntax, `lemma5` is the theorem or lemma written above.

- State the desired identity or inequality in Lean’s syntax.
- Introduce temporary names and intermediate claims that organize the argument.
- Use rewriting, simplification, and earlier lemmas to reduce the goal to standard matrix or norm manipulations.
- Close the remaining algebraic or order-theoretic steps with Lean’s proof tactics.

## Dependencies and downstream use

### Earlier declarations this depends on
- [`vecKet`](vecKet.md) from `PositiveGap/Lemma5.lean`

### Later declarations that use this one
- No later documented declaration mentions this name explicitly.

## Backlinks

- [Back to `INDEX.md`](../../INDEX.md)
- [Back to the `PositiveGap/Lemma5.lean` section in the index](../../INDEX.md#diamond-positivegap-lemma5-lean)
- [Previous declaration in this file](vecKet_apply.md)