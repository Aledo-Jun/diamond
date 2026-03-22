# theorem_eq7_witness_bound_explicit

## Source location

- Original Lean file: `Diamond/EndMatter/Eq7.lean`
- Declaration name: `theorem_eq7_witness_bound_explicit`
- Declaration kind: `theorem`

## Why this declaration exists

This theorem records a reusable fact named `theorem_eq7_witness_bound_explicit`. Its role is to make the later proof flow easier to state and reuse.

 In the file `EndMatter/Eq7.lean`, it contributes to the explicit witness construction used to prove the lower bound labelled Eq. (7). Later proofs call this result by name, so documenting it makes the larger argument readable as a mathematical chain rather than as opaque proof script.

## Original code

```lean
theorem theorem_eq7_witness_bound_explicit (d : ℕ) [Fact (1 < d)] :
    traceNormOp
        ((d : ℂ)⁻¹ •
          (swapMatrix d - swapMatrix d * ((Ud d)ᵀ ⊗ₖ star (Ud d)))) ≤
      diamondOp (Lambda d) := by
  simpa [lambda_phiState_eq] using theorem_eq7_witness_bound d
```

## Block-by-block explanation

The explanation below follows the declaration block by block. Each block groups a coherent piece of the definition or proof, so the mathematical structure is easier to see than in a strictly line-oriented reading.

1. Code:
```lean
theorem theorem_eq7_witness_bound_explicit (d : ℕ) [Fact (1 < d)] :
```
This line starts the `theorem_eq7_witness_bound_explicit` declaration. Because it begins with `theorem`, Lean now knows what kind of named object is being introduced.

2. Code:
```lean
    traceNormOp
```
This line is one local step in the declaration. It either refines the formula being defined or advances the proof by a small algebraic or logical move.

3. Code:
```lean
        ((d : ℂ)⁻¹ •
```
This line is one local step in the declaration. It either refines the formula being defined or advances the proof by a small algebraic or logical move.

4. Code:
```lean
          (swapMatrix d - swapMatrix d * ((Ud d)ᵀ ⊗ₖ star (Ud d)))) ≤
```
This line is one local step in the declaration. It either refines the formula being defined or advances the proof by a small algebraic or logical move.  `Matrix d d ℂ` means a square matrix with complex entries; the index type `d` tells Lean which rows and columns exist.  The symbol `⊗ₖ` is the Kronecker (tensor) product of matrices.  The superscript `ᵀ` means ordinary transpose.

5. Code:
```lean
      diamondOp (Lambda d) := by
```
This line says that a proof script begins here. Everything indented underneath is a sequence of instructions that Lean will check step by step.

6. Code:
```lean
  simpa [lambda_phiState_eq] using theorem_eq7_witness_bound d
```
This line simplifies the goal using definitions and known equalities. `simpa` means that, after simplification, the desired statement matches a theorem Lean already has.

## Mathematical summary

Restated without Lean syntax, `theorem_eq7_witness_bound_explicit` is the theorem or lemma written above.

- State the desired identity or inequality in Lean’s syntax.
- Introduce temporary names and intermediate claims that organize the argument.
- Use rewriting, simplification, and earlier lemmas to reduce the goal to standard matrix or norm manipulations.
- Close the remaining algebraic or order-theoretic steps with Lean’s proof tactics.

## Dependencies and downstream use

### Earlier declarations this depends on
- [`traceNormOp`](../../Setups/traceNormOp.md) from `Setups.lean`
- [`diamondOp`](../../Setups/diamondOp.md) from `Setups.lean`
- [`Ud`](../../Setups/Ud.md) from `Setups.lean`
- [`Lambda`](../../Setups/Lambda.md) from `Setups.lean`
- [`swapMatrix`](../../PositiveGap/Lemma6/swapMatrix.md) from `PositiveGap/Lemma6.lean`
- [`lambda_phiState_eq`](lambda_phiState_eq.md) from `EndMatter/Eq7.lean`
- [`theorem_eq7_witness_bound`](theorem_eq7_witness_bound.md) from `EndMatter/Eq7.lean`

### Later declarations that use this one
- [`theorem_eq7`](theorem_eq7.md) in `EndMatter/Eq7.lean`

## Backlinks

- [Back to `INDEX.md`](../../INDEX.md)
- [Back to the `EndMatter/Eq7.lean` section in the index](../../INDEX.md#diamond-endmatter-eq7-lean)
- [Previous declaration in this file](theorem_eq7_witness_bound.md)
- [Next declaration in this file](ud_add_eq_mul.md)