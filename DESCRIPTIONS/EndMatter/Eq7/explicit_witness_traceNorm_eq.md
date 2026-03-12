# explicit_witness_traceNorm_eq

## Source location

- Original Lean file: `Diamond/EndMatter/Eq7.lean`
- Declaration name: `explicit_witness_traceNorm_eq`
- Declaration kind: `theorem`

## Why this declaration exists

Exact trace-norm value of the Eq. (7) witness.

 In the file `EndMatter/Eq7.lean`, it contributes to the explicit witness construction used to prove the lower bound labelled Eq. (7). Later proofs call this result by name, so documenting it makes the larger argument readable as a mathematical chain rather than as opaque proof script.

## Original code

```lean
/-- Exact trace-norm value of the Eq. (7) witness. -/
theorem explicit_witness_traceNorm_eq (d : ℕ) [Fact (1 < d)] :
    traceNormOp
      ((d : ℂ)⁻¹ •
        (swapMatrix d - swapMatrix d * ((Ud d)ᵀ ⊗ₖ star (Ud d)))) =
      2 * Real.cot (Real.pi / (2 * d)) := by
  rw [explicit_witness_traceNorm_eq_sum, norm_one_sub_ud_sum_eq_cot]
```

## Line-by-line explanation

The explanation below follows the declaration one physical line at a time. For long proofs, some lines are tiny bookkeeping steps; those are still explained, but briefly.

1. Code:
```lean
/-- Exact trace-norm value of the Eq. (7) witness. -/
```
This is a Lean docstring. It is a human-written comment that tells readers what the declaration is meant to express before the formal code begins.

2. Code:
```lean
theorem explicit_witness_traceNorm_eq (d : ℕ) [Fact (1 < d)] :
```
This line starts the `explicit_witness_traceNorm_eq` declaration. Because it begins with `theorem`, Lean now knows what kind of named object is being introduced.

3. Code:
```lean
    traceNormOp
```
This line is one local step in the declaration. It either refines the formula being defined or advances the proof by a small algebraic or logical move.

4. Code:
```lean
      ((d : ℂ)⁻¹ •
```
This line is one local step in the declaration. It either refines the formula being defined or advances the proof by a small algebraic or logical move.

5. Code:
```lean
        (swapMatrix d - swapMatrix d * ((Ud d)ᵀ ⊗ₖ star (Ud d)))) =
```
This line is one local step in the declaration. It either refines the formula being defined or advances the proof by a small algebraic or logical move.  `Matrix d d ℂ` means a square matrix with complex entries; the index type `d` tells Lean which rows and columns exist.  The symbol `⊗ₖ` is the Kronecker (tensor) product of matrices.  The superscript `ᵀ` means ordinary transpose.

6. Code:
```lean
      2 * Real.cot (Real.pi / (2 * d)) := by
```
This line says that a proof script begins here. Everything indented underneath is a sequence of instructions that Lean will check step by step.

7. Code:
```lean
  rw [explicit_witness_traceNorm_eq_sum, norm_one_sub_ud_sum_eq_cot]
```
This line uses rewriting. Lean replaces one expression by an equal expression using the lemmas listed in brackets.

## Mathematical summary

Restated without Lean syntax, `explicit_witness_traceNorm_eq` is the theorem or lemma written above.

- State the desired identity or inequality in Lean’s syntax.
- Introduce temporary names and intermediate claims that organize the argument.
- Use rewriting, simplification, and earlier lemmas to reduce the goal to standard matrix or norm manipulations.
- Close the remaining algebraic or order-theoretic steps with Lean’s proof tactics.

## Dependencies and downstream use

### Earlier declarations this depends on
- [`traceNormOp`](../../Setups/traceNormOp.md) from `Setups.lean`
- [`Ud`](../../Setups/Ud.md) from `Setups.lean`
- [`swapMatrix`](../../PositiveGap/Lemma6/swapMatrix.md) from `PositiveGap/Lemma6.lean`
- [`explicit_witness_traceNorm_eq_sum`](explicit_witness_traceNorm_eq_sum.md) from `EndMatter/Eq7.lean`
- [`norm_one_sub_ud_sum_eq_cot`](norm_one_sub_ud_sum_eq_cot.md) from `EndMatter/Eq7.lean`

### Later declarations that use this one
- [`theorem_eq7`](theorem_eq7.md) in `EndMatter/Eq7.lean`

## Backlinks

- [Back to `INDEX.md`](../../INDEX.md)
- [Back to the `EndMatter/Eq7.lean` section in the index](../../INDEX.md#diamond-endmatter-eq7-lean)
- [Previous declaration in this file](norm_one_sub_ud_sum_eq_cot.md)
- [Next declaration in this file](theorem_eq7.md)