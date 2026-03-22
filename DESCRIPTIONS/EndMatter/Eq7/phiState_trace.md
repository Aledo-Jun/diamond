# phiState_trace

## Source location

- Original Lean file: `Diamond/EndMatter/Eq7.lean`
- Declaration name: `phiState_trace`
- Declaration kind: `theorem`

## Why this declaration exists

This theorem records a reusable fact named `phiState_trace`. Its role is to make the later proof flow easier to state and reuse.

 In the file `EndMatter/Eq7.lean`, it contributes to the explicit witness construction used to prove the lower bound labelled Eq. (7). Later proofs call this result by name, so documenting it makes the larger argument readable as a mathematical chain rather than as opaque proof script.

## Original code

```lean
theorem phiState_trace (d : ℕ) [Fact (1 < d)] :
    Matrix.trace (phiState d) = 1 := by
  rw [phiState, Matrix.trace_vecMulVec, dotProduct, Fintype.sum_prod_type]
  simp [omegaVec, inv_sqrt_mul_inv_sqrt]
```

## Block-by-block explanation

The explanation below follows the declaration block by block. Each block groups a coherent piece of the definition or proof, so the mathematical structure is easier to see than in a strictly line-oriented reading.

1. Code:
```lean
theorem phiState_trace (d : ℕ) [Fact (1 < d)] :
```
This line starts the `phiState_trace` declaration. Because it begins with `theorem`, Lean now knows what kind of named object is being introduced.

2. Code:
```lean
    Matrix.trace (phiState d) = 1 := by
```
This line says that a proof script begins here. Everything indented underneath is a sequence of instructions that Lean will check step by step.

3. Code:
```lean
  rw [phiState, Matrix.trace_vecMulVec, dotProduct, Fintype.sum_prod_type]
```
This line uses rewriting. Lean replaces one expression by an equal expression using the lemmas listed in brackets.

4. Code:
```lean
  simp [omegaVec, inv_sqrt_mul_inv_sqrt]
```
This line simplifies the goal using definitions and known equalities. `simpa` means that, after simplification, the desired statement matches a theorem Lean already has.

## Mathematical summary

Restated without Lean syntax, `phiState_trace` is the theorem or lemma written above.

- State the desired identity or inequality in Lean’s syntax.
- Introduce temporary names and intermediate claims that organize the argument.
- Use rewriting, simplification, and earlier lemmas to reduce the goal to standard matrix or norm manipulations.
- Close the remaining algebraic or order-theoretic steps with Lean’s proof tactics.

## Dependencies and downstream use

### Earlier declarations this depends on
- [`omegaVec`](omegaVec.md) from `EndMatter/Eq7.lean`
- [`phiState`](phiState.md) from `EndMatter/Eq7.lean`
- [`inv_sqrt_mul_inv_sqrt`](inv_sqrt_mul_inv_sqrt.md) from `EndMatter/Eq7.lean`

### Later declarations that use this one
- [`phiState_isDensityState`](phiState_isDensityState.md) in `EndMatter/Eq7.lean`

## Backlinks

- [Back to `INDEX.md`](../../INDEX.md)
- [Back to the `EndMatter/Eq7.lean` section in the index](../../INDEX.md#diamond-endmatter-eq7-lean)
- [Previous declaration in this file](inv_sqrt_mul_inv_sqrt.md)
- [Next declaration in this file](phiState_isDensityState.md)