# transpose_phiState_eq_swap

## Source location

- Original Lean file: `Diamond/EndMatter/Eq7.lean`
- Declaration name: `transpose_phiState_eq_swap`
- Declaration kind: `theorem`

## Why this declaration exists

The transposed maximally entangled state is the normalized swap operator.

 In the file `EndMatter/Eq7.lean`, it contributes to the explicit witness construction used to prove the lower bound labelled Eq. (7). Later proofs call this result by name, so documenting it makes the larger argument readable as a mathematical chain rather than as opaque proof script.

## Original code

```lean
/-- The transposed maximally entangled state is the normalized swap operator. -/
theorem transpose_phiState_eq_swap (d : ℕ) [Fact (1 < d)] :
    tensorWithIdentity (Fin d) (Fin d) (transposeMap (Fin d)) (phiState d) =
      (d : ℂ)⁻¹ • swapMatrix d := by
  ext i j
  rcases i with ⟨a, b⟩
  rcases j with ⟨c, e⟩
  simp [tensorWithIdentity, transposeMap, swapMatrix, phiState_apply, eq_comm, and_comm]
```

## Block-by-block explanation

The explanation below follows the declaration block by block. Each block groups a coherent piece of the definition or proof, so the mathematical structure is easier to see than in a strictly line-oriented reading.

1. Code:
```lean
/-- The transposed maximally entangled state is the normalized swap operator. -/
```
This is a Lean docstring. It is a human-written comment that tells readers what the declaration is meant to express before the formal code begins.

2. Code:
```lean
theorem transpose_phiState_eq_swap (d : ℕ) [Fact (1 < d)] :
```
This line starts the `transpose_phiState_eq_swap` declaration. Because it begins with `theorem`, Lean now knows what kind of named object is being introduced.

3. Code:
```lean
    tensorWithIdentity (Fin d) (Fin d) (transposeMap (Fin d)) (phiState d) =
```
This line is one local step in the declaration. It either refines the formula being defined or advances the proof by a small algebraic or logical move.

4. Code:
```lean
      (d : ℂ)⁻¹ • swapMatrix d := by
```
This line says that a proof script begins here. Everything indented underneath is a sequence of instructions that Lean will check step by step.  `Matrix d d ℂ` means a square matrix with complex entries; the index type `d` tells Lean which rows and columns exist.

5. Code:
```lean
  ext i j
```
This line invokes extensionality. To prove two maps or matrices are equal, Lean reduces the problem to checking their values entry by entry.

6. Code:
```lean
  rcases i with ⟨a, b⟩
```
This line is one local step in the declaration. It either refines the formula being defined or advances the proof by a small algebraic or logical move.

7. Code:
```lean
  rcases j with ⟨c, e⟩
```
This line is one local step in the declaration. It either refines the formula being defined or advances the proof by a small algebraic or logical move.

8. Code:
```lean
  simp [tensorWithIdentity, transposeMap, swapMatrix, phiState_apply, eq_comm, and_comm]
```
This line simplifies the goal using definitions and known equalities. `simpa` means that, after simplification, the desired statement matches a theorem Lean already has.

## Mathematical summary

Restated without Lean syntax, `transpose_phiState_eq_swap` is the theorem or lemma written above.

- State the desired identity or inequality in Lean’s syntax.
- Introduce temporary names and intermediate claims that organize the argument.
- Use rewriting, simplification, and earlier lemmas to reduce the goal to standard matrix or norm manipulations.
- Close the remaining algebraic or order-theoretic steps with Lean’s proof tactics.

## Dependencies and downstream use

### Earlier declarations this depends on
- [`transposeMap`](../../Setups/transposeMap.md) from `Setups.lean`
- [`tensorWithIdentity`](../../Setups/tensorWithIdentity.md) from `Setups.lean`
- [`swapMatrix`](../../PositiveGap/Lemma6/swapMatrix.md) from `PositiveGap/Lemma6.lean`
- [`phiState`](phiState.md) from `EndMatter/Eq7.lean`
- [`phiState_apply`](phiState_apply.md) from `EndMatter/Eq7.lean`

### Later declarations that use this one
- [`lambda_phiState_eq`](lambda_phiState_eq.md) in `EndMatter/Eq7.lean`

## Backlinks

- [Back to `INDEX.md`](../../INDEX.md)
- [Back to the `EndMatter/Eq7.lean` section in the index](../../INDEX.md#diamond-endmatter-eq7-lean)
- [Previous declaration in this file](phiState_apply.md)
- [Next declaration in this file](swapMatrix_mul_phase_apply.md)