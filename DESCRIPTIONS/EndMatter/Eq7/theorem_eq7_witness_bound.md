# theorem_eq7_witness_bound

## Source location

- Original Lean file: `Diamond/EndMatter/Eq7.lean`
- Declaration name: `theorem_eq7_witness_bound`
- Declaration kind: `theorem`

## Why this declaration exists

The witness-state reduction for the lower bound in Eq. (7).

 In the file `EndMatter/Eq7.lean`, it contributes to the explicit witness construction used to prove the lower bound labelled Eq. (7). Later proofs call this result by name, so documenting it makes the larger argument readable as a mathematical chain rather than as opaque proof script.

## Original code

```lean
/-- The witness-state reduction for the lower bound in Eq. (7). -/
theorem theorem_eq7_witness_bound (d : ℕ) [Fact (1 < d)] :
    traceNormOp
        ((tensorWithIdentity (Fin d) (Fin d) (Lambda d)) (phiState d)) ≤
      diamondOp (Lambda d) := by
  simpa [diamondOp] using
    traceNorm_apply_le_diamond (d := Fin d) (k := Fin d)
      (Φ := Lambda d)
      (ρ := ⟨phiState d, phiState_isDensityState d⟩)
```

## Block-by-block explanation

The explanation below follows the declaration block by block. Each block groups a coherent piece of the definition or proof, so the mathematical structure is easier to see than in a strictly line-oriented reading.

1. Code:
```lean
/-- The witness-state reduction for the lower bound in Eq. (7). -/
```
This is a Lean docstring. It is a human-written comment that tells readers what the declaration is meant to express before the formal code begins.

2. Code:
```lean
theorem theorem_eq7_witness_bound (d : ℕ) [Fact (1 < d)] :
```
This line starts the `theorem_eq7_witness_bound` declaration. Because it begins with `theorem`, Lean now knows what kind of named object is being introduced.

3. Code:
```lean
    traceNormOp
```
This line is one local step in the declaration. It either refines the formula being defined or advances the proof by a small algebraic or logical move.

4. Code:
```lean
        ((tensorWithIdentity (Fin d) (Fin d) (Lambda d)) (phiState d)) ≤
```
This line is one local step in the declaration. It either refines the formula being defined or advances the proof by a small algebraic or logical move.

5. Code:
```lean
      diamondOp (Lambda d) := by
```
This line says that a proof script begins here. Everything indented underneath is a sequence of instructions that Lean will check step by step.

6. Code:
```lean
  simpa [diamondOp] using
```
This line simplifies the goal using definitions and known equalities. `simpa` means that, after simplification, the desired statement matches a theorem Lean already has.

7. Code:
```lean
    traceNorm_apply_le_diamond (d := Fin d) (k := Fin d)
```
This line is one local step in the declaration. It either refines the formula being defined or advances the proof by a small algebraic or logical move.

8. Code:
```lean
      (Φ := Lambda d)
```
This line is one local step in the declaration. It either refines the formula being defined or advances the proof by a small algebraic or logical move.

9. Code:
```lean
      (ρ := ⟨phiState d, phiState_isDensityState d⟩)
```
This line is one local step in the declaration. It either refines the formula being defined or advances the proof by a small algebraic or logical move.

## Mathematical summary

Restated without Lean syntax, `theorem_eq7_witness_bound` is the theorem or lemma written above.

- State the desired identity or inequality in Lean’s syntax.
- Introduce temporary names and intermediate claims that organize the argument.
- Use rewriting, simplification, and earlier lemmas to reduce the goal to standard matrix or norm manipulations.
- Close the remaining algebraic or order-theoretic steps with Lean’s proof tactics.

## Dependencies and downstream use

### Earlier declarations this depends on
- [`traceNormOp`](../../Setups/traceNormOp.md) from `Setups.lean`
- [`tensorWithIdentity`](../../Setups/tensorWithIdentity.md) from `Setups.lean`
- [`diamondOp`](../../Setups/diamondOp.md) from `Setups.lean`
- [`Lambda`](../../Setups/Lambda.md) from `Setups.lean`
- [`traceNorm_apply_le_diamond`](../../StandardFacts/traceNorm_apply_le_diamond.md) from `StandardFacts.lean`
- [`phiState`](phiState.md) from `EndMatter/Eq7.lean`
- [`phiState_isDensityState`](phiState_isDensityState.md) from `EndMatter/Eq7.lean`

### Later declarations that use this one
- [`theorem_eq7_witness_bound_explicit`](theorem_eq7_witness_bound_explicit.md) in `EndMatter/Eq7.lean`

## Backlinks

- [Back to `INDEX.md`](../../INDEX.md)
- [Back to the `EndMatter/Eq7.lean` section in the index](../../INDEX.md#diamond-endmatter-eq7-lean)
- [Previous declaration in this file](lambda_phiState_eq.md)
- [Next declaration in this file](theorem_eq7_witness_bound_explicit.md)