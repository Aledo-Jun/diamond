# phiState_isDensityState

## Source location

- Original Lean file: `Diamond/EndMatter/Eq7.lean`
- Declaration name: `phiState_isDensityState`
- Declaration kind: `theorem`

## Why this declaration exists

This theorem records a reusable fact named `phiState_isDensityState`. Its role is to make the later proof flow easier to state and reuse.

 In the file `EndMatter/Eq7.lean`, it contributes to the explicit witness construction used to prove the lower bound labelled Eq. (7). Later proofs call this result by name, so documenting it makes the larger argument readable as a mathematical chain rather than as opaque proof script.

## Original code

```lean
theorem phiState_isDensityState (d : ℕ) [Fact (1 < d)] :
    IsDensityState (phiState d) := by
  refine ⟨?_, phiState_trace d⟩
  simpa [phiState] using Matrix.posSemidef_vecMulVec_self_star (omegaVec d)
```

## Block-by-block explanation

The explanation below follows the declaration block by block. Each block groups a coherent piece of the definition or proof, so the mathematical structure is easier to see than in a strictly line-oriented reading.

1. Code:
```lean
theorem phiState_isDensityState (d : ℕ) [Fact (1 < d)] :
```
This line starts the `phiState_isDensityState` declaration. Because it begins with `theorem`, Lean now knows what kind of named object is being introduced.

2. Code:
```lean
    IsDensityState (phiState d) := by
```
This line says that a proof script begins here. Everything indented underneath is a sequence of instructions that Lean will check step by step.

3. Code:
```lean
  refine ⟨?_, phiState_trace d⟩
```
This line is a more controlled version of `apply`. It sets up the proof with a partly specified argument and leaves smaller goals to solve next.

4. Code:
```lean
  simpa [phiState] using Matrix.posSemidef_vecMulVec_self_star (omegaVec d)
```
This line simplifies the goal using definitions and known equalities. `simpa` means that, after simplification, the desired statement matches a theorem Lean already has.

## Mathematical summary

Restated without Lean syntax, `phiState_isDensityState` is the theorem or lemma written above.

- State the desired identity or inequality in Lean’s syntax.
- Introduce temporary names and intermediate claims that organize the argument.
- Use rewriting, simplification, and earlier lemmas to reduce the goal to standard matrix or norm manipulations.
- Close the remaining algebraic or order-theoretic steps with Lean’s proof tactics.

## Dependencies and downstream use

### Earlier declarations this depends on
- [`IsDensityState`](../../Setups/IsDensityState.md) from `Setups.lean`
- [`omegaVec`](omegaVec.md) from `EndMatter/Eq7.lean`
- [`phiState`](phiState.md) from `EndMatter/Eq7.lean`
- [`phiState_trace`](phiState_trace.md) from `EndMatter/Eq7.lean`

### Later declarations that use this one
- [`theorem_eq7_witness_bound`](theorem_eq7_witness_bound.md) in `EndMatter/Eq7.lean`

## Backlinks

- [Back to `INDEX.md`](../../INDEX.md)
- [Back to the `EndMatter/Eq7.lean` section in the index](../../INDEX.md#diamond-endmatter-eq7-lean)
- [Previous declaration in this file](phiState_trace.md)
- [Next declaration in this file](phiState_apply.md)