# omegaVec

## Source location

- Original Lean file: `Diamond/EndMatter/Eq7.lean`
- Declaration name: `omegaVec`
- Declaration kind: `def`

## Why this declaration exists

This definition introduces the maximally entangled vector used as the explicit witness for Eq. (7).

 In the file `EndMatter/Eq7.lean`, it contributes to the explicit witness construction used to prove the lower bound labelled Eq. (7). Later declarations use this name instead of repeatedly expanding the underlying matrix formula.

## Original code

```lean
/-- The maximally entangled vector used in the lower bound for Eq. (7). -/
def omegaVec (d : ℕ) : Fin d × Fin d → ℂ :=
  fun ij => if ij.1 = ij.2 then (Real.sqrt d : ℂ)⁻¹ else 0
```

## Block-by-block explanation

The explanation below follows the declaration block by block. Each block groups a coherent piece of the definition or proof, so the mathematical structure is easier to see than in a strictly line-oriented reading.

1. Code:
```lean
/-- The maximally entangled vector used in the lower bound for Eq. (7). -/
```
This is a Lean docstring. It is a human-written comment that tells readers what the declaration is meant to express before the formal code begins.

2. Code:
```lean
def omegaVec (d : ℕ) : Fin d × Fin d → ℂ :=
```
This line starts the `omegaVec` declaration. Because it begins with `def`, Lean now knows what kind of named object is being introduced.

3. Code:
```lean
  fun ij => if ij.1 = ij.2 then (Real.sqrt d : ℂ)⁻¹ else 0
```
This line is one local step in the declaration. It either refines the formula being defined or advances the proof by a small algebraic or logical move.

## Mathematical summary

In ordinary mathematical language, `omegaVec` is the project's formal Lean name for the object introduced in this declaration.

## Dependencies and downstream use

### Earlier declarations this depends on
- This declaration does not explicitly cite an earlier named declaration from the documented tree; it mostly uses Lean primitives or local algebraic steps.

### Later declarations that use this one
- [`phiState`](phiState.md) in `EndMatter/Eq7.lean`
- [`phiState_trace`](phiState_trace.md) in `EndMatter/Eq7.lean`
- [`phiState_isDensityState`](phiState_isDensityState.md) in `EndMatter/Eq7.lean`
- [`phiState_apply`](phiState_apply.md) in `EndMatter/Eq7.lean`

## Backlinks

- [Back to `INDEX.md`](../../INDEX.md)
- [Back to the `EndMatter/Eq7.lean` section in the index](../../INDEX.md#diamond-endmatter-eq7-lean)
- [Next declaration in this file](phiState.md)