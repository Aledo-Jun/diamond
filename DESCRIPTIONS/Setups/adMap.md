# adMap

## Source location

- Original Lean file: `Diamond/Setups.lean`
- Declaration name: `adMap`
- Declaration kind: `def`

## Why this declaration exists

This definition packages unitary conjugation $X \mapsto UXU^\dagger$ as a channel.

 In the file `Setups.lean`, it contributes to foundational objects and notational definitions for operators, channels, norms, and the maps studied in the paper. Later declarations use this name instead of repeatedly expanding the underlying matrix formula.

## Original code

```lean
/-- Unitary conjugation. -/
def adMap (d : Type u) [Fintype d] [DecidableEq d]
    (U : Matrix d d ℂ) : Channel d where
  toFun := fun X => U * X * Uᴴ
  map_add' := by
    intro X Y
    simp [Matrix.mul_add, Matrix.add_mul, Matrix.mul_assoc]
  map_smul' := by
    intro c X
    simp [Matrix.mul_assoc]
```

## Block-by-block explanation

The explanation below follows the declaration block by block. Each block groups a coherent piece of the definition or proof, so the mathematical structure is easier to see than in a strictly line-oriented reading.

1. Code:
```lean
/-- Unitary conjugation. -/
```
This is a Lean docstring. It is a human-written comment that tells readers what the declaration is meant to express before the formal code begins.

2. Code:
```lean
def adMap (d : Type u) [Fintype d] [DecidableEq d]
```
This line starts the `adMap` declaration. Because it begins with `def`, Lean now knows what kind of named object is being introduced. The bracketed assumptions tell Lean that the relevant index sets are finite and that equality of indices can be checked mechanically.  A bracket such as `[Fintype d]` tells Lean that the index set `d` is finite, so sums over all indices make sense.  A bracket such as `[DecidableEq d]` tells Lean that it can decide whether two indices are equal.

3. Code:
```lean
    (U : Matrix d d ℂ) : Channel d where
```
This line starts a `where` block. In Lean, a `where` block lists the fields of a structure or bundled map.

4. Code:
```lean
  toFun := fun X => U * X * Uᴴ
```
This line is one local step in the declaration. It either refines the formula being defined or advances the proof by a small algebraic or logical move.  The superscript `ᴴ` means conjugate transpose (also called the adjoint).

5. Code:
```lean
  map_add' := by
```
This line says that a proof script begins here. Everything indented underneath is a sequence of instructions that Lean will check step by step.

6. Code:
```lean
    intro X Y
```
This line introduces the variable or hypothesis named here into the proof context. In ordinary mathematical prose, it is the same as saying “let” or “assume”.

7. Code:
```lean
    simp [Matrix.mul_add, Matrix.add_mul, Matrix.mul_assoc]
```
This line simplifies the goal using definitions and known equalities. `simpa` means that, after simplification, the desired statement matches a theorem Lean already has.

8. Code:
```lean
  map_smul' := by
```
This line says that a proof script begins here. Everything indented underneath is a sequence of instructions that Lean will check step by step.

9. Code:
```lean
    intro c X
```
This line introduces the variable or hypothesis named here into the proof context. In ordinary mathematical prose, it is the same as saying “let” or “assume”.

10. Code:
```lean
    simp [Matrix.mul_assoc]
```
This line simplifies the goal using definitions and known equalities. `simpa` means that, after simplification, the desired statement matches a theorem Lean already has.

## Mathematical summary

In ordinary mathematical language, `adMap` is the project's formal Lean name for the object introduced in this declaration.

## Dependencies and downstream use

### Earlier declarations this depends on
- [`Channel`](Channel.md) from `Setups.lean`

### Later declarations that use this one
- [`Lambda`](Lambda.md) in `Setups.lean`
- [`adMap_isQuantumChannel`](../StandardFacts/adMap_isQuantumChannel.md) in `StandardFacts.lean`
- [`unitary_channel_diamond_distance_eq_two_of_trace_zero`](../StandardFacts/unitary_channel_diamond_distance_eq_two_of_trace_zero.md) in `StandardFacts.lean`
- [`transpose_ad_phiState_eq_swap_mul_phase`](../EndMatter/Eq7/transpose_ad_phiState_eq_swap_mul_phase.md) in `EndMatter/Eq7.lean`
- [`lambda_phiState_eq`](../EndMatter/Eq7/lambda_phiState_eq.md) in `EndMatter/Eq7.lean`
- [`theorem_eq8`](../EndMatter/Eq8/theorem_eq8.md) in `EndMatter/Eq8.lean`
- [`alpha_lower_bound`](../EndMatter/Eq8/alpha_lower_bound.md) in `EndMatter/Eq8.lean`

## Backlinks

- [Back to `INDEX.md`](../INDEX.md)
- [Back to the `Setups.lean` section in the index](../INDEX.md#diamond-setups-lean)
- [Previous declaration in this file](idMinus.md)
- [Next declaration in this file](Ud.md)