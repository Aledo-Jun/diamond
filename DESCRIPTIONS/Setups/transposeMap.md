# transposeMap

## Source location

- Original Lean file: `Diamond/Setups.lean`
- Declaration name: `transposeMap`
- Declaration kind: `def`

## Why this declaration exists

This is the transpose channel $\Theta$, one of the central maps in the paper.

 In the file `Setups.lean`, it contributes to foundational objects and notational definitions for operators, channels, norms, and the maps studied in the paper. Later declarations use this name instead of repeatedly expanding the underlying matrix formula.

## Original code

```lean
/-- Transposition. -/
def transposeMap (d : Type u) [Fintype d] [DecidableEq d] : Channel d where
  toFun := fun X => Xᵀ
  map_add' := by
    intro X Y
    ext i j
    simp
  map_smul' := by
    intro c X
    ext i j
    simp
```

## Block-by-block explanation

The explanation below follows the declaration block by block. Each block groups a coherent piece of the definition or proof, so the mathematical structure is easier to see than in a strictly line-oriented reading.

1. Code:
```lean
/-- Transposition. -/
```
This is a Lean docstring. It is a human-written comment that tells readers what the declaration is meant to express before the formal code begins.

2. Code:
```lean
def transposeMap (d : Type u) [Fintype d] [DecidableEq d] : Channel d where
```
This line starts the `transposeMap` declaration. Because it begins with `def`, Lean now knows what kind of named object is being introduced. The bracketed assumptions tell Lean that the relevant index sets are finite and that equality of indices can be checked mechanically. The type information on this line explains what sort of mathematical object the declaration talks about.  `Channel d` is an abbreviation for a complex-linear map from operators on `d` to operators on `d`.  A bracket such as `[Fintype d]` tells Lean that the index set `d` is finite, so sums over all indices make sense.  A bracket such as `[DecidableEq d]` tells Lean that it can decide whether two indices are equal.

3. Code:
```lean
  toFun := fun X => Xᵀ
```
This line is one local step in the declaration. It either refines the formula being defined or advances the proof by a small algebraic or logical move.  The superscript `ᵀ` means ordinary transpose.

4. Code:
```lean
  map_add' := by
```
This line says that a proof script begins here. Everything indented underneath is a sequence of instructions that Lean will check step by step.

5. Code:
```lean
    intro X Y
```
This line introduces the variable or hypothesis named here into the proof context. In ordinary mathematical prose, it is the same as saying “let” or “assume”.

6. Code:
```lean
    ext i j
```
This line invokes extensionality. To prove two maps or matrices are equal, Lean reduces the problem to checking their values entry by entry.

7. Code:
```lean
    simp
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
    ext i j
```
This line invokes extensionality. To prove two maps or matrices are equal, Lean reduces the problem to checking their values entry by entry.

11. Code:
```lean
    simp
```
This line simplifies the goal using definitions and known equalities. `simpa` means that, after simplification, the desired statement matches a theorem Lean already has.

## Mathematical summary

In ordinary mathematical language, `transposeMap` is the project's formal Lean name for the object introduced in this declaration.

## Dependencies and downstream use

### Earlier declarations this depends on
- [`Channel`](Channel.md) from `Setups.lean`

### Later declarations that use this one
- [`Lambda`](Lambda.md) in `Setups.lean`
- [`tensorWithIdentity_comp_transpose`](../StandardFacts/tensorWithIdentity_comp_transpose.md) in `StandardFacts.lean`
- [`lemma_transpose_diamond`](../StandardFacts/lemma_transpose_diamond.md) in `StandardFacts.lean`
- [`exists_maximizing_state`](../StandardFacts/exists_maximizing_state.md) in `StandardFacts.lean`
- [`theorem1`](../Theorem/Theorem1/theorem1.md) in `Theorem/Theorem1.lean`
- [`remark1`](../Theorem/Remark1/remark1.md) in `Theorem/Remark1.lean`
- [`lemma7`](../PositiveGap/Lemma7/lemma7.md) in `PositiveGap/Lemma7.lean`
- [`theorem_not_tight`](../PositiveGap/NotTight/theorem_not_tight.md) in `PositiveGap/NotTight.lean`
- [`transpose_phiState_eq_swap`](../EndMatter/Eq7/transpose_phiState_eq_swap.md) in `EndMatter/Eq7.lean`
- [`transpose_ad_phiState_eq_swap_mul_phase`](../EndMatter/Eq7/transpose_ad_phiState_eq_swap_mul_phase.md) in `EndMatter/Eq7.lean`
- [`lambda_phiState_eq`](../EndMatter/Eq7/lambda_phiState_eq.md) in `EndMatter/Eq7.lean`
- [`alpha_lower_bound`](../EndMatter/Eq8/alpha_lower_bound.md) in `EndMatter/Eq8.lean`
- [`corollary2_linear_bound`](../EndMatter/Corollary2/corollary2_linear_bound.md) in `EndMatter/Corollary2.lean`
- [`corollary2`](../EndMatter/Corollary2/corollary2.md) in `EndMatter/Corollary2.lean`

## Backlinks

- [Back to `INDEX.md`](../INDEX.md)
- [Back to the `Setups.lean` section in the index](../INDEX.md#diamond-setups-lean)
- [Previous declaration in this file](IsTraceAnnihilating.md)
- [Next declaration in this file](tensorWithIdentity.md)