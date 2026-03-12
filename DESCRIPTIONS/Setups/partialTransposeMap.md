# partialTransposeMap

## Source location

- Original Lean file: `Diamond/Setups.lean`
- Declaration name: `partialTransposeMap`
- Declaration kind: `def`

## Why this declaration exists

This definition applies transposition only on the left tensor factor, leaving the right factor unchanged.

 In the file `Setups.lean`, it contributes to foundational objects and notational definitions for operators, channels, norms, and the maps studied in the paper. Later declarations use this name instead of repeatedly expanding the underlying matrix formula.

## Original code

```lean
/-- Partial transpose on the left tensor factor. -/
def partialTransposeMap
    (d k : Type u) [Fintype d] [DecidableEq d] [Fintype k] [DecidableEq k] :
    Channel (d × k) where
  toFun := fun X i j => X (j.1, i.2) (i.1, j.2)
  map_add' := by
    intro X Y
    ext i j
    simp
  map_smul' := by
    intro c X
    ext i j
    simp
```

## Line-by-line explanation

The explanation below follows the declaration one physical line at a time. For long proofs, some lines are tiny bookkeeping steps; those are still explained, but briefly.

1. Code:
```lean
/-- Partial transpose on the left tensor factor. -/
```
This is a Lean docstring. It is a human-written comment that tells readers what the declaration is meant to express before the formal code begins.

2. Code:
```lean
def partialTransposeMap
```
This line starts the `partialTransposeMap` declaration. Because it begins with `def`, Lean now knows what kind of named object is being introduced.

3. Code:
```lean
    (d k : Type u) [Fintype d] [DecidableEq d] [Fintype k] [DecidableEq k] :
```
This line is one local step in the declaration. It either refines the formula being defined or advances the proof by a small algebraic or logical move.  A bracket such as `[Fintype d]` tells Lean that the index set `d` is finite, so sums over all indices make sense.  A bracket such as `[DecidableEq d]` tells Lean that it can decide whether two indices are equal.

4. Code:
```lean
    Channel (d × k) where
```
This line starts a `where` block. In Lean, a `where` block lists the fields of a structure or bundled map.

5. Code:
```lean
  toFun := fun X i j => X (j.1, i.2) (i.1, j.2)
```
This line is one local step in the declaration. It either refines the formula being defined or advances the proof by a small algebraic or logical move.

6. Code:
```lean
  map_add' := by
```
This line says that a proof script begins here. Everything indented underneath is a sequence of instructions that Lean will check step by step.

7. Code:
```lean
    intro X Y
```
This line introduces the variable or hypothesis named here into the proof context. In ordinary mathematical prose, it is the same as saying “let” or “assume”.

8. Code:
```lean
    ext i j
```
This line invokes extensionality. To prove two maps or matrices are equal, Lean reduces the problem to checking their values entry by entry.

9. Code:
```lean
    simp
```
This line simplifies the goal using definitions and known equalities. `simpa` means that, after simplification, the desired statement matches a theorem Lean already has.

10. Code:
```lean
  map_smul' := by
```
This line says that a proof script begins here. Everything indented underneath is a sequence of instructions that Lean will check step by step.

11. Code:
```lean
    intro c X
```
This line introduces the variable or hypothesis named here into the proof context. In ordinary mathematical prose, it is the same as saying “let” or “assume”.

12. Code:
```lean
    ext i j
```
This line invokes extensionality. To prove two maps or matrices are equal, Lean reduces the problem to checking their values entry by entry.

13. Code:
```lean
    simp
```
This line simplifies the goal using definitions and known equalities. `simpa` means that, after simplification, the desired statement matches a theorem Lean already has.

## Mathematical summary

In ordinary mathematical language, `partialTransposeMap` is the project's formal Lean name for the object introduced in this declaration.

## Dependencies and downstream use

### Earlier declarations this depends on
- [`Channel`](Channel.md) from `Setups.lean`

### Later declarations that use this one
- [`tensorWithIdentity_comp_transpose`](../StandardFacts/tensorWithIdentity_comp_transpose.md) in `StandardFacts.lean`
- [`partialTranspose_rank_upper_bound`](../StandardFacts/partialTranspose_rank_upper_bound.md) in `StandardFacts.lean`
- [`lemma3`](../Theorem/Lemma3/lemma3.md) in `Theorem/Lemma3.lean`
- [`theorem1`](../Theorem/Theorem1/theorem1.md) in `Theorem/Theorem1.lean`
- [`remark1`](../Theorem/Remark1/remark1.md) in `Theorem/Remark1.lean`
- [`partialTranspose_ne_zero_of_ne_zero`](../PositiveGap/NotTight/partialTranspose_ne_zero_of_ne_zero.md) in `PositiveGap/NotTight.lean`
- [`theorem_not_tight`](../PositiveGap/NotTight/theorem_not_tight.md) in `PositiveGap/NotTight.lean`

## Backlinks

- [Back to `INDEX.md`](../INDEX.md)
- [Back to the `Setups.lean` section in the index](../INDEX.md#diamond-setups-lean)
- [Previous declaration in this file](tensorWithIdentity.md)
- [Next declaration in this file](diamondNorm.md)