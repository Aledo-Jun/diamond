# tensorWithIdentity

## Source location

- Original Lean file: `Diamond/Setups.lean`
- Declaration name: `tensorWithIdentity`
- Declaration kind: `def`

## Why this declaration exists

This definition stabilizes a map by tensoring it with the identity on an ancilla space.

 In the file `Setups.lean`, it contributes to foundational objects and notational definitions for operators, channels, norms, and the maps studied in the paper. Later declarations use this name instead of repeatedly expanding the underlying matrix formula.

## Original code

```lean
/-- Tensor a map on the left factor with the identity on the right factor. -/
def tensorWithIdentity
    (d k : Type u) [Fintype d] [DecidableEq d] [Fintype k] [DecidableEq k]
    (Φ : Channel d) : Channel (d × k) where
  toFun := fun X i j =>
    Φ (fun p q : d => X (p, i.2) (q, j.2)) i.1 j.1
  map_add' := by
    intro X Y
    ext i j
    let X' : Operator d := fun p q => X (p, i.2) (q, j.2)
    let Y' : Operator d := fun p q => Y (p, i.2) (q, j.2)
    change (Φ (X' + Y')) i.1 j.1 = (Φ X' + Φ Y') i.1 j.1
    rw [map_add]
  map_smul' := by
    intro c X
    ext i j
    let X' : Operator d := fun p q => X (p, i.2) (q, j.2)
    change (Φ (c • X')) i.1 j.1 = (c • Φ X') i.1 j.1
    rw [map_smul]
```

## Line-by-line explanation

The explanation below follows the declaration one physical line at a time. For long proofs, some lines are tiny bookkeeping steps; those are still explained, but briefly.

1. Code:
```lean
/-- Tensor a map on the left factor with the identity on the right factor. -/
```
This is a Lean docstring. It is a human-written comment that tells readers what the declaration is meant to express before the formal code begins.

2. Code:
```lean
def tensorWithIdentity
```
This line starts the `tensorWithIdentity` declaration. Because it begins with `def`, Lean now knows what kind of named object is being introduced.

3. Code:
```lean
    (d k : Type u) [Fintype d] [DecidableEq d] [Fintype k] [DecidableEq k]
```
This line is one local step in the declaration. It either refines the formula being defined or advances the proof by a small algebraic or logical move.  A bracket such as `[Fintype d]` tells Lean that the index set `d` is finite, so sums over all indices make sense.  A bracket such as `[DecidableEq d]` tells Lean that it can decide whether two indices are equal.

4. Code:
```lean
    (Φ : Channel d) : Channel (d × k) where
```
This line starts a `where` block. In Lean, a `where` block lists the fields of a structure or bundled map.

5. Code:
```lean
  toFun := fun X i j =>
```
This line is one local step in the declaration. It either refines the formula being defined or advances the proof by a small algebraic or logical move.

6. Code:
```lean
    Φ (fun p q : d => X (p, i.2) (q, j.2)) i.1 j.1
```
This line is one local step in the declaration. It either refines the formula being defined or advances the proof by a small algebraic or logical move.

7. Code:
```lean
  map_add' := by
```
This line says that a proof script begins here. Everything indented underneath is a sequence of instructions that Lean will check step by step.

8. Code:
```lean
    intro X Y
```
This line introduces the variable or hypothesis named here into the proof context. In ordinary mathematical prose, it is the same as saying “let” or “assume”.

9. Code:
```lean
    ext i j
```
This line invokes extensionality. To prove two maps or matrices are equal, Lean reduces the problem to checking their values entry by entry.

10. Code:
```lean
    let X' : Operator d := fun p q => X (p, i.2) (q, j.2)
```
This line gives a temporary name to an expression. Doing that makes later lines shorter and easier to read.

11. Code:
```lean
    let Y' : Operator d := fun p q => Y (p, i.2) (q, j.2)
```
This line gives a temporary name to an expression. Doing that makes later lines shorter and easier to read.

12. Code:
```lean
    change (Φ (X' + Y')) i.1 j.1 = (Φ X' + Φ Y') i.1 j.1
```
This line replaces the current goal by a definitionally equal goal that is easier to manipulate.

13. Code:
```lean
    rw [map_add]
```
This line uses rewriting. Lean replaces one expression by an equal expression using the lemmas listed in brackets.

14. Code:
```lean
  map_smul' := by
```
This line says that a proof script begins here. Everything indented underneath is a sequence of instructions that Lean will check step by step.

15. Code:
```lean
    intro c X
```
This line introduces the variable or hypothesis named here into the proof context. In ordinary mathematical prose, it is the same as saying “let” or “assume”.

16. Code:
```lean
    ext i j
```
This line invokes extensionality. To prove two maps or matrices are equal, Lean reduces the problem to checking their values entry by entry.

17. Code:
```lean
    let X' : Operator d := fun p q => X (p, i.2) (q, j.2)
```
This line gives a temporary name to an expression. Doing that makes later lines shorter and easier to read.

18. Code:
```lean
    change (Φ (c • X')) i.1 j.1 = (c • Φ X') i.1 j.1
```
This line replaces the current goal by a definitionally equal goal that is easier to manipulate.

19. Code:
```lean
    rw [map_smul]
```
This line uses rewriting. Lean replaces one expression by an equal expression using the lemmas listed in brackets.

## Mathematical summary

In ordinary mathematical language, `tensorWithIdentity` is the project's formal Lean name for the object introduced in this declaration.

## Dependencies and downstream use

### Earlier declarations this depends on
- [`Operator`](Operator.md) from `Setups.lean`
- [`Channel`](Channel.md) from `Setups.lean`

### Later declarations that use this one
- [`diamondNorm`](diamondNorm.md) in `Setups.lean`
- [`diamondNormAt`](diamondNormAt.md) in `Setups.lean`
- [`tensorWithIdentity_comp_transpose`](../StandardFacts/tensorWithIdentity_comp_transpose.md) in `StandardFacts.lean`
- [`diamond_le_of_pointwise`](../StandardFacts/diamond_le_of_pointwise.md) in `StandardFacts.lean`
- [`traceNorm_apply_le_diamond`](../StandardFacts/traceNorm_apply_le_diamond.md) in `StandardFacts.lean`
- [`exists_maximizing_state`](../StandardFacts/exists_maximizing_state.md) in `StandardFacts.lean`
- [`partialTraceLeft_tensor_zero`](../StandardFacts/partialTraceLeft_tensor_zero.md) in `StandardFacts.lean`
- [`tensorWithIdentity_trace_zero`](../StandardFacts/tensorWithIdentity_trace_zero.md) in `StandardFacts.lean`
- [`tensorWithIdentity_hermitian`](../StandardFacts/tensorWithIdentity_hermitian.md) in `StandardFacts.lean`
- [`theorem1`](../Theorem/Theorem1/theorem1.md) in `Theorem/Theorem1.lean`
- [`remark1`](../Theorem/Remark1/remark1.md) in `Theorem/Remark1.lean`
- [`lemma4`](../PositiveGap/Lemma4/lemma4.md) in `PositiveGap/Lemma4.lean`
- [`corollary1`](../PositiveGap/Corollary1/corollary1.md) in `PositiveGap/Corollary1.lean`
- [`lemma7`](../PositiveGap/Lemma7/lemma7.md) in `PositiveGap/Lemma7.lean`
- [`theorem_not_tight`](../PositiveGap/NotTight/theorem_not_tight.md) in `PositiveGap/NotTight.lean`
- [`transpose_phiState_eq_swap`](../EndMatter/Eq7/transpose_phiState_eq_swap.md) in `EndMatter/Eq7.lean`
- [`transpose_ad_phiState_eq_swap_mul_phase`](../EndMatter/Eq7/transpose_ad_phiState_eq_swap_mul_phase.md) in `EndMatter/Eq7.lean`
- [`lambda_phiState_eq`](../EndMatter/Eq7/lambda_phiState_eq.md) in `EndMatter/Eq7.lean`
- [`theorem_eq7_witness_bound`](../EndMatter/Eq7/theorem_eq7_witness_bound.md) in `EndMatter/Eq7.lean`

## Backlinks

- [Back to `INDEX.md`](../INDEX.md)
- [Back to the `Setups.lean` section in the index](../INDEX.md#diamond-setups-lean)
- [Previous declaration in this file](transposeMap.md)
- [Next declaration in this file](partialTransposeMap.md)