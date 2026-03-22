# partialTraceLeft

## Source location

- Original Lean file: `Diamond/Setups.lean`
- Declaration name: `partialTraceLeft`
- Declaration kind: `def`

## Why this declaration exists

This definition implements the partial trace over the left tensor factor.

 In the file `Setups.lean`, it contributes to foundational objects and notational definitions for operators, channels, norms, and the maps studied in the paper. Later declarations use this name instead of repeatedly expanding the underlying matrix formula.

## Original code

```lean
/-- Partial trace over the left factor. -/
def partialTraceLeft
    (d k : Type u) [Fintype d] [DecidableEq d] [Fintype k] [DecidableEq k]
    (X : Matrix (d × k) (d × k) ℂ) : Matrix k k ℂ :=
  fun i j => ∑ a, X (a, i) (a, j)
```

## Block-by-block explanation

The explanation below follows the declaration block by block. Each block groups a coherent piece of the definition or proof, so the mathematical structure is easier to see than in a strictly line-oriented reading.

1. Code:
```lean
/-- Partial trace over the left factor. -/
```
This is a Lean docstring. It is a human-written comment that tells readers what the declaration is meant to express before the formal code begins.

2. Code:
```lean
def partialTraceLeft
```
This line starts the `partialTraceLeft` declaration. Because it begins with `def`, Lean now knows what kind of named object is being introduced.

3. Code:
```lean
    (d k : Type u) [Fintype d] [DecidableEq d] [Fintype k] [DecidableEq k]
```
This line is one local step in the declaration. It either refines the formula being defined or advances the proof by a small algebraic or logical move.  A bracket such as `[Fintype d]` tells Lean that the index set `d` is finite, so sums over all indices make sense.  A bracket such as `[DecidableEq d]` tells Lean that it can decide whether two indices are equal.

4. Code:
```lean
    (X : Matrix (d × k) (d × k) ℂ) : Matrix k k ℂ :=
```
This line is one local step in the declaration. It either refines the formula being defined or advances the proof by a small algebraic or logical move.  `Matrix d d ℂ` means a square matrix with complex entries; the index type `d` tells Lean which rows and columns exist.

5. Code:
```lean
  fun i j => ∑ a, X (a, i) (a, j)
```
This line is one local step in the declaration. It either refines the formula being defined or advances the proof by a small algebraic or logical move.

## Mathematical summary

In ordinary mathematical language, `partialTraceLeft` is the project's formal Lean name for the object introduced in this declaration.

## Dependencies and downstream use

### Earlier declarations this depends on
- This declaration does not explicitly cite an earlier named declaration from the documented tree; it mostly uses Lean primitives or local algebraic steps.

### Later declarations that use this one
- [`partialTranspose_rank_upper_bound`](../PositiveGap/NotTight/partialTranspose_rank_upper_bound.md) in `PositiveGap/NotTight.lean`
- [`trace_eq_trace_partialTraceLeft`](../StandardFacts/trace_eq_trace_partialTraceLeft.md) in `StandardFacts.lean`
- [`partialTraceLeft_tensor_zero`](../StandardFacts/partialTraceLeft_tensor_zero.md) in `StandardFacts.lean`
- [`lemma4`](../PositiveGap/Lemma4/lemma4.md) in `PositiveGap/Lemma4.lean`
- [`corollary1`](../PositiveGap/Corollary1/corollary1.md) in `PositiveGap/Corollary1.lean`
- [`theorem_not_tight`](../PositiveGap/NotTight/theorem_not_tight.md) in `PositiveGap/NotTight.lean`

## Backlinks

- [Back to `INDEX.md`](../INDEX.md)
- [Back to the `Setups.lean` section in the index](../INDEX.md#diamond-setups-lean)
- [Previous declaration in this file](diamondOp.md)
- [Next declaration in this file](idMinus.md)
