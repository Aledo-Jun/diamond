# hsNormOp_eq_zero_iff

## Source location

- Original Lean file: `Diamond/StandardFacts.lean`
- Declaration name: `hsNormOp_eq_zero_iff`
- Declaration kind: `theorem`

## Why this declaration exists

This theorem records a reusable fact named `hsNormOp_eq_zero_iff`. Its role is to make the later proof flow easier to state and reuse.

 In the file `StandardFacts.lean`, it contributes to helper facts and background axioms that the paper treats as standard or external input. Later proofs call this result by name, so documenting it makes the larger argument readable as a mathematical chain rather than as opaque proof script.

## Original code

```lean
theorem hsNormOp_eq_zero_iff
    {m n : Type u} [Fintype m] [DecidableEq m] [Fintype n] [DecidableEq n]
    {X : Matrix m n ℂ} : hsNormOp X = 0 ↔ X = 0 := by
  unfold hsNormOp hsNorm
  simp
```

## Line-by-line explanation

The explanation below follows the declaration one physical line at a time. For long proofs, some lines are tiny bookkeeping steps; those are still explained, but briefly.

1. Code:
```lean
theorem hsNormOp_eq_zero_iff
```
This line starts the `hsNormOp_eq_zero_iff` declaration. Because it begins with `theorem`, Lean now knows what kind of named object is being introduced.

2. Code:
```lean
    {m n : Type u} [Fintype m] [DecidableEq m] [Fintype n] [DecidableEq n]
```
This line is one local step in the declaration. It either refines the formula being defined or advances the proof by a small algebraic or logical move.  A bracket such as `[Fintype d]` tells Lean that the index set `d` is finite, so sums over all indices make sense.  A bracket such as `[DecidableEq d]` tells Lean that it can decide whether two indices are equal.

3. Code:
```lean
    {X : Matrix m n ℂ} : hsNormOp X = 0 ↔ X = 0 := by
```
This line says that a proof script begins here. Everything indented underneath is a sequence of instructions that Lean will check step by step.  `Matrix d d ℂ` means a square matrix with complex entries; the index type `d` tells Lean which rows and columns exist.

4. Code:
```lean
  unfold hsNormOp hsNorm
```
This line is one local step in the declaration. It either refines the formula being defined or advances the proof by a small algebraic or logical move.

5. Code:
```lean
  simp
```
This line simplifies the goal using definitions and known equalities. `simpa` means that, after simplification, the desired statement matches a theorem Lean already has.

## Mathematical summary

Restated without Lean syntax, `hsNormOp_eq_zero_iff` is the theorem or lemma written above.

- State the desired identity or inequality in Lean’s syntax.
- Introduce temporary names and intermediate claims that organize the argument.
- Use rewriting, simplification, and earlier lemmas to reduce the goal to standard matrix or norm manipulations.
- Close the remaining algebraic or order-theoretic steps with Lean’s proof tactics.

## Dependencies and downstream use

### Earlier declarations this depends on
- [`hsNorm`](../Setups/hsNorm.md) from `Setups.lean`
- [`hsNormOp`](../Setups/hsNormOp.md) from `Setups.lean`

### Later declarations that use this one
- [`partialTranspose_ne_zero_of_ne_zero`](../PositiveGap/NotTight/partialTranspose_ne_zero_of_ne_zero.md) in `PositiveGap/NotTight.lean`

## Backlinks

- [Back to `INDEX.md`](../INDEX.md)
- [Back to the `StandardFacts.lean` section in the index](../INDEX.md#diamond-standardfacts-lean)
- [Previous declaration in this file](hsNorm_nonneg.md)
- [Next declaration in this file](quantumChannel_has_kraus.md)