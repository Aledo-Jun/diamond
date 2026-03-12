# partialTranspose_ne_zero_of_ne_zero

## Source location

- Original Lean file: `Diamond/PositiveGap/NotTight.lean`
- Declaration name: `partialTranspose_ne_zero_of_ne_zero`
- Declaration kind: `lemma`

## Why this declaration exists

Partial transpose preserves nonzeroness because it preserves the Hilbert--Schmidt norm.

 In the file `PositiveGap/NotTight.lean`, it contributes to the finite-dimensional non-tightness argument and the equality-case analysis behind it. Later proofs call this result by name, so documenting it makes the larger argument readable as a mathematical chain rather than as opaque proof script.

## Original code

```lean
/-- Partial transpose preserves nonzeroness because it preserves the Hilbert--Schmidt norm. -/
private lemma partialTranspose_ne_zero_of_ne_zero
    {d k : Type u} [Fintype d] [DecidableEq d] [Fintype k] [DecidableEq k]
    {X : Matrix (d × k) (d × k) ℂ} (hX : X ≠ 0) :
    partialTransposeMap d k X ≠ 0 := by
  intro hzero
  have hnormY : hsNormOp (partialTransposeMap d k X) = 0 := by
    exact (hsNormOp_eq_zero_iff).2 hzero
  have hnormX : hsNormOp X = 0 := by
    rw [lemma3 (d := d) (k := k) X] at hnormY
    exact hnormY
  exact hX ((hsNormOp_eq_zero_iff).1 hnormX)
```

## Line-by-line explanation

The explanation below follows the declaration one physical line at a time. For long proofs, some lines are tiny bookkeeping steps; those are still explained, but briefly.

1. Code:
```lean
/-- Partial transpose preserves nonzeroness because it preserves the Hilbert--Schmidt norm. -/
```
This is a Lean docstring. It is a human-written comment that tells readers what the declaration is meant to express before the formal code begins.

2. Code:
```lean
private lemma partialTranspose_ne_zero_of_ne_zero
```
This line starts the `partialTranspose_ne_zero_of_ne_zero` declaration. Because it begins with `lemma`, Lean now knows what kind of named object is being introduced.

3. Code:
```lean
    {d k : Type u} [Fintype d] [DecidableEq d] [Fintype k] [DecidableEq k]
```
This line is one local step in the declaration. It either refines the formula being defined or advances the proof by a small algebraic or logical move.  A bracket such as `[Fintype d]` tells Lean that the index set `d` is finite, so sums over all indices make sense.  A bracket such as `[DecidableEq d]` tells Lean that it can decide whether two indices are equal.

4. Code:
```lean
    {X : Matrix (d × k) (d × k) ℂ} (hX : X ≠ 0) :
```
This line is one local step in the declaration. It either refines the formula being defined or advances the proof by a small algebraic or logical move.  `Matrix d d ℂ` means a square matrix with complex entries; the index type `d` tells Lean which rows and columns exist.

5. Code:
```lean
    partialTransposeMap d k X ≠ 0 := by
```
This line says that a proof script begins here. Everything indented underneath is a sequence of instructions that Lean will check step by step.

6. Code:
```lean
  intro hzero
```
This line introduces the variable or hypothesis named here into the proof context. In ordinary mathematical prose, it is the same as saying “let” or “assume”.

7. Code:
```lean
  have hnormY : hsNormOp (partialTransposeMap d k X) = 0 := by
```
This line says that a proof script begins here. Everything indented underneath is a sequence of instructions that Lean will check step by step.

8. Code:
```lean
    exact (hsNormOp_eq_zero_iff).2 hzero
```
This line finishes the current goal by giving Lean the exact theorem, lemma, or term that proves it.

9. Code:
```lean
  have hnormX : hsNormOp X = 0 := by
```
This line says that a proof script begins here. Everything indented underneath is a sequence of instructions that Lean will check step by step.

10. Code:
```lean
    rw [lemma3 (d := d) (k := k) X] at hnormY
```
This line uses rewriting. Lean replaces one expression by an equal expression using the lemmas listed in brackets.

11. Code:
```lean
    exact hnormY
```
This line finishes the current goal by giving Lean the exact theorem, lemma, or term that proves it.

12. Code:
```lean
  exact hX ((hsNormOp_eq_zero_iff).1 hnormX)
```
This line finishes the current goal by giving Lean the exact theorem, lemma, or term that proves it.

## Mathematical summary

Restated without Lean syntax, `partialTranspose_ne_zero_of_ne_zero` is the theorem or lemma written above.

- State the desired identity or inequality in Lean’s syntax.
- Introduce temporary names and intermediate claims that organize the argument.
- Use rewriting, simplification, and earlier lemmas to reduce the goal to standard matrix or norm manipulations.
- Close the remaining algebraic or order-theoretic steps with Lean’s proof tactics.

## Dependencies and downstream use

### Earlier declarations this depends on
- [`hsNormOp`](../../Setups/hsNormOp.md) from `Setups.lean`
- [`partialTransposeMap`](../../Setups/partialTransposeMap.md) from `Setups.lean`
- [`hsNormOp_eq_zero_iff`](../../StandardFacts/hsNormOp_eq_zero_iff.md) from `StandardFacts.lean`
- [`lemma3`](../../Theorem/Lemma3/lemma3.md) from `Theorem/Lemma3.lean`

### Later declarations that use this one
- [`theorem_not_tight`](theorem_not_tight.md) in `PositiveGap/NotTight.lean`

## Backlinks

- [Back to `INDEX.md`](../../INDEX.md)
- [Back to the `PositiveGap/NotTight.lean` section in the index](../../INDEX.md#diamond-positivegap-nottight-lean)
- [Previous declaration in this file](lemma2_eq_imp_full_rank.md)
- [Next declaration in this file](theorem_not_tight.md)