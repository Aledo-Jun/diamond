# lemma3

## Source location

- Original Lean file: `Diamond/Theorem/Lemma3.lean`
- Declaration name: `lemma3`
- Declaration kind: `theorem`

## Why this declaration exists

Lemma 3: partial transpose preserves the Hilbert--Schmidt norm.

 In the file `Theorem/Lemma3.lean`, it contributes to the Hilbert--Schmidt invariance of partial transpose. Later proofs call this result by name, so documenting it makes the larger argument readable as a mathematical chain rather than as opaque proof script.

## Original code

```lean
/-- Lemma 3: partial transpose preserves the Hilbert--Schmidt norm. -/
theorem lemma3
    {d k : Type u} [Fintype d] [DecidableEq d] [Fintype k] [DecidableEq k]
    (X : Matrix (d × k) (d × k) ℂ) :
    hsNormOp (partialTransposeMap d k X) = hsNormOp X := by
  change ‖partialTransposeMap d k X‖ = ‖X‖
  let e : (d × k) × (d × k) ≃ (d × k) × (d × k) :=
    { toFun := fun p => ((p.2.1, p.1.2), (p.1.1, p.2.2))
      invFun := fun p => ((p.2.1, p.1.2), (p.1.1, p.2.2))
      left_inv := by
        intro p
        aesop
      right_inv := by
        intro p
        aesop }
  have hEq :
      (∑ p : (d × k) × (d × k), ‖X (e p).1 (e p).2‖ ^ (2 : ℝ)) =
        ∑ p : (d × k) × (d × k), ‖X p.1 p.2‖ ^ (2 : ℝ) := by
    exact Equiv.sum_comp e (g := fun p => ‖X p.1 p.2‖ ^ (2 : ℝ))
  calc
    ‖partialTransposeMap d k X‖
      = (∑ p : (d × k) × (d × k), ‖X (e p).1 (e p).2‖ ^ (2 : ℝ)) ^ (1 / 2 : ℝ) := by
          simp [partialTransposeMap, Matrix.frobenius_norm_def, e, Fintype.sum_prod_type]
    _ = (∑ p : (d × k) × (d × k), ‖X p.1 p.2‖ ^ (2 : ℝ)) ^ (1 / 2 : ℝ) := by
          rw [hEq]
    _ = ‖X‖ := by
          simp [Matrix.frobenius_norm_def, Fintype.sum_prod_type]
```

## Line-by-line explanation

The explanation below follows the declaration one physical line at a time. For long proofs, some lines are tiny bookkeeping steps; those are still explained, but briefly.

1. Code:
```lean
/-- Lemma 3: partial transpose preserves the Hilbert--Schmidt norm. -/
```
This is a Lean docstring. It is a human-written comment that tells readers what the declaration is meant to express before the formal code begins.

2. Code:
```lean
theorem lemma3
```
This line starts the `lemma3` declaration. Because it begins with `theorem`, Lean now knows what kind of named object is being introduced.

3. Code:
```lean
    {d k : Type u} [Fintype d] [DecidableEq d] [Fintype k] [DecidableEq k]
```
This line is one local step in the declaration. It either refines the formula being defined or advances the proof by a small algebraic or logical move.  A bracket such as `[Fintype d]` tells Lean that the index set `d` is finite, so sums over all indices make sense.  A bracket such as `[DecidableEq d]` tells Lean that it can decide whether two indices are equal.

4. Code:
```lean
    (X : Matrix (d × k) (d × k) ℂ) :
```
This line is one local step in the declaration. It either refines the formula being defined or advances the proof by a small algebraic or logical move.  `Matrix d d ℂ` means a square matrix with complex entries; the index type `d` tells Lean which rows and columns exist.

5. Code:
```lean
    hsNormOp (partialTransposeMap d k X) = hsNormOp X := by
```
This line says that a proof script begins here. Everything indented underneath is a sequence of instructions that Lean will check step by step.

6. Code:
```lean
  change ‖partialTransposeMap d k X‖ = ‖X‖
```
This line replaces the current goal by a definitionally equal goal that is easier to manipulate.

7. Code:
```lean
  let e : (d × k) × (d × k) ≃ (d × k) × (d × k) :=
```
This line gives a temporary name to an expression. Doing that makes later lines shorter and easier to read.

8. Code:
```lean
    { toFun := fun p => ((p.2.1, p.1.2), (p.1.1, p.2.2))
```
This line is one local step in the declaration. It either refines the formula being defined or advances the proof by a small algebraic or logical move.

9. Code:
```lean
      invFun := fun p => ((p.2.1, p.1.2), (p.1.1, p.2.2))
```
This line is one local step in the declaration. It either refines the formula being defined or advances the proof by a small algebraic or logical move.

10. Code:
```lean
      left_inv := by
```
This line says that a proof script begins here. Everything indented underneath is a sequence of instructions that Lean will check step by step.

11. Code:
```lean
        intro p
```
This line introduces the variable or hypothesis named here into the proof context. In ordinary mathematical prose, it is the same as saying “let” or “assume”.

12. Code:
```lean
        aesop
```
This line uses Lean's automation tactic `aesop`, which tries a collection of standard proof moves automatically.

13. Code:
```lean
      right_inv := by
```
This line says that a proof script begins here. Everything indented underneath is a sequence of instructions that Lean will check step by step.

14. Code:
```lean
        intro p
```
This line introduces the variable or hypothesis named here into the proof context. In ordinary mathematical prose, it is the same as saying “let” or “assume”.

15. Code:
```lean
        aesop }
```
This line uses Lean's automation tactic `aesop`, which tries a collection of standard proof moves automatically.

16. Code:
```lean
  have hEq :
```
This line introduces an intermediate claim. The proof pauses to establish a fact that will be used shortly afterwards.

17. Code:
```lean
      (∑ p : (d × k) × (d × k), ‖X (e p).1 (e p).2‖ ^ (2 : ℝ)) =
```
This line is one local step in the declaration. It either refines the formula being defined or advances the proof by a small algebraic or logical move.

18. Code:
```lean
        ∑ p : (d × k) × (d × k), ‖X p.1 p.2‖ ^ (2 : ℝ) := by
```
This line says that a proof script begins here. Everything indented underneath is a sequence of instructions that Lean will check step by step.

19. Code:
```lean
    exact Equiv.sum_comp e (g := fun p => ‖X p.1 p.2‖ ^ (2 : ℝ))
```
This line finishes the current goal by giving Lean the exact theorem, lemma, or term that proves it.

20. Code:
```lean
  calc
```
This line begins a chained calculation. Each displayed step that follows must be justified by the indented proof after `:= by`.

21. Code:
```lean
    ‖partialTransposeMap d k X‖
```
This line is one local step in the declaration. It either refines the formula being defined or advances the proof by a small algebraic or logical move.

22. Code:
```lean
      = (∑ p : (d × k) × (d × k), ‖X (e p).1 (e p).2‖ ^ (2 : ℝ)) ^ (1 / 2 : ℝ) := by
```
This line says that a proof script begins here. Everything indented underneath is a sequence of instructions that Lean will check step by step.

23. Code:
```lean
          simp [partialTransposeMap, Matrix.frobenius_norm_def, e, Fintype.sum_prod_type]
```
This line simplifies the goal using definitions and known equalities. `simpa` means that, after simplification, the desired statement matches a theorem Lean already has.

24. Code:
```lean
    _ = (∑ p : (d × k) × (d × k), ‖X p.1 p.2‖ ^ (2 : ℝ)) ^ (1 / 2 : ℝ) := by
```
This line says that a proof script begins here. Everything indented underneath is a sequence of instructions that Lean will check step by step.

25. Code:
```lean
          rw [hEq]
```
This line uses rewriting. Lean replaces one expression by an equal expression using the lemmas listed in brackets.

26. Code:
```lean
    _ = ‖X‖ := by
```
This line says that a proof script begins here. Everything indented underneath is a sequence of instructions that Lean will check step by step.

27. Code:
```lean
          simp [Matrix.frobenius_norm_def, Fintype.sum_prod_type]
```
This line simplifies the goal using definitions and known equalities. `simpa` means that, after simplification, the desired statement matches a theorem Lean already has.

## Mathematical summary

Restated without Lean syntax, `lemma3` is the theorem or lemma written above.

- State the desired identity or inequality in Lean’s syntax.
- Introduce temporary names and intermediate claims that organize the argument.
- Use rewriting, simplification, and earlier lemmas to reduce the goal to standard matrix or norm manipulations.
- Close the remaining algebraic or order-theoretic steps with Lean’s proof tactics.

## Dependencies and downstream use

### Earlier declarations this depends on
- [`hsNormOp`](../../Setups/hsNormOp.md) from `Setups.lean`
- [`partialTransposeMap`](../../Setups/partialTransposeMap.md) from `Setups.lean`

### Later declarations that use this one
- [`theorem1`](../Theorem1/theorem1.md) in `Theorem/Theorem1.lean`
- [`remark1`](../Remark1/remark1.md) in `Theorem/Remark1.lean`
- [`partialTranspose_ne_zero_of_ne_zero`](../../PositiveGap/NotTight/partialTranspose_ne_zero_of_ne_zero.md) in `PositiveGap/NotTight.lean`
- [`theorem_not_tight`](../../PositiveGap/NotTight/theorem_not_tight.md) in `PositiveGap/NotTight.lean`

## Backlinks

- [Back to `INDEX.md`](../../INDEX.md)
- [Back to the `Theorem/Lemma3.lean` section in the index](../../INDEX.md#diamond-theorem-lemma3-lean)