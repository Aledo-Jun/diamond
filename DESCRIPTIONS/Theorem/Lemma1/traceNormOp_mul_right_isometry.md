# traceNormOp_mul_right_isometry

## Source location

- Original Lean file: `Diamond/Theorem/Lemma1.lean`
- Declaration name: `traceNormOp_mul_right_isometry`
- Declaration kind: `theorem`

## Why this declaration exists

Right multiplication by an isometry preserves the concrete trace norm.

 In the file `Theorem/Lemma1.lean`, it contributes to the proof infrastructure for the first norm inequality and the public theorem `lemma1`. Later proofs call this result by name, so documenting it makes the larger argument readable as a mathematical chain rather than as opaque proof script.

## Original code

```lean
/-- Right multiplication by an isometry preserves the concrete trace norm. -/
theorem traceNormOp_mul_right_isometry
    {d : Type u} [Fintype d] [DecidableEq d]
    (X U : Matrix d d ℂ) (hU : U * Uᴴ = 1) :
    traceNormOp (X * U) = traceNormOp X := by
  have hU' : (Uᴴ)ᴴ * Uᴴ = 1 := by
    simpa using hU
  calc
    traceNormOp (X * U) = traceNormOp ((X * U)ᴴ) := by
      symm
      exact traceNormOp_conjTranspose (X := X * U)
    _ = traceNormOp (Uᴴ * Xᴴ) := by
      rw [Matrix.conjTranspose_mul]
    _ = traceNormOp Xᴴ := by
      exact traceNormOp_mul_left_isometry (U := Uᴴ) (X := Xᴴ) hU'
    _ = traceNormOp X := by
      exact traceNormOp_conjTranspose (X := X)
```

## Line-by-line explanation

The explanation below follows the declaration one physical line at a time. For long proofs, some lines are tiny bookkeeping steps; those are still explained, but briefly.

1. Code:
```lean
/-- Right multiplication by an isometry preserves the concrete trace norm. -/
```
This is a Lean docstring. It is a human-written comment that tells readers what the declaration is meant to express before the formal code begins.

2. Code:
```lean
theorem traceNormOp_mul_right_isometry
```
This line starts the `traceNormOp_mul_right_isometry` declaration. Because it begins with `theorem`, Lean now knows what kind of named object is being introduced.

3. Code:
```lean
    {d : Type u} [Fintype d] [DecidableEq d]
```
This line is one local step in the declaration. It either refines the formula being defined or advances the proof by a small algebraic or logical move.  A bracket such as `[Fintype d]` tells Lean that the index set `d` is finite, so sums over all indices make sense.  A bracket such as `[DecidableEq d]` tells Lean that it can decide whether two indices are equal.

4. Code:
```lean
    (X U : Matrix d d ℂ) (hU : U * Uᴴ = 1) :
```
This line is one local step in the declaration. It either refines the formula being defined or advances the proof by a small algebraic or logical move.  `Matrix d d ℂ` means a square matrix with complex entries; the index type `d` tells Lean which rows and columns exist.  The superscript `ᴴ` means conjugate transpose (also called the adjoint).

5. Code:
```lean
    traceNormOp (X * U) = traceNormOp X := by
```
This line says that a proof script begins here. Everything indented underneath is a sequence of instructions that Lean will check step by step.

6. Code:
```lean
  have hU' : (Uᴴ)ᴴ * Uᴴ = 1 := by
```
This line says that a proof script begins here. Everything indented underneath is a sequence of instructions that Lean will check step by step.  The superscript `ᴴ` means conjugate transpose (also called the adjoint).

7. Code:
```lean
    simpa using hU
```
This line simplifies the goal using definitions and known equalities. `simpa` means that, after simplification, the desired statement matches a theorem Lean already has.

8. Code:
```lean
  calc
```
This line begins a chained calculation. Each displayed step that follows must be justified by the indented proof after `:= by`.

9. Code:
```lean
    traceNormOp (X * U) = traceNormOp ((X * U)ᴴ) := by
```
This line says that a proof script begins here. Everything indented underneath is a sequence of instructions that Lean will check step by step.  The superscript `ᴴ` means conjugate transpose (also called the adjoint).

10. Code:
```lean
      symm
```
This line is one local step in the declaration. It either refines the formula being defined or advances the proof by a small algebraic or logical move.

11. Code:
```lean
      exact traceNormOp_conjTranspose (X := X * U)
```
This line finishes the current goal by giving Lean the exact theorem, lemma, or term that proves it.

12. Code:
```lean
    _ = traceNormOp (Uᴴ * Xᴴ) := by
```
This line says that a proof script begins here. Everything indented underneath is a sequence of instructions that Lean will check step by step.  The superscript `ᴴ` means conjugate transpose (also called the adjoint).

13. Code:
```lean
      rw [Matrix.conjTranspose_mul]
```
This line uses rewriting. Lean replaces one expression by an equal expression using the lemmas listed in brackets.

14. Code:
```lean
    _ = traceNormOp Xᴴ := by
```
This line says that a proof script begins here. Everything indented underneath is a sequence of instructions that Lean will check step by step.  The superscript `ᴴ` means conjugate transpose (also called the adjoint).

15. Code:
```lean
      exact traceNormOp_mul_left_isometry (U := Uᴴ) (X := Xᴴ) hU'
```
This line finishes the current goal by giving Lean the exact theorem, lemma, or term that proves it.  The superscript `ᴴ` means conjugate transpose (also called the adjoint).

16. Code:
```lean
    _ = traceNormOp X := by
```
This line says that a proof script begins here. Everything indented underneath is a sequence of instructions that Lean will check step by step.

17. Code:
```lean
      exact traceNormOp_conjTranspose (X := X)
```
This line finishes the current goal by giving Lean the exact theorem, lemma, or term that proves it.

## Mathematical summary

Restated without Lean syntax, `traceNormOp_mul_right_isometry` is the theorem or lemma written above.

- State the desired identity or inequality in Lean’s syntax.
- Introduce temporary names and intermediate claims that organize the argument.
- Use rewriting, simplification, and earlier lemmas to reduce the goal to standard matrix or norm manipulations.
- Close the remaining algebraic or order-theoretic steps with Lean’s proof tactics.

## Dependencies and downstream use

### Earlier declarations this depends on
- [`traceNormOp`](../../Setups/traceNormOp.md) from `Setups.lean`
- [`traceNormOp_mul_left_isometry`](traceNormOp_mul_left_isometry.md) from `Theorem/Lemma1.lean`
- [`traceNormOp_conjTranspose`](traceNormOp_conjTranspose.md) from `Theorem/Lemma1.lean`

### Later declarations that use this one
- [`traceNormOp_hermitian_eq_sum_abs_eigenvalues`](traceNormOp_hermitian_eq_sum_abs_eigenvalues.md) in `Theorem/Lemma1.lean`

## Backlinks

- [Back to `INDEX.md`](../../INDEX.md)
- [Back to the `Theorem/Lemma1.lean` section in the index](../../INDEX.md#diamond-theorem-lemma1-lean)
- [Previous declaration in this file](traceNormOp_conjTranspose.md)
- [Next declaration in this file](traceNormOp_hermitian_eq_sum_abs_eigenvalues.md)