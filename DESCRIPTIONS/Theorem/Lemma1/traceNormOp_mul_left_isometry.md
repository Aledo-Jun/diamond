# traceNormOp_mul_left_isometry

## Source location

- Original Lean file: `Diamond/Theorem/Lemma1.lean`
- Declaration name: `traceNormOp_mul_left_isometry`
- Declaration kind: `theorem`

## Why this declaration exists

Left multiplication by an isometry preserves the concrete trace norm.

 In the file `Theorem/Lemma1.lean`, it contributes to the proof infrastructure for the first norm inequality and the public theorem `lemma1`. Later proofs call this result by name, so documenting it makes the larger argument readable as a mathematical chain rather than as opaque proof script.

## Original code

```lean
/-- Left multiplication by an isometry preserves the concrete trace norm. -/
theorem traceNormOp_mul_left_isometry
    {d : Type u} [Fintype d] [DecidableEq d]
    (U X : Matrix d d ℂ) (hU : Uᴴ * U = 1) :
    traceNormOp (U * X) = traceNormOp X := by
  have hmul : (U * X)ᴴ * (U * X) = Xᴴ * X := by
    calc
      (U * X)ᴴ * (U * X) = Xᴴ * (Uᴴ * U) * X := by
        simp [Matrix.conjTranspose_mul, Matrix.mul_assoc]
      _ = Xᴴ * X := by
        simp [hU]
  dsimp [traceNormOp, traceNorm]
  have hEig :
      (Matrix.isHermitian_conjTranspose_mul_self (U * X)).eigenvalues =
        (Matrix.isHermitian_conjTranspose_mul_self X).eigenvalues := by
    apply
      (Matrix.IsHermitian.eigenvalues_eq_eigenvalues_iff
        (Matrix.isHermitian_conjTranspose_mul_self (U * X))
        (Matrix.isHermitian_conjTranspose_mul_self X)).2
    exact congrArg Matrix.charpoly hmul
  rw [hEig]
```

## Line-by-line explanation

The explanation below follows the declaration one physical line at a time. For long proofs, some lines are tiny bookkeeping steps; those are still explained, but briefly.

1. Code:
```lean
/-- Left multiplication by an isometry preserves the concrete trace norm. -/
```
This is a Lean docstring. It is a human-written comment that tells readers what the declaration is meant to express before the formal code begins.

2. Code:
```lean
theorem traceNormOp_mul_left_isometry
```
This line starts the `traceNormOp_mul_left_isometry` declaration. Because it begins with `theorem`, Lean now knows what kind of named object is being introduced.

3. Code:
```lean
    {d : Type u} [Fintype d] [DecidableEq d]
```
This line is one local step in the declaration. It either refines the formula being defined or advances the proof by a small algebraic or logical move.  A bracket such as `[Fintype d]` tells Lean that the index set `d` is finite, so sums over all indices make sense.  A bracket such as `[DecidableEq d]` tells Lean that it can decide whether two indices are equal.

4. Code:
```lean
    (U X : Matrix d d ℂ) (hU : Uᴴ * U = 1) :
```
This line is one local step in the declaration. It either refines the formula being defined or advances the proof by a small algebraic or logical move.  `Matrix d d ℂ` means a square matrix with complex entries; the index type `d` tells Lean which rows and columns exist.  The superscript `ᴴ` means conjugate transpose (also called the adjoint).

5. Code:
```lean
    traceNormOp (U * X) = traceNormOp X := by
```
This line says that a proof script begins here. Everything indented underneath is a sequence of instructions that Lean will check step by step.

6. Code:
```lean
  have hmul : (U * X)ᴴ * (U * X) = Xᴴ * X := by
```
This line says that a proof script begins here. Everything indented underneath is a sequence of instructions that Lean will check step by step.  The superscript `ᴴ` means conjugate transpose (also called the adjoint).

7. Code:
```lean
    calc
```
This line begins a chained calculation. Each displayed step that follows must be justified by the indented proof after `:= by`.

8. Code:
```lean
      (U * X)ᴴ * (U * X) = Xᴴ * (Uᴴ * U) * X := by
```
This line says that a proof script begins here. Everything indented underneath is a sequence of instructions that Lean will check step by step.  The superscript `ᴴ` means conjugate transpose (also called the adjoint).

9. Code:
```lean
        simp [Matrix.conjTranspose_mul, Matrix.mul_assoc]
```
This line simplifies the goal using definitions and known equalities. `simpa` means that, after simplification, the desired statement matches a theorem Lean already has.

10. Code:
```lean
      _ = Xᴴ * X := by
```
This line says that a proof script begins here. Everything indented underneath is a sequence of instructions that Lean will check step by step.  The superscript `ᴴ` means conjugate transpose (also called the adjoint).

11. Code:
```lean
        simp [hU]
```
This line simplifies the goal using definitions and known equalities. `simpa` means that, after simplification, the desired statement matches a theorem Lean already has.

12. Code:
```lean
  dsimp [traceNormOp, traceNorm]
```
This line is one local step in the declaration. It either refines the formula being defined or advances the proof by a small algebraic or logical move.

13. Code:
```lean
  have hEig :
```
This line introduces an intermediate claim. The proof pauses to establish a fact that will be used shortly afterwards.

14. Code:
```lean
      (Matrix.isHermitian_conjTranspose_mul_self (U * X)).eigenvalues =
```
This line is one local step in the declaration. It either refines the formula being defined or advances the proof by a small algebraic or logical move.

15. Code:
```lean
        (Matrix.isHermitian_conjTranspose_mul_self X).eigenvalues := by
```
This line says that a proof script begins here. Everything indented underneath is a sequence of instructions that Lean will check step by step.

16. Code:
```lean
    apply
```
This line applies an existing theorem to the current goal. Lean then asks the author to prove the theorem’s hypotheses.

17. Code:
```lean
      (Matrix.IsHermitian.eigenvalues_eq_eigenvalues_iff
```
This line is one local step in the declaration. It either refines the formula being defined or advances the proof by a small algebraic or logical move.

18. Code:
```lean
        (Matrix.isHermitian_conjTranspose_mul_self (U * X))
```
This line is one local step in the declaration. It either refines the formula being defined or advances the proof by a small algebraic or logical move.

19. Code:
```lean
        (Matrix.isHermitian_conjTranspose_mul_self X)).2
```
This line is one local step in the declaration. It either refines the formula being defined or advances the proof by a small algebraic or logical move.

20. Code:
```lean
    exact congrArg Matrix.charpoly hmul
```
This line finishes the current goal by giving Lean the exact theorem, lemma, or term that proves it.

21. Code:
```lean
  rw [hEig]
```
This line uses rewriting. Lean replaces one expression by an equal expression using the lemmas listed in brackets.

## Mathematical summary

Restated without Lean syntax, `traceNormOp_mul_left_isometry` is the theorem or lemma written above.

- State the desired identity or inequality in Lean’s syntax.
- Introduce temporary names and intermediate claims that organize the argument.
- Use rewriting, simplification, and earlier lemmas to reduce the goal to standard matrix or norm manipulations.
- Close the remaining algebraic or order-theoretic steps with Lean’s proof tactics.

## Dependencies and downstream use

### Earlier declarations this depends on
- [`traceNorm`](../../Setups/traceNorm.md) from `Setups.lean`
- [`traceNormOp`](../../Setups/traceNormOp.md) from `Setups.lean`

### Later declarations that use this one
- [`traceNormOp_mul_right_isometry`](traceNormOp_mul_right_isometry.md) in `Theorem/Lemma1.lean`
- [`traceNormOp_hermitian_eq_sum_abs_eigenvalues`](traceNormOp_hermitian_eq_sum_abs_eigenvalues.md) in `Theorem/Lemma1.lean`
- [`explicit_witness_traceNorm_eq_sum`](../../EndMatter/Eq7/explicit_witness_traceNorm_eq_sum.md) in `EndMatter/Eq7.lean`

## Backlinks

- [Back to `INDEX.md`](../../INDEX.md)
- [Back to the `Theorem/Lemma1.lean` section in the index](../../INDEX.md#diamond-theorem-lemma1-lean)
- [Previous declaration in this file](hermitian_re_trace_conjTranspose_mul_self_eq_sum_sq_eigenvalues.md)
- [Next declaration in this file](traceNormOp_diagonal.md)