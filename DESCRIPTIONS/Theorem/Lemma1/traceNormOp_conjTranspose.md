# traceNormOp_conjTranspose

## Source location

- Original Lean file: `Diamond/Theorem/Lemma1.lean`
- Declaration name: `traceNormOp_conjTranspose`
- Declaration kind: `theorem`

## Why this declaration exists

The concrete trace norm is invariant under conjugate transpose.

 In the file `Theorem/Lemma1.lean`, it contributes to the proof infrastructure for the first norm inequality and the public theorem `lemma1`. Later proofs call this result by name, so documenting it makes the larger argument readable as a mathematical chain rather than as opaque proof script.

## Original code

```lean
/-- The concrete trace norm is invariant under conjugate transpose. -/
theorem traceNormOp_conjTranspose
    {d : Type u} [Fintype d] [DecidableEq d] (X : Matrix d d ℂ) :
    traceNormOp Xᴴ = traceNormOp X := by
  dsimp [traceNormOp, traceNorm]
  have hEig :
      (Matrix.isHermitian_conjTranspose_mul_self Xᴴ).eigenvalues =
        (Matrix.isHermitian_conjTranspose_mul_self X).eigenvalues := by
    apply
      (Matrix.IsHermitian.eigenvalues_eq_eigenvalues_iff
        (Matrix.isHermitian_conjTranspose_mul_self Xᴴ)
        (Matrix.isHermitian_conjTranspose_mul_self X)).2
    simpa using Matrix.charpoly_mul_comm X Xᴴ
  rw [hEig]
```

## Block-by-block explanation

The explanation below follows the declaration block by block. Each block groups a coherent piece of the definition or proof, so the mathematical structure is easier to see than in a strictly line-oriented reading.

1. Code:
```lean
/-- The concrete trace norm is invariant under conjugate transpose. -/
```
This is a Lean docstring. It is a human-written comment that tells readers what the declaration is meant to express before the formal code begins.

2. Code:
```lean
theorem traceNormOp_conjTranspose
```
This line starts the `traceNormOp_conjTranspose` declaration. Because it begins with `theorem`, Lean now knows what kind of named object is being introduced.

3. Code:
```lean
    {d : Type u} [Fintype d] [DecidableEq d] (X : Matrix d d ℂ) :
```
This line is one local step in the declaration. It either refines the formula being defined or advances the proof by a small algebraic or logical move.  `Matrix d d ℂ` means a square matrix with complex entries; the index type `d` tells Lean which rows and columns exist.  A bracket such as `[Fintype d]` tells Lean that the index set `d` is finite, so sums over all indices make sense.  A bracket such as `[DecidableEq d]` tells Lean that it can decide whether two indices are equal.

4. Code:
```lean
    traceNormOp Xᴴ = traceNormOp X := by
```
This line says that a proof script begins here. Everything indented underneath is a sequence of instructions that Lean will check step by step.  The superscript `ᴴ` means conjugate transpose (also called the adjoint).

5. Code:
```lean
  dsimp [traceNormOp, traceNorm]
```
This line is one local step in the declaration. It either refines the formula being defined or advances the proof by a small algebraic or logical move.

6. Code:
```lean
  have hEig :
```
This line introduces an intermediate claim. The proof pauses to establish a fact that will be used shortly afterwards.

7. Code:
```lean
      (Matrix.isHermitian_conjTranspose_mul_self Xᴴ).eigenvalues =
```
This line is one local step in the declaration. It either refines the formula being defined or advances the proof by a small algebraic or logical move.  The superscript `ᴴ` means conjugate transpose (also called the adjoint).

8. Code:
```lean
        (Matrix.isHermitian_conjTranspose_mul_self X).eigenvalues := by
```
This line says that a proof script begins here. Everything indented underneath is a sequence of instructions that Lean will check step by step.

9. Code:
```lean
    apply
```
This line applies an existing theorem to the current goal. Lean then asks the author to prove the theorem’s hypotheses.

10. Code:
```lean
      (Matrix.IsHermitian.eigenvalues_eq_eigenvalues_iff
```
This line is one local step in the declaration. It either refines the formula being defined or advances the proof by a small algebraic or logical move.

11. Code:
```lean
        (Matrix.isHermitian_conjTranspose_mul_self Xᴴ)
```
This line is one local step in the declaration. It either refines the formula being defined or advances the proof by a small algebraic or logical move.  The superscript `ᴴ` means conjugate transpose (also called the adjoint).

12. Code:
```lean
        (Matrix.isHermitian_conjTranspose_mul_self X)).2
```
This line is one local step in the declaration. It either refines the formula being defined or advances the proof by a small algebraic or logical move.

13. Code:
```lean
    simpa using Matrix.charpoly_mul_comm X Xᴴ
```
This line simplifies the goal using definitions and known equalities. `simpa` means that, after simplification, the desired statement matches a theorem Lean already has.  The superscript `ᴴ` means conjugate transpose (also called the adjoint).

14. Code:
```lean
  rw [hEig]
```
This line uses rewriting. Lean replaces one expression by an equal expression using the lemmas listed in brackets.

## Mathematical summary

Restated without Lean syntax, `traceNormOp_conjTranspose` is the theorem or lemma written above.

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

## Backlinks

- [Back to `INDEX.md`](../../INDEX.md)
- [Back to the `Theorem/Lemma1.lean` section in the index](../../INDEX.md#diamond-theorem-lemma1-lean)
- [Previous declaration in this file](traceNormOp_diagonal.md)
- [Next declaration in this file](traceNormOp_mul_right_isometry.md)