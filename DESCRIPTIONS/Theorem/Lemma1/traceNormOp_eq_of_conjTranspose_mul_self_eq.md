# traceNormOp_eq_of_conjTranspose_mul_self_eq

## Source location

- Original Lean file: `Diamond/Theorem/Lemma1.lean`
- Declaration name: `traceNormOp_eq_of_conjTranspose_mul_self_eq`
- Declaration kind: `theorem`

## Why this declaration exists

The concrete trace norm depends only on `Xᴴ * X`.

 In the file `Theorem/Lemma1.lean`, it contributes to the proof infrastructure for the first norm inequality and the public theorem `lemma1`. Later proofs call this result by name, so documenting it makes the larger argument readable as a mathematical chain rather than as opaque proof script.

## Original code

```lean
/-- The concrete trace norm depends only on `Xᴴ * X`. -/
private theorem traceNormOp_eq_of_conjTranspose_mul_self_eq
    {d : Type u} [Fintype d] [DecidableEq d]
    {A B : Matrix d d ℂ} (hAB : Aᴴ * A = Bᴴ * B) :
    traceNormOp A = traceNormOp B := by
  dsimp [traceNormOp, traceNorm]
  have hEig :
      (Matrix.isHermitian_conjTranspose_mul_self A).eigenvalues =
        (Matrix.isHermitian_conjTranspose_mul_self B).eigenvalues := by
    apply
      (Matrix.IsHermitian.eigenvalues_eq_eigenvalues_iff
        (Matrix.isHermitian_conjTranspose_mul_self A)
        (Matrix.isHermitian_conjTranspose_mul_self B)).2
    exact congrArg Matrix.charpoly hAB
  rw [hEig]
```

## Block-by-block explanation

The explanation below follows the declaration block by block. Each block groups a coherent piece of the definition or proof, so the mathematical structure is easier to see than in a strictly line-oriented reading.

1. Code:
```lean
/-- The concrete trace norm depends only on `Xᴴ * X`. -/
```
This is a Lean docstring. It is a human-written comment that tells readers what the declaration is meant to express before the formal code begins.

2. Code:
```lean
private theorem traceNormOp_eq_of_conjTranspose_mul_self_eq
```
This line starts the `traceNormOp_eq_of_conjTranspose_mul_self_eq` declaration. Because it begins with `theorem`, Lean now knows what kind of named object is being introduced.

3. Code:
```lean
    {d : Type u} [Fintype d] [DecidableEq d]
```
This line is one local step in the declaration. It either refines the formula being defined or advances the proof by a small algebraic or logical move.  A bracket such as `[Fintype d]` tells Lean that the index set `d` is finite, so sums over all indices make sense.  A bracket such as `[DecidableEq d]` tells Lean that it can decide whether two indices are equal.

4. Code:
```lean
    {A B : Matrix d d ℂ} (hAB : Aᴴ * A = Bᴴ * B) :
```
This line is one local step in the declaration. It either refines the formula being defined or advances the proof by a small algebraic or logical move.  `Matrix d d ℂ` means a square matrix with complex entries; the index type `d` tells Lean which rows and columns exist.  The superscript `ᴴ` means conjugate transpose (also called the adjoint).

5. Code:
```lean
    traceNormOp A = traceNormOp B := by
```
This line says that a proof script begins here. Everything indented underneath is a sequence of instructions that Lean will check step by step.

6. Code:
```lean
  dsimp [traceNormOp, traceNorm]
```
This line is one local step in the declaration. It either refines the formula being defined or advances the proof by a small algebraic or logical move.

7. Code:
```lean
  have hEig :
```
This line introduces an intermediate claim. The proof pauses to establish a fact that will be used shortly afterwards.

8. Code:
```lean
      (Matrix.isHermitian_conjTranspose_mul_self A).eigenvalues =
```
This line is one local step in the declaration. It either refines the formula being defined or advances the proof by a small algebraic or logical move.

9. Code:
```lean
        (Matrix.isHermitian_conjTranspose_mul_self B).eigenvalues := by
```
This line says that a proof script begins here. Everything indented underneath is a sequence of instructions that Lean will check step by step.

10. Code:
```lean
    apply
```
This line applies an existing theorem to the current goal. Lean then asks the author to prove the theorem’s hypotheses.

11. Code:
```lean
      (Matrix.IsHermitian.eigenvalues_eq_eigenvalues_iff
```
This line is one local step in the declaration. It either refines the formula being defined or advances the proof by a small algebraic or logical move.

12. Code:
```lean
        (Matrix.isHermitian_conjTranspose_mul_self A)
```
This line is one local step in the declaration. It either refines the formula being defined or advances the proof by a small algebraic or logical move.

13. Code:
```lean
        (Matrix.isHermitian_conjTranspose_mul_self B)).2
```
This line is one local step in the declaration. It either refines the formula being defined or advances the proof by a small algebraic or logical move.

14. Code:
```lean
    exact congrArg Matrix.charpoly hAB
```
This line finishes the current goal by giving Lean the exact theorem, lemma, or term that proves it.

15. Code:
```lean
  rw [hEig]
```
This line uses rewriting. Lean replaces one expression by an equal expression using the lemmas listed in brackets.

## Mathematical summary

Restated without Lean syntax, `traceNormOp_eq_of_conjTranspose_mul_self_eq` is the theorem or lemma written above.

- State the desired identity or inequality in Lean’s syntax.
- Introduce temporary names and intermediate claims that organize the argument.
- Use rewriting, simplification, and earlier lemmas to reduce the goal to standard matrix or norm manipulations.
- Close the remaining algebraic or order-theoretic steps with Lean’s proof tactics.

## Dependencies and downstream use

### Earlier declarations this depends on
- [`traceNorm`](../../Setups/traceNorm.md) from `Setups.lean`
- [`traceNormOp`](../../Setups/traceNormOp.md) from `Setups.lean`

### Later declarations that use this one
- No later documented declaration mentions this name explicitly.

## Backlinks

- [Back to `INDEX.md`](../../INDEX.md)
- [Back to the `Theorem/Lemma1.lean` section in the index](../../INDEX.md#diamond-theorem-lemma1-lean)
- [Previous declaration in this file](traceNormOp_sub_density_le_two.md)