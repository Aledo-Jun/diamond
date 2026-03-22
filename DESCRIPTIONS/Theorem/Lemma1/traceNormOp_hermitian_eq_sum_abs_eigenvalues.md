# traceNormOp_hermitian_eq_sum_abs_eigenvalues

## Source location

- Original Lean file: `Diamond/Theorem/Lemma1.lean`
- Declaration name: `traceNormOp_hermitian_eq_sum_abs_eigenvalues`
- Declaration kind: `theorem`

## Why this declaration exists

For Hermitian matrices, the concrete trace norm is the sum of the absolute eigenvalues.

 In the file `Theorem/Lemma1.lean`, it contributes to the proof infrastructure for the first norm inequality and the public theorem `lemma1`. Later proofs call this result by name, so documenting it makes the larger argument readable as a mathematical chain rather than as opaque proof script.

## Original code

```lean
/-- For Hermitian matrices, the concrete trace norm is the sum of the absolute eigenvalues. -/
theorem traceNormOp_hermitian_eq_sum_abs_eigenvalues
    {d : Type u} [Fintype d] [DecidableEq d]
    {A : Matrix d d ℂ} (hA : Matrix.IsHermitian A) :
    traceNormOp A = ∑ i, |hA.eigenvalues i| := by
  let U : Matrix d d ℂ := hA.eigenvectorUnitary
  let Ustar : Matrix d d ℂ := star hA.eigenvectorUnitary
  let D : Matrix d d ℂ := Matrix.diagonal (fun i => ((hA.eigenvalues i : ℝ) : ℂ))
  have hU_left : Uᴴ * U = 1 := by
    exact (Matrix.mem_unitaryGroup_iff').1 hA.eigenvectorUnitary.property
  have hUstar_right : Ustar * Ustarᴴ = 1 := by
    exact (Matrix.mem_unitaryGroup_iff).1 (star hA.eigenvectorUnitary).property
  calc
    traceNormOp A = traceNormOp (U * (D * Ustar)) := by
      simpa [Unitary.conjStarAlgAut_apply, U, Ustar, D, Matrix.mul_assoc] using
        congrArg traceNormOp hA.spectral_theorem
    _ = traceNormOp (D * Ustar) := by
      exact traceNormOp_mul_left_isometry (U := U) (X := D * Ustar) hU_left
    _ = traceNormOp D := by
      exact traceNormOp_mul_right_isometry (X := D) (U := Ustar) hUstar_right
    _ = ∑ i, |hA.eigenvalues i| := by
      simp [D, traceNormOp_diagonal]
```

## Block-by-block explanation

The explanation below follows the declaration block by block. Each block groups a coherent piece of the definition or proof, so the mathematical structure is easier to see than in a strictly line-oriented reading.

1. Code:
```lean
/-- For Hermitian matrices, the concrete trace norm is the sum of the absolute eigenvalues. -/
```
This is a Lean docstring. It is a human-written comment that tells readers what the declaration is meant to express before the formal code begins.

2. Code:
```lean
theorem traceNormOp_hermitian_eq_sum_abs_eigenvalues
```
This line starts the `traceNormOp_hermitian_eq_sum_abs_eigenvalues` declaration. Because it begins with `theorem`, Lean now knows what kind of named object is being introduced.

3. Code:
```lean
    {d : Type u} [Fintype d] [DecidableEq d]
```
This line is one local step in the declaration. It either refines the formula being defined or advances the proof by a small algebraic or logical move.  A bracket such as `[Fintype d]` tells Lean that the index set `d` is finite, so sums over all indices make sense.  A bracket such as `[DecidableEq d]` tells Lean that it can decide whether two indices are equal.

4. Code:
```lean
    {A : Matrix d d ℂ} (hA : Matrix.IsHermitian A) :
```
This line is one local step in the declaration. It either refines the formula being defined or advances the proof by a small algebraic or logical move.  `Matrix d d ℂ` means a square matrix with complex entries; the index type `d` tells Lean which rows and columns exist.

5. Code:
```lean
    traceNormOp A = ∑ i, |hA.eigenvalues i| := by
```
This line says that a proof script begins here. Everything indented underneath is a sequence of instructions that Lean will check step by step.

6. Code:
```lean
  let U : Matrix d d ℂ := hA.eigenvectorUnitary
```
This line gives a temporary name to an expression. Doing that makes later lines shorter and easier to read.  `Matrix d d ℂ` means a square matrix with complex entries; the index type `d` tells Lean which rows and columns exist.

7. Code:
```lean
  let Ustar : Matrix d d ℂ := star hA.eigenvectorUnitary
```
This line gives a temporary name to an expression. Doing that makes later lines shorter and easier to read.  `Matrix d d ℂ` means a square matrix with complex entries; the index type `d` tells Lean which rows and columns exist.

8. Code:
```lean
  let D : Matrix d d ℂ := Matrix.diagonal (fun i => ((hA.eigenvalues i : ℝ) : ℂ))
```
This line gives a temporary name to an expression. Doing that makes later lines shorter and easier to read.  `Matrix d d ℂ` means a square matrix with complex entries; the index type `d` tells Lean which rows and columns exist.

9. Code:
```lean
  have hU_left : Uᴴ * U = 1 := by
```
This line says that a proof script begins here. Everything indented underneath is a sequence of instructions that Lean will check step by step.  The superscript `ᴴ` means conjugate transpose (also called the adjoint).

10. Code:
```lean
    exact (Matrix.mem_unitaryGroup_iff').1 hA.eigenvectorUnitary.property
```
This line finishes the current goal by giving Lean the exact theorem, lemma, or term that proves it.

11. Code:
```lean
  have hUstar_right : Ustar * Ustarᴴ = 1 := by
```
This line says that a proof script begins here. Everything indented underneath is a sequence of instructions that Lean will check step by step.  The superscript `ᴴ` means conjugate transpose (also called the adjoint).

12. Code:
```lean
    exact (Matrix.mem_unitaryGroup_iff).1 (star hA.eigenvectorUnitary).property
```
This line finishes the current goal by giving Lean the exact theorem, lemma, or term that proves it.

13. Code:
```lean
  calc
```
This line begins a chained calculation. Each displayed step that follows must be justified by the indented proof after `:= by`.

14. Code:
```lean
    traceNormOp A = traceNormOp (U * (D * Ustar)) := by
```
This line says that a proof script begins here. Everything indented underneath is a sequence of instructions that Lean will check step by step.

15. Code:
```lean
      simpa [Unitary.conjStarAlgAut_apply, U, Ustar, D, Matrix.mul_assoc] using
```
This line simplifies the goal using definitions and known equalities. `simpa` means that, after simplification, the desired statement matches a theorem Lean already has.

16. Code:
```lean
        congrArg traceNormOp hA.spectral_theorem
```
This line applies the same function to both sides of a known equality, producing a new equality better suited to the current goal.

17. Code:
```lean
    _ = traceNormOp (D * Ustar) := by
```
This line says that a proof script begins here. Everything indented underneath is a sequence of instructions that Lean will check step by step.

18. Code:
```lean
      exact traceNormOp_mul_left_isometry (U := U) (X := D * Ustar) hU_left
```
This line finishes the current goal by giving Lean the exact theorem, lemma, or term that proves it.

19. Code:
```lean
    _ = traceNormOp D := by
```
This line says that a proof script begins here. Everything indented underneath is a sequence of instructions that Lean will check step by step.

20. Code:
```lean
      exact traceNormOp_mul_right_isometry (X := D) (U := Ustar) hUstar_right
```
This line finishes the current goal by giving Lean the exact theorem, lemma, or term that proves it.

21. Code:
```lean
    _ = ∑ i, |hA.eigenvalues i| := by
```
This line says that a proof script begins here. Everything indented underneath is a sequence of instructions that Lean will check step by step.

22. Code:
```lean
      simp [D, traceNormOp_diagonal]
```
This line simplifies the goal using definitions and known equalities. `simpa` means that, after simplification, the desired statement matches a theorem Lean already has.

## Mathematical summary

Restated without Lean syntax, `traceNormOp_hermitian_eq_sum_abs_eigenvalues` is the theorem or lemma written above.

- State the desired identity or inequality in Lean’s syntax.
- Introduce temporary names and intermediate claims that organize the argument.
- Use rewriting, simplification, and earlier lemmas to reduce the goal to standard matrix or norm manipulations.
- Close the remaining algebraic or order-theoretic steps with Lean’s proof tactics.

## Dependencies and downstream use

### Earlier declarations this depends on
- [`traceNormOp`](../../Setups/traceNormOp.md) from `Setups.lean`
- [`traceNormOp_mul_left_isometry`](traceNormOp_mul_left_isometry.md) from `Theorem/Lemma1.lean`
- [`traceNormOp_diagonal`](traceNormOp_diagonal.md) from `Theorem/Lemma1.lean`
- [`traceNormOp_mul_right_isometry`](traceNormOp_mul_right_isometry.md) from `Theorem/Lemma1.lean`

### Later declarations that use this one
- [`lemma1`](lemma1.md) in `Theorem/Lemma1.lean`
- [`traceNormOp_posSemidef_eq_trace`](traceNormOp_posSemidef_eq_trace.md) in `Theorem/Lemma1.lean`
- [`traceNormOp_sub_density_le_two`](traceNormOp_sub_density_le_two.md) in `Theorem/Lemma1.lean`
- [`lemma1_eq_imp_rank_two`](../../PositiveGap/NotTight/lemma1_eq_imp_rank_two.md) in `PositiveGap/NotTight.lean`

## Backlinks

- [Back to `INDEX.md`](../../INDEX.md)
- [Back to the `Theorem/Lemma1.lean` section in the index](../../INDEX.md#diamond-theorem-lemma1-lean)
- [Previous declaration in this file](traceNormOp_mul_right_isometry.md)
- [Next declaration in this file](lemma1.md)