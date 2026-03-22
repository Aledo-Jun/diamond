# hermitian_re_trace_conjTranspose_mul_self_eq_sum_sq_eigenvalues

## Source location

- Original Lean file: `Diamond/Theorem/Lemma1.lean`
- Declaration name: `hermitian_re_trace_conjTranspose_mul_self_eq_sum_sq_eigenvalues`
- Declaration kind: `theorem`

## Why this declaration exists

This theorem records a reusable fact named `hermitian_re_trace_conjTranspose_mul_self_eq_sum_sq_eigenvalues`. Its role is to make the later proof flow easier to state and reuse.

 In the file `Theorem/Lemma1.lean`, it contributes to the proof infrastructure for the first norm inequality and the public theorem `lemma1`. Later proofs call this result by name, so documenting it makes the larger argument readable as a mathematical chain rather than as opaque proof script.

## Original code

```lean
theorem hermitian_re_trace_conjTranspose_mul_self_eq_sum_sq_eigenvalues
    {d : Type u} [Fintype d] [DecidableEq d]
    {A : Matrix d d ℂ} (hA : Matrix.IsHermitian A) :
    Complex.re (Matrix.trace (Aᴴ * A)) = ∑ i, (hA.eigenvalues i) ^ 2 := by
  let U : Matrix d d ℂ := hA.eigenvectorUnitary
  let D : Matrix d d ℂ := Matrix.diagonal (fun i => ((hA.eigenvalues i : ℝ) : ℂ))
  let e := Unitary.conjStarAlgAut ℂ (Matrix d d ℂ) (star hA.eigenvectorUnitary)
  have hdiag : e A = D := by
    simpa [e, D] using hA.conjStarAlgAut_star_eigenvectorUnitary
  have hmul : e (A * A) = e A * e A := by
    exact map_mul e A A
  have hDsq : D * D = (star hA.eigenvectorUnitary : Matrix d d ℂ) * (A * A) * U := by
    calc
      D * D = e (A * A) := by
        rw [← hdiag]
        simpa [hdiag] using hmul.symm
      _ = (star hA.eigenvectorUnitary : Matrix d d ℂ) * (A * A) * U := by
        simp [e, U, Unitary.conjStarAlgAut_apply]
  have hUright : U * (star hA.eigenvectorUnitary : Matrix d d ℂ) = 1 := by
    simpa [U] using (Matrix.mem_unitaryGroup_iff).1 hA.eigenvectorUnitary.property
  have hAA : Aᴴ * A = A * A := by
    simpa [hA.eq]
  calc
    Complex.re (Matrix.trace (Aᴴ * A)) = Complex.re (Matrix.trace (A * A)) := by
      rw [hAA]
    _ = Complex.re (Matrix.trace ((star hA.eigenvectorUnitary : Matrix d d ℂ) * (A * A) * U)) := by
          rw [Matrix.trace_mul_cycle (star hA.eigenvectorUnitary : Matrix d d ℂ) (A * A) U]
          simp [hUright]
    _ = Complex.re (Matrix.trace (D * D)) := by
          rw [hDsq]
    _ = ∑ i, (hA.eigenvalues i) ^ 2 := by
          simp [D, Matrix.trace, pow_two]
```

## Block-by-block explanation

The explanation below follows the declaration block by block. Each block groups a coherent piece of the definition or proof, so the mathematical structure is easier to see than in a strictly line-oriented reading.

1. Code:
```lean
theorem hermitian_re_trace_conjTranspose_mul_self_eq_sum_sq_eigenvalues
```
This line starts the `hermitian_re_trace_conjTranspose_mul_self_eq_sum_sq_eigenvalues` declaration. Because it begins with `theorem`, Lean now knows what kind of named object is being introduced.

2. Code:
```lean
    {d : Type u} [Fintype d] [DecidableEq d]
```
This line is one local step in the declaration. It either refines the formula being defined or advances the proof by a small algebraic or logical move.  A bracket such as `[Fintype d]` tells Lean that the index set `d` is finite, so sums over all indices make sense.  A bracket such as `[DecidableEq d]` tells Lean that it can decide whether two indices are equal.

3. Code:
```lean
    {A : Matrix d d ℂ} (hA : Matrix.IsHermitian A) :
```
This line is one local step in the declaration. It either refines the formula being defined or advances the proof by a small algebraic or logical move.  `Matrix d d ℂ` means a square matrix with complex entries; the index type `d` tells Lean which rows and columns exist.

4. Code:
```lean
    Complex.re (Matrix.trace (Aᴴ * A)) = ∑ i, (hA.eigenvalues i) ^ 2 := by
```
This line says that a proof script begins here. Everything indented underneath is a sequence of instructions that Lean will check step by step.  The superscript `ᴴ` means conjugate transpose (also called the adjoint).

5. Code:
```lean
  let U : Matrix d d ℂ := hA.eigenvectorUnitary
```
This line gives a temporary name to an expression. Doing that makes later lines shorter and easier to read.  `Matrix d d ℂ` means a square matrix with complex entries; the index type `d` tells Lean which rows and columns exist.

6. Code:
```lean
  let D : Matrix d d ℂ := Matrix.diagonal (fun i => ((hA.eigenvalues i : ℝ) : ℂ))
```
This line gives a temporary name to an expression. Doing that makes later lines shorter and easier to read.  `Matrix d d ℂ` means a square matrix with complex entries; the index type `d` tells Lean which rows and columns exist.

7. Code:
```lean
  let e := Unitary.conjStarAlgAut ℂ (Matrix d d ℂ) (star hA.eigenvectorUnitary)
```
This line gives a temporary name to an expression. Doing that makes later lines shorter and easier to read.  `Matrix d d ℂ` means a square matrix with complex entries; the index type `d` tells Lean which rows and columns exist.

8. Code:
```lean
  have hdiag : e A = D := by
```
This line says that a proof script begins here. Everything indented underneath is a sequence of instructions that Lean will check step by step.

9. Code:
```lean
    simpa [e, D] using hA.conjStarAlgAut_star_eigenvectorUnitary
```
This line simplifies the goal using definitions and known equalities. `simpa` means that, after simplification, the desired statement matches a theorem Lean already has.

10. Code:
```lean
  have hmul : e (A * A) = e A * e A := by
```
This line says that a proof script begins here. Everything indented underneath is a sequence of instructions that Lean will check step by step.

11. Code:
```lean
    exact map_mul e A A
```
This line finishes the current goal by giving Lean the exact theorem, lemma, or term that proves it.

12. Code:
```lean
  have hDsq : D * D = (star hA.eigenvectorUnitary : Matrix d d ℂ) * (A * A) * U := by
```
This line says that a proof script begins here. Everything indented underneath is a sequence of instructions that Lean will check step by step.  `Matrix d d ℂ` means a square matrix with complex entries; the index type `d` tells Lean which rows and columns exist.

13. Code:
```lean
    calc
```
This line begins a chained calculation. Each displayed step that follows must be justified by the indented proof after `:= by`.

14. Code:
```lean
      D * D = e (A * A) := by
```
This line says that a proof script begins here. Everything indented underneath is a sequence of instructions that Lean will check step by step.

15. Code:
```lean
        rw [← hdiag]
```
This line uses rewriting. Lean replaces one expression by an equal expression using the lemmas listed in brackets.

16. Code:
```lean
        simpa [hdiag] using hmul.symm
```
This line simplifies the goal using definitions and known equalities. `simpa` means that, after simplification, the desired statement matches a theorem Lean already has.

17. Code:
```lean
      _ = (star hA.eigenvectorUnitary : Matrix d d ℂ) * (A * A) * U := by
```
This line says that a proof script begins here. Everything indented underneath is a sequence of instructions that Lean will check step by step.  `Matrix d d ℂ` means a square matrix with complex entries; the index type `d` tells Lean which rows and columns exist.

18. Code:
```lean
        simp [e, U, Unitary.conjStarAlgAut_apply]
```
This line simplifies the goal using definitions and known equalities. `simpa` means that, after simplification, the desired statement matches a theorem Lean already has.

19. Code:
```lean
  have hUright : U * (star hA.eigenvectorUnitary : Matrix d d ℂ) = 1 := by
```
This line says that a proof script begins here. Everything indented underneath is a sequence of instructions that Lean will check step by step.  `Matrix d d ℂ` means a square matrix with complex entries; the index type `d` tells Lean which rows and columns exist.

20. Code:
```lean
    simpa [U] using (Matrix.mem_unitaryGroup_iff).1 hA.eigenvectorUnitary.property
```
This line simplifies the goal using definitions and known equalities. `simpa` means that, after simplification, the desired statement matches a theorem Lean already has.

21. Code:
```lean
  have hAA : Aᴴ * A = A * A := by
```
This line says that a proof script begins here. Everything indented underneath is a sequence of instructions that Lean will check step by step.  The superscript `ᴴ` means conjugate transpose (also called the adjoint).

22. Code:
```lean
    simpa [hA.eq]
```
This line simplifies the goal using definitions and known equalities. `simpa` means that, after simplification, the desired statement matches a theorem Lean already has.

23. Code:
```lean
  calc
```
This line begins a chained calculation. Each displayed step that follows must be justified by the indented proof after `:= by`.

24. Code:
```lean
    Complex.re (Matrix.trace (Aᴴ * A)) = Complex.re (Matrix.trace (A * A)) := by
```
This line says that a proof script begins here. Everything indented underneath is a sequence of instructions that Lean will check step by step.  The superscript `ᴴ` means conjugate transpose (also called the adjoint).

25. Code:
```lean
      rw [hAA]
```
This line uses rewriting. Lean replaces one expression by an equal expression using the lemmas listed in brackets.

26. Code:
```lean
    _ = Complex.re (Matrix.trace ((star hA.eigenvectorUnitary : Matrix d d ℂ) * (A * A) * U)) := by
```
This line says that a proof script begins here. Everything indented underneath is a sequence of instructions that Lean will check step by step.  `Matrix d d ℂ` means a square matrix with complex entries; the index type `d` tells Lean which rows and columns exist.

27. Code:
```lean
          rw [Matrix.trace_mul_cycle (star hA.eigenvectorUnitary : Matrix d d ℂ) (A * A) U]
```
This line uses rewriting. Lean replaces one expression by an equal expression using the lemmas listed in brackets.  `Matrix d d ℂ` means a square matrix with complex entries; the index type `d` tells Lean which rows and columns exist.

28. Code:
```lean
          simp [hUright]
```
This line simplifies the goal using definitions and known equalities. `simpa` means that, after simplification, the desired statement matches a theorem Lean already has.

29. Code:
```lean
    _ = Complex.re (Matrix.trace (D * D)) := by
```
This line says that a proof script begins here. Everything indented underneath is a sequence of instructions that Lean will check step by step.

30. Code:
```lean
          rw [hDsq]
```
This line uses rewriting. Lean replaces one expression by an equal expression using the lemmas listed in brackets.

31. Code:
```lean
    _ = ∑ i, (hA.eigenvalues i) ^ 2 := by
```
This line says that a proof script begins here. Everything indented underneath is a sequence of instructions that Lean will check step by step.

32. Code:
```lean
          simp [D, Matrix.trace, pow_two]
```
This line simplifies the goal using definitions and known equalities. `simpa` means that, after simplification, the desired statement matches a theorem Lean already has.

## Mathematical summary

Restated without Lean syntax, `hermitian_re_trace_conjTranspose_mul_self_eq_sum_sq_eigenvalues` is the theorem or lemma written above.

- State the desired identity or inequality in Lean’s syntax.
- Introduce temporary names and intermediate claims that organize the argument.
- Use rewriting, simplification, and earlier lemmas to reduce the goal to standard matrix or norm manipulations.
- Close the remaining algebraic or order-theoretic steps with Lean’s proof tactics.

## Dependencies and downstream use

### Earlier declarations this depends on
- This declaration does not explicitly cite an earlier named declaration from the documented tree; it mostly uses Lean primitives or local algebraic steps.

### Later declarations that use this one
- [`lemma1`](lemma1.md) in `Theorem/Lemma1.lean`
- [`lemma1_eq_imp_rank_two`](../../PositiveGap/NotTight/lemma1_eq_imp_rank_two.md) in `PositiveGap/NotTight.lean`

## Backlinks

- [Back to `INDEX.md`](../../INDEX.md)
- [Back to the `Theorem/Lemma1.lean` section in the index](../../INDEX.md#diamond-theorem-lemma1-lean)
- [Previous declaration in this file](hsNorm_sq_eq_re_trace_conjTranspose_mul_self.md)
- [Next declaration in this file](traceNormOp_mul_left_isometry.md)