# hsNorm_sq_eq_re_trace_conjTranspose_mul_self

## Source location

- Original Lean file: `Diamond/Theorem/Lemma1.lean`
- Declaration name: `hsNorm_sq_eq_re_trace_conjTranspose_mul_self`
- Declaration kind: `theorem`

## Why this declaration exists

This theorem records a reusable fact named `hsNorm_sq_eq_re_trace_conjTranspose_mul_self`. Its role is to make the later proof flow easier to state and reuse.

 In the file `Theorem/Lemma1.lean`, it contributes to the proof infrastructure for the first norm inequality and the public theorem `lemma1`. Later proofs call this result by name, so documenting it makes the larger argument readable as a mathematical chain rather than as opaque proof script.

## Original code

```lean
theorem hsNorm_sq_eq_re_trace_conjTranspose_mul_self
    {m n : Type u} [Fintype m] [DecidableEq m] [Fintype n] [DecidableEq n]
    (X : Matrix m n ℂ) :
    hsNormOp X ^ 2 = Complex.re (Matrix.trace (Xᴴ * X)) := by
  change ‖X‖ ^ 2 = Complex.re (Matrix.trace (Xᴴ * X))
  rw [Matrix.frobenius_norm_def]
  have hnonneg : 0 ≤ (∑ i, ∑ j, ‖X i j‖ ^ (2 : ℝ) : ℝ) := by
    positivity
  have htrace :
      Complex.re (Matrix.trace (Xᴴ * X)) =
        ∑ x : n, ∑ y : m, ((X y x).re * (X y x).re + (X y x).im * (X y x).im) := by
    simp [Matrix.trace, Matrix.mul_apply, Complex.mul_re]
  calc
    ((∑ i, ∑ j, ‖X i j‖ ^ (2 : ℝ) : ℝ) ^ (1 / 2 : ℝ)) ^ 2
      = (∑ i, ∑ j, ‖X i j‖ ^ (2 : ℝ) : ℝ) := by
          rw [← Real.sqrt_eq_rpow (∑ i, ∑ j, ‖X i j‖ ^ (2 : ℝ) : ℝ)]
          simpa [pow_two] using Real.sq_sqrt hnonneg
    _ = ∑ i, ∑ j, ((X i j).re * (X i j).re + (X i j).im * (X i j).im) := by
          refine Finset.sum_congr rfl ?_
          intro i hi
          refine Finset.sum_congr rfl ?_
          intro j hj
          simpa [Complex.normSq_apply] using (Complex.normSq_eq_norm_sq (X i j)).symm
    _ = ∑ x : n, ∑ y : m, ((X y x).re * (X y x).re + (X y x).im * (X y x).im) := by
          simpa using
            (Finset.sum_comm
              (s := (Finset.univ : Finset m))
              (t := (Finset.univ : Finset n))
              (f := fun i j => ((X i j).re * (X i j).re + (X i j).im * (X i j).im)))
    _ = Complex.re (Matrix.trace (Xᴴ * X)) := by
          exact htrace.symm
```

## Line-by-line explanation

The explanation below follows the declaration one physical line at a time. For long proofs, some lines are tiny bookkeeping steps; those are still explained, but briefly.

1. Code:
```lean
theorem hsNorm_sq_eq_re_trace_conjTranspose_mul_self
```
This line starts the `hsNorm_sq_eq_re_trace_conjTranspose_mul_self` declaration. Because it begins with `theorem`, Lean now knows what kind of named object is being introduced.

2. Code:
```lean
    {m n : Type u} [Fintype m] [DecidableEq m] [Fintype n] [DecidableEq n]
```
This line is one local step in the declaration. It either refines the formula being defined or advances the proof by a small algebraic or logical move.  A bracket such as `[Fintype d]` tells Lean that the index set `d` is finite, so sums over all indices make sense.  A bracket such as `[DecidableEq d]` tells Lean that it can decide whether two indices are equal.

3. Code:
```lean
    (X : Matrix m n ℂ) :
```
This line is one local step in the declaration. It either refines the formula being defined or advances the proof by a small algebraic or logical move.  `Matrix d d ℂ` means a square matrix with complex entries; the index type `d` tells Lean which rows and columns exist.

4. Code:
```lean
    hsNormOp X ^ 2 = Complex.re (Matrix.trace (Xᴴ * X)) := by
```
This line says that a proof script begins here. Everything indented underneath is a sequence of instructions that Lean will check step by step.  The superscript `ᴴ` means conjugate transpose (also called the adjoint).

5. Code:
```lean
  change ‖X‖ ^ 2 = Complex.re (Matrix.trace (Xᴴ * X))
```
This line replaces the current goal by a definitionally equal goal that is easier to manipulate.  The superscript `ᴴ` means conjugate transpose (also called the adjoint).

6. Code:
```lean
  rw [Matrix.frobenius_norm_def]
```
This line uses rewriting. Lean replaces one expression by an equal expression using the lemmas listed in brackets.

7. Code:
```lean
  have hnonneg : 0 ≤ (∑ i, ∑ j, ‖X i j‖ ^ (2 : ℝ) : ℝ) := by
```
This line says that a proof script begins here. Everything indented underneath is a sequence of instructions that Lean will check step by step.

8. Code:
```lean
    positivity
```
This line asks Lean to prove that the displayed quantity is positive or nonnegative using standard positivity rules.

9. Code:
```lean
  have htrace :
```
This line introduces an intermediate claim. The proof pauses to establish a fact that will be used shortly afterwards.

10. Code:
```lean
      Complex.re (Matrix.trace (Xᴴ * X)) =
```
This line is one local step in the declaration. It either refines the formula being defined or advances the proof by a small algebraic or logical move.  The superscript `ᴴ` means conjugate transpose (also called the adjoint).

11. Code:
```lean
        ∑ x : n, ∑ y : m, ((X y x).re * (X y x).re + (X y x).im * (X y x).im) := by
```
This line says that a proof script begins here. Everything indented underneath is a sequence of instructions that Lean will check step by step.

12. Code:
```lean
    simp [Matrix.trace, Matrix.mul_apply, Complex.mul_re]
```
This line simplifies the goal using definitions and known equalities. `simpa` means that, after simplification, the desired statement matches a theorem Lean already has.

13. Code:
```lean
  calc
```
This line begins a chained calculation. Each displayed step that follows must be justified by the indented proof after `:= by`.

14. Code:
```lean
    ((∑ i, ∑ j, ‖X i j‖ ^ (2 : ℝ) : ℝ) ^ (1 / 2 : ℝ)) ^ 2
```
This line is one local step in the declaration. It either refines the formula being defined or advances the proof by a small algebraic or logical move.

15. Code:
```lean
      = (∑ i, ∑ j, ‖X i j‖ ^ (2 : ℝ) : ℝ) := by
```
This line says that a proof script begins here. Everything indented underneath is a sequence of instructions that Lean will check step by step.

16. Code:
```lean
          rw [← Real.sqrt_eq_rpow (∑ i, ∑ j, ‖X i j‖ ^ (2 : ℝ) : ℝ)]
```
This line uses rewriting. Lean replaces one expression by an equal expression using the lemmas listed in brackets.

17. Code:
```lean
          simpa [pow_two] using Real.sq_sqrt hnonneg
```
This line simplifies the goal using definitions and known equalities. `simpa` means that, after simplification, the desired statement matches a theorem Lean already has.

18. Code:
```lean
    _ = ∑ i, ∑ j, ((X i j).re * (X i j).re + (X i j).im * (X i j).im) := by
```
This line says that a proof script begins here. Everything indented underneath is a sequence of instructions that Lean will check step by step.

19. Code:
```lean
          refine Finset.sum_congr rfl ?_
```
This line is a more controlled version of `apply`. It sets up the proof with a partly specified argument and leaves smaller goals to solve next.

20. Code:
```lean
          intro i hi
```
This line introduces the variable or hypothesis named here into the proof context. In ordinary mathematical prose, it is the same as saying “let” or “assume”.

21. Code:
```lean
          refine Finset.sum_congr rfl ?_
```
This line is a more controlled version of `apply`. It sets up the proof with a partly specified argument and leaves smaller goals to solve next.

22. Code:
```lean
          intro j hj
```
This line introduces the variable or hypothesis named here into the proof context. In ordinary mathematical prose, it is the same as saying “let” or “assume”.

23. Code:
```lean
          simpa [Complex.normSq_apply] using (Complex.normSq_eq_norm_sq (X i j)).symm
```
This line simplifies the goal using definitions and known equalities. `simpa` means that, after simplification, the desired statement matches a theorem Lean already has.

24. Code:
```lean
    _ = ∑ x : n, ∑ y : m, ((X y x).re * (X y x).re + (X y x).im * (X y x).im) := by
```
This line says that a proof script begins here. Everything indented underneath is a sequence of instructions that Lean will check step by step.

25. Code:
```lean
          simpa using
```
This line simplifies the goal using definitions and known equalities. `simpa` means that, after simplification, the desired statement matches a theorem Lean already has.

26. Code:
```lean
            (Finset.sum_comm
```
This line is one local step in the declaration. It either refines the formula being defined or advances the proof by a small algebraic or logical move.

27. Code:
```lean
              (s := (Finset.univ : Finset m))
```
This line is one local step in the declaration. It either refines the formula being defined or advances the proof by a small algebraic or logical move.

28. Code:
```lean
              (t := (Finset.univ : Finset n))
```
This line is one local step in the declaration. It either refines the formula being defined or advances the proof by a small algebraic or logical move.

29. Code:
```lean
              (f := fun i j => ((X i j).re * (X i j).re + (X i j).im * (X i j).im)))
```
This line is one local step in the declaration. It either refines the formula being defined or advances the proof by a small algebraic or logical move.

30. Code:
```lean
    _ = Complex.re (Matrix.trace (Xᴴ * X)) := by
```
This line says that a proof script begins here. Everything indented underneath is a sequence of instructions that Lean will check step by step.  The superscript `ᴴ` means conjugate transpose (also called the adjoint).

31. Code:
```lean
          exact htrace.symm
```
This line finishes the current goal by giving Lean the exact theorem, lemma, or term that proves it.

## Mathematical summary

Restated without Lean syntax, `hsNorm_sq_eq_re_trace_conjTranspose_mul_self` is the theorem or lemma written above.

- State the desired identity or inequality in Lean’s syntax.
- Introduce temporary names and intermediate claims that organize the argument.
- Use rewriting, simplification, and earlier lemmas to reduce the goal to standard matrix or norm manipulations.
- Close the remaining algebraic or order-theoretic steps with Lean’s proof tactics.

## Dependencies and downstream use

### Earlier declarations this depends on
- [`hsNormOp`](../../Setups/hsNormOp.md) from `Setups.lean`

### Later declarations that use this one
- [`lemma1`](lemma1.md) in `Theorem/Lemma1.lean`
- [`hsNorm_sq_eq_re_trace_conjTranspose_mul_self`](../Lemma2/hsNorm_sq_eq_re_trace_conjTranspose_mul_self.md) in `Theorem/Lemma2.lean`
- [`lemma2`](../Lemma2/lemma2.md) in `Theorem/Lemma2.lean`
- [`lemma1_eq_imp_rank_two`](../../PositiveGap/NotTight/lemma1_eq_imp_rank_two.md) in `PositiveGap/NotTight.lean`
- [`lemma2_eq_imp_full_rank`](../../PositiveGap/NotTight/lemma2_eq_imp_full_rank.md) in `PositiveGap/NotTight.lean`

## Backlinks

- [Back to `INDEX.md`](../../INDEX.md)
- [Back to the `Theorem/Lemma1.lean` section in the index](../../INDEX.md#diamond-theorem-lemma1-lean)
- [Next declaration in this file](hermitian_re_trace_conjTranspose_mul_self_eq_sum_sq_eigenvalues.md)