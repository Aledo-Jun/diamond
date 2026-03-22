# traceNormOp_posSemidef_eq_trace

## Source location

- Original Lean file: `Diamond/Theorem/Lemma1.lean`
- Declaration name: `traceNormOp_posSemidef_eq_trace`
- Declaration kind: `theorem`

## Why this declaration exists

Positive semidefinite matrices have trace norm equal to the real trace.

 In the file `Theorem/Lemma1.lean`, it contributes to the proof infrastructure for the first norm inequality and the public theorem `lemma1`. Later proofs call this result by name, so documenting it makes the larger argument readable as a mathematical chain rather than as opaque proof script.

## Original code

```lean
/-- Positive semidefinite matrices have trace norm equal to the real trace. -/
private theorem traceNormOp_posSemidef_eq_trace
    {d : Type u} [Fintype d] [DecidableEq d]
    {A : Matrix d d ℂ} (hA : A.PosSemidef) :
    traceNormOp A = Complex.re (Matrix.trace A) := by
  calc
    traceNormOp A = ∑ i, |hA.isHermitian.eigenvalues i| := by
      simpa using traceNormOp_hermitian_eq_sum_abs_eigenvalues hA.isHermitian
    _ = ∑ i, hA.isHermitian.eigenvalues i := by
      refine Finset.sum_congr rfl ?_
      intro i hi
      exact abs_of_nonneg (hA.eigenvalues_nonneg i)
    _ = Complex.re (Matrix.trace A) := by
      rw [hA.isHermitian.trace_eq_sum_eigenvalues]
      simp
```

## Block-by-block explanation

The explanation below follows the declaration block by block. Each block groups a coherent piece of the definition or proof, so the mathematical structure is easier to see than in a strictly line-oriented reading.

1. Code:
```lean
/-- Positive semidefinite matrices have trace norm equal to the real trace. -/
```
This is a Lean docstring. It is a human-written comment that tells readers what the declaration is meant to express before the formal code begins.

2. Code:
```lean
private theorem traceNormOp_posSemidef_eq_trace
```
This line starts the `traceNormOp_posSemidef_eq_trace` declaration. Because it begins with `theorem`, Lean now knows what kind of named object is being introduced.

3. Code:
```lean
    {d : Type u} [Fintype d] [DecidableEq d]
```
This line is one local step in the declaration. It either refines the formula being defined or advances the proof by a small algebraic or logical move.  A bracket such as `[Fintype d]` tells Lean that the index set `d` is finite, so sums over all indices make sense.  A bracket such as `[DecidableEq d]` tells Lean that it can decide whether two indices are equal.

4. Code:
```lean
    {A : Matrix d d ℂ} (hA : A.PosSemidef) :
```
This line is one local step in the declaration. It either refines the formula being defined or advances the proof by a small algebraic or logical move.  `Matrix d d ℂ` means a square matrix with complex entries; the index type `d` tells Lean which rows and columns exist.  `PosSemidef` is Lean’s name for “positive semidefinite”.

5. Code:
```lean
    traceNormOp A = Complex.re (Matrix.trace A) := by
```
This line says that a proof script begins here. Everything indented underneath is a sequence of instructions that Lean will check step by step.

6. Code:
```lean
  calc
```
This line begins a chained calculation. Each displayed step that follows must be justified by the indented proof after `:= by`.

7. Code:
```lean
    traceNormOp A = ∑ i, |hA.isHermitian.eigenvalues i| := by
```
This line says that a proof script begins here. Everything indented underneath is a sequence of instructions that Lean will check step by step.

8. Code:
```lean
      simpa using traceNormOp_hermitian_eq_sum_abs_eigenvalues hA.isHermitian
```
This line simplifies the goal using definitions and known equalities. `simpa` means that, after simplification, the desired statement matches a theorem Lean already has.

9. Code:
```lean
    _ = ∑ i, hA.isHermitian.eigenvalues i := by
```
This line says that a proof script begins here. Everything indented underneath is a sequence of instructions that Lean will check step by step.

10. Code:
```lean
      refine Finset.sum_congr rfl ?_
```
This line is a more controlled version of `apply`. It sets up the proof with a partly specified argument and leaves smaller goals to solve next.

11. Code:
```lean
      intro i hi
```
This line introduces the variable or hypothesis named here into the proof context. In ordinary mathematical prose, it is the same as saying “let” or “assume”.

12. Code:
```lean
      exact abs_of_nonneg (hA.eigenvalues_nonneg i)
```
This line finishes the current goal by giving Lean the exact theorem, lemma, or term that proves it.

13. Code:
```lean
    _ = Complex.re (Matrix.trace A) := by
```
This line says that a proof script begins here. Everything indented underneath is a sequence of instructions that Lean will check step by step.

14. Code:
```lean
      rw [hA.isHermitian.trace_eq_sum_eigenvalues]
```
This line uses rewriting. Lean replaces one expression by an equal expression using the lemmas listed in brackets.

15. Code:
```lean
      simp
```
This line simplifies the goal using definitions and known equalities. `simpa` means that, after simplification, the desired statement matches a theorem Lean already has.

## Mathematical summary

Restated without Lean syntax, `traceNormOp_posSemidef_eq_trace` is the theorem or lemma written above.

- State the desired identity or inequality in Lean’s syntax.
- Introduce temporary names and intermediate claims that organize the argument.
- Use rewriting, simplification, and earlier lemmas to reduce the goal to standard matrix or norm manipulations.
- Close the remaining algebraic or order-theoretic steps with Lean’s proof tactics.

## Dependencies and downstream use

### Earlier declarations this depends on
- [`traceNormOp`](../../Setups/traceNormOp.md) from `Setups.lean`
- [`traceNormOp_hermitian_eq_sum_abs_eigenvalues`](traceNormOp_hermitian_eq_sum_abs_eigenvalues.md) from `Theorem/Lemma1.lean`

### Later declarations that use this one
- [`traceNormOp_density_eq_one`](traceNormOp_density_eq_one.md) in `Theorem/Lemma1.lean`

## Backlinks

- [Back to `INDEX.md`](../../INDEX.md)
- [Back to the `Theorem/Lemma1.lean` section in the index](../../INDEX.md#diamond-theorem-lemma1-lean)
- [Previous declaration in this file](lemma1.md)
- [Next declaration in this file](traceNormOp_density_eq_one.md)