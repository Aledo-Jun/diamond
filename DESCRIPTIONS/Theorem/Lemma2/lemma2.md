# lemma2

## Source location

- Original Lean file: `Diamond/Theorem/Lemma2.lean`
- Declaration name: `lemma2`
- Declaration kind: `theorem`

## Why this declaration exists

Lemma 2: `‖Y‖₁ ≤ √N ‖Y‖₂` on an `N`-dimensional space.

 In the file `Theorem/Lemma2.lean`, it contributes to the Hilbert--Schmidt versus trace norm bound `lemma2`. Later proofs call this result by name, so documenting it makes the larger argument readable as a mathematical chain rather than as opaque proof script.

## Original code

```lean
/-- Lemma 2: `‖Y‖₁ ≤ √N ‖Y‖₂` on an `N`-dimensional space. -/
theorem lemma2
    {ι : Type u} [Fintype ι] [DecidableEq ι]
    (Y : Matrix ι ι ℂ) :
    traceNormOp Y ≤ Real.sqrt (Fintype.card ι : ℝ) * hsNormOp Y := by
  let μ : ι → ℝ := (Matrix.isHermitian_conjTranspose_mul_self Y).eigenvalues
  have hμ_nonneg : ∀ i, 0 ≤ μ i := by
    intro i
    exact Matrix.eigenvalues_conjTranspose_mul_self_nonneg Y i
  have hsum_sq :
      (∑ i, Real.sqrt (μ i)) ^ 2 ≤ (Fintype.card ι : ℝ) * ∑ i, μ i := by
    calc
      (∑ i, Real.sqrt (μ i)) ^ 2 ≤
          (Fintype.card ι : ℝ) * ∑ i, (Real.sqrt (μ i)) ^ 2 := by
            simpa using
              sq_sum_le_card_mul_sum_sq
                (s := (Finset.univ : Finset ι))
                (f := fun i => Real.sqrt (μ i))
      _ = (Fintype.card ι : ℝ) * ∑ i, μ i := by
            refine congrArg ((Fintype.card ι : ℝ) * ·) ?_
            refine Finset.sum_congr rfl ?_
            intro i hi
            exact Real.sq_sqrt (hμ_nonneg i)
  have hnorm_sq : hsNormOp Y ^ 2 = ∑ i, μ i := by
    calc
      hsNormOp Y ^ 2 = Complex.re (Matrix.trace (Yᴴ * Y)) := by
        exact hsNorm_sq_eq_re_trace_conjTranspose_mul_self Y
      _ = ∑ i, μ i := by
        rw [(Matrix.isHermitian_conjTranspose_mul_self Y).trace_eq_sum_eigenvalues]
        simp [μ]
  have hrhs_sq :
      (Real.sqrt (Fintype.card ι : ℝ) * hsNormOp Y) ^ 2 =
        (Fintype.card ι : ℝ) * ∑ i, μ i := by
    calc
      (Real.sqrt (Fintype.card ι : ℝ) * hsNormOp Y) ^ 2
        = (Real.sqrt (Fintype.card ι : ℝ)) ^ 2 * (hsNormOp Y) ^ 2 := by
            ring
      _ = (Fintype.card ι : ℝ) * ∑ i, μ i := by
            rw [Real.sq_sqrt (by positivity), hnorm_sq]
  have hsqineq :
      (∑ i, Real.sqrt (μ i)) ^ 2 ≤ (Real.sqrt (Fintype.card ι : ℝ) * hsNormOp Y) ^ 2 := by
    rw [hrhs_sq]
    exact hsum_sq
  have hleft : 0 ≤ ∑ i, Real.sqrt (μ i) := by
    exact Finset.sum_nonneg (fun i _ => Real.sqrt_nonneg _)
  have hright : 0 ≤ Real.sqrt (Fintype.card ι : ℝ) * hsNormOp Y := by
    exact mul_nonneg (Real.sqrt_nonneg _) (norm_nonneg _)
  have hle_abs : ∑ i, Real.sqrt (μ i) ≤ |Real.sqrt (Fintype.card ι : ℝ) * hsNormOp Y| := by
    simpa [abs_of_nonneg hleft] using (sq_le_sq.mp hsqineq)
  calc
    traceNormOp Y = ∑ i, Real.sqrt (μ i) := by
      rfl
    _ ≤ |Real.sqrt (Fintype.card ι : ℝ) * hsNormOp Y| := hle_abs
    _ = Real.sqrt (Fintype.card ι : ℝ) * hsNormOp Y := abs_of_nonneg hright
```

## Line-by-line explanation

The explanation below follows the declaration one physical line at a time. For long proofs, some lines are tiny bookkeeping steps; those are still explained, but briefly.

1. Code:
```lean
/-- Lemma 2: `‖Y‖₁ ≤ √N ‖Y‖₂` on an `N`-dimensional space. -/
```
This is a Lean docstring. It is a human-written comment that tells readers what the declaration is meant to express before the formal code begins.

2. Code:
```lean
theorem lemma2
```
This line starts the `lemma2` declaration. Because it begins with `theorem`, Lean now knows what kind of named object is being introduced.

3. Code:
```lean
    {ι : Type u} [Fintype ι] [DecidableEq ι]
```
This line is one local step in the declaration. It either refines the formula being defined or advances the proof by a small algebraic or logical move.  A bracket such as `[Fintype d]` tells Lean that the index set `d` is finite, so sums over all indices make sense.  A bracket such as `[DecidableEq d]` tells Lean that it can decide whether two indices are equal.

4. Code:
```lean
    (Y : Matrix ι ι ℂ) :
```
This line is one local step in the declaration. It either refines the formula being defined or advances the proof by a small algebraic or logical move.  `Matrix d d ℂ` means a square matrix with complex entries; the index type `d` tells Lean which rows and columns exist.

5. Code:
```lean
    traceNormOp Y ≤ Real.sqrt (Fintype.card ι : ℝ) * hsNormOp Y := by
```
This line says that a proof script begins here. Everything indented underneath is a sequence of instructions that Lean will check step by step.  `Fintype.card` is the size of a finite index set.

6. Code:
```lean
  let μ : ι → ℝ := (Matrix.isHermitian_conjTranspose_mul_self Y).eigenvalues
```
This line gives a temporary name to an expression. Doing that makes later lines shorter and easier to read.

7. Code:
```lean
  have hμ_nonneg : ∀ i, 0 ≤ μ i := by
```
This line says that a proof script begins here. Everything indented underneath is a sequence of instructions that Lean will check step by step.

8. Code:
```lean
    intro i
```
This line introduces the variable or hypothesis named here into the proof context. In ordinary mathematical prose, it is the same as saying “let” or “assume”.

9. Code:
```lean
    exact Matrix.eigenvalues_conjTranspose_mul_self_nonneg Y i
```
This line finishes the current goal by giving Lean the exact theorem, lemma, or term that proves it.

10. Code:
```lean
  have hsum_sq :
```
This line introduces an intermediate claim. The proof pauses to establish a fact that will be used shortly afterwards.

11. Code:
```lean
      (∑ i, Real.sqrt (μ i)) ^ 2 ≤ (Fintype.card ι : ℝ) * ∑ i, μ i := by
```
This line says that a proof script begins here. Everything indented underneath is a sequence of instructions that Lean will check step by step.  `Fintype.card` is the size of a finite index set.

12. Code:
```lean
    calc
```
This line begins a chained calculation. Each displayed step that follows must be justified by the indented proof after `:= by`.

13. Code:
```lean
      (∑ i, Real.sqrt (μ i)) ^ 2 ≤
```
This line is one local step in the declaration. It either refines the formula being defined or advances the proof by a small algebraic or logical move.

14. Code:
```lean
          (Fintype.card ι : ℝ) * ∑ i, (Real.sqrt (μ i)) ^ 2 := by
```
This line says that a proof script begins here. Everything indented underneath is a sequence of instructions that Lean will check step by step.  `Fintype.card` is the size of a finite index set.

15. Code:
```lean
            simpa using
```
This line simplifies the goal using definitions and known equalities. `simpa` means that, after simplification, the desired statement matches a theorem Lean already has.

16. Code:
```lean
              sq_sum_le_card_mul_sum_sq
```
This line is one local step in the declaration. It either refines the formula being defined or advances the proof by a small algebraic or logical move.

17. Code:
```lean
                (s := (Finset.univ : Finset ι))
```
This line is one local step in the declaration. It either refines the formula being defined or advances the proof by a small algebraic or logical move.

18. Code:
```lean
                (f := fun i => Real.sqrt (μ i))
```
This line is one local step in the declaration. It either refines the formula being defined or advances the proof by a small algebraic or logical move.

19. Code:
```lean
      _ = (Fintype.card ι : ℝ) * ∑ i, μ i := by
```
This line says that a proof script begins here. Everything indented underneath is a sequence of instructions that Lean will check step by step.  `Fintype.card` is the size of a finite index set.

20. Code:
```lean
            refine congrArg ((Fintype.card ι : ℝ) * ·) ?_
```
This line is a more controlled version of `apply`. It sets up the proof with a partly specified argument and leaves smaller goals to solve next.  `Fintype.card` is the size of a finite index set.

21. Code:
```lean
            refine Finset.sum_congr rfl ?_
```
This line is a more controlled version of `apply`. It sets up the proof with a partly specified argument and leaves smaller goals to solve next.

22. Code:
```lean
            intro i hi
```
This line introduces the variable or hypothesis named here into the proof context. In ordinary mathematical prose, it is the same as saying “let” or “assume”.

23. Code:
```lean
            exact Real.sq_sqrt (hμ_nonneg i)
```
This line finishes the current goal by giving Lean the exact theorem, lemma, or term that proves it.

24. Code:
```lean
  have hnorm_sq : hsNormOp Y ^ 2 = ∑ i, μ i := by
```
This line says that a proof script begins here. Everything indented underneath is a sequence of instructions that Lean will check step by step.

25. Code:
```lean
    calc
```
This line begins a chained calculation. Each displayed step that follows must be justified by the indented proof after `:= by`.

26. Code:
```lean
      hsNormOp Y ^ 2 = Complex.re (Matrix.trace (Yᴴ * Y)) := by
```
This line says that a proof script begins here. Everything indented underneath is a sequence of instructions that Lean will check step by step.  The superscript `ᴴ` means conjugate transpose (also called the adjoint).

27. Code:
```lean
        exact hsNorm_sq_eq_re_trace_conjTranspose_mul_self Y
```
This line finishes the current goal by giving Lean the exact theorem, lemma, or term that proves it.

28. Code:
```lean
      _ = ∑ i, μ i := by
```
This line says that a proof script begins here. Everything indented underneath is a sequence of instructions that Lean will check step by step.

29. Code:
```lean
        rw [(Matrix.isHermitian_conjTranspose_mul_self Y).trace_eq_sum_eigenvalues]
```
This line uses rewriting. Lean replaces one expression by an equal expression using the lemmas listed in brackets.

30. Code:
```lean
        simp [μ]
```
This line simplifies the goal using definitions and known equalities. `simpa` means that, after simplification, the desired statement matches a theorem Lean already has.

31. Code:
```lean
  have hrhs_sq :
```
This line introduces an intermediate claim. The proof pauses to establish a fact that will be used shortly afterwards.

32. Code:
```lean
      (Real.sqrt (Fintype.card ι : ℝ) * hsNormOp Y) ^ 2 =
```
This line is one local step in the declaration. It either refines the formula being defined or advances the proof by a small algebraic or logical move.  `Fintype.card` is the size of a finite index set.

33. Code:
```lean
        (Fintype.card ι : ℝ) * ∑ i, μ i := by
```
This line says that a proof script begins here. Everything indented underneath is a sequence of instructions that Lean will check step by step.  `Fintype.card` is the size of a finite index set.

34. Code:
```lean
    calc
```
This line begins a chained calculation. Each displayed step that follows must be justified by the indented proof after `:= by`.

35. Code:
```lean
      (Real.sqrt (Fintype.card ι : ℝ) * hsNormOp Y) ^ 2
```
This line is one local step in the declaration. It either refines the formula being defined or advances the proof by a small algebraic or logical move.  `Fintype.card` is the size of a finite index set.

36. Code:
```lean
        = (Real.sqrt (Fintype.card ι : ℝ)) ^ 2 * (hsNormOp Y) ^ 2 := by
```
This line says that a proof script begins here. Everything indented underneath is a sequence of instructions that Lean will check step by step.  `Fintype.card` is the size of a finite index set.

37. Code:
```lean
            ring
```
This line normalizes an algebraic identity in a commutative ring, just as one would expand and collect like terms by hand.

38. Code:
```lean
      _ = (Fintype.card ι : ℝ) * ∑ i, μ i := by
```
This line says that a proof script begins here. Everything indented underneath is a sequence of instructions that Lean will check step by step.  `Fintype.card` is the size of a finite index set.

39. Code:
```lean
            rw [Real.sq_sqrt (by positivity), hnorm_sq]
```
This line uses rewriting. Lean replaces one expression by an equal expression using the lemmas listed in brackets.

40. Code:
```lean
  have hsqineq :
```
This line introduces an intermediate claim. The proof pauses to establish a fact that will be used shortly afterwards.

41. Code:
```lean
      (∑ i, Real.sqrt (μ i)) ^ 2 ≤ (Real.sqrt (Fintype.card ι : ℝ) * hsNormOp Y) ^ 2 := by
```
This line says that a proof script begins here. Everything indented underneath is a sequence of instructions that Lean will check step by step.  `Fintype.card` is the size of a finite index set.

42. Code:
```lean
    rw [hrhs_sq]
```
This line uses rewriting. Lean replaces one expression by an equal expression using the lemmas listed in brackets.

43. Code:
```lean
    exact hsum_sq
```
This line finishes the current goal by giving Lean the exact theorem, lemma, or term that proves it.

44. Code:
```lean
  have hleft : 0 ≤ ∑ i, Real.sqrt (μ i) := by
```
This line says that a proof script begins here. Everything indented underneath is a sequence of instructions that Lean will check step by step.

45. Code:
```lean
    exact Finset.sum_nonneg (fun i _ => Real.sqrt_nonneg _)
```
This line finishes the current goal by giving Lean the exact theorem, lemma, or term that proves it.

46. Code:
```lean
  have hright : 0 ≤ Real.sqrt (Fintype.card ι : ℝ) * hsNormOp Y := by
```
This line says that a proof script begins here. Everything indented underneath is a sequence of instructions that Lean will check step by step.  `Fintype.card` is the size of a finite index set.

47. Code:
```lean
    exact mul_nonneg (Real.sqrt_nonneg _) (norm_nonneg _)
```
This line finishes the current goal by giving Lean the exact theorem, lemma, or term that proves it.

48. Code:
```lean
  have hle_abs : ∑ i, Real.sqrt (μ i) ≤ |Real.sqrt (Fintype.card ι : ℝ) * hsNormOp Y| := by
```
This line says that a proof script begins here. Everything indented underneath is a sequence of instructions that Lean will check step by step.  `Fintype.card` is the size of a finite index set.

49. Code:
```lean
    simpa [abs_of_nonneg hleft] using (sq_le_sq.mp hsqineq)
```
This line simplifies the goal using definitions and known equalities. `simpa` means that, after simplification, the desired statement matches a theorem Lean already has.

50. Code:
```lean
  calc
```
This line begins a chained calculation. Each displayed step that follows must be justified by the indented proof after `:= by`.

51. Code:
```lean
    traceNormOp Y = ∑ i, Real.sqrt (μ i) := by
```
This line says that a proof script begins here. Everything indented underneath is a sequence of instructions that Lean will check step by step.

52. Code:
```lean
      rfl
```
This line closes the goal by reflexivity: after unfolding definitions, both sides are literally the same expression.

53. Code:
```lean
    _ ≤ |Real.sqrt (Fintype.card ι : ℝ) * hsNormOp Y| := hle_abs
```
This line is one step inside a `calc` block. Lean is checking that the new expression really follows from the previous one.  `Fintype.card` is the size of a finite index set.

54. Code:
```lean
    _ = Real.sqrt (Fintype.card ι : ℝ) * hsNormOp Y := abs_of_nonneg hright
```
This line is one step inside a `calc` block. Lean is checking that the new expression really follows from the previous one.  `Fintype.card` is the size of a finite index set.

## Mathematical summary

Restated without Lean syntax, `lemma2` is the theorem or lemma written above.

- State the desired identity or inequality in Lean’s syntax.
- Introduce temporary names and intermediate claims that organize the argument.
- Use rewriting, simplification, and earlier lemmas to reduce the goal to standard matrix or norm manipulations.
- Close the remaining algebraic or order-theoretic steps with Lean’s proof tactics.

## Dependencies and downstream use

### Earlier declarations this depends on
- [`traceNormOp`](../../Setups/traceNormOp.md) from `Setups.lean`
- [`hsNormOp`](../../Setups/hsNormOp.md) from `Setups.lean`
- [`hsNorm_sq_eq_re_trace_conjTranspose_mul_self`](../Lemma1/hsNorm_sq_eq_re_trace_conjTranspose_mul_self.md) from `Theorem/Lemma1.lean`
- [`hsNorm_sq_eq_re_trace_conjTranspose_mul_self`](hsNorm_sq_eq_re_trace_conjTranspose_mul_self.md) from `Theorem/Lemma2.lean`

### Later declarations that use this one
- [`theorem1`](../Theorem1/theorem1.md) in `Theorem/Theorem1.lean`
- [`remark1`](../Remark1/remark1.md) in `Theorem/Remark1.lean`
- [`theorem_not_tight`](../../PositiveGap/NotTight/theorem_not_tight.md) in `PositiveGap/NotTight.lean`

## Backlinks

- [Back to `INDEX.md`](../../INDEX.md)
- [Back to the `Theorem/Lemma2.lean` section in the index](../../INDEX.md#diamond-theorem-lemma2-lean)
- [Previous declaration in this file](hsNorm_sq_eq_re_trace_conjTranspose_mul_self.md)