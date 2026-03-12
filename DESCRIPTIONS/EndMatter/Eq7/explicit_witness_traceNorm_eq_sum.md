# explicit_witness_traceNorm_eq_sum

## Source location

- Original Lean file: `Diamond/EndMatter/Eq7.lean`
- Declaration name: `explicit_witness_traceNorm_eq_sum`
- Declaration kind: `theorem`

## Why this declaration exists

The witness trace norm collapses to the one-dimensional phase sum.

 In the file `EndMatter/Eq7.lean`, it contributes to the explicit witness construction used to prove the lower bound labelled Eq. (7). Later proofs call this result by name, so documenting it makes the larger argument readable as a mathematical chain rather than as opaque proof script.

## Original code

```lean
/-- The witness trace norm collapses to the one-dimensional phase sum. -/
theorem explicit_witness_traceNorm_eq_sum (d : ℕ) [Fact (1 < d)] :
    traceNormOp
      ((d : ℂ)⁻¹ •
        (swapMatrix d - swapMatrix d * ((Ud d)ᵀ ⊗ₖ star (Ud d)))) =
      ∑ k : Fin d, ‖1 - Ud d k k‖ := by
  let f : Fin d × Fin d → ℂ := fun ab =>
    (d : ℂ)⁻¹ * (1 - Ud d ab.1 ab.1 * star (Ud d ab.2 ab.2))
  rw [explicit_witness_eq_swap_diagonal]
  rw [traceNormOp_mul_left_isometry (U := swapMatrix d) (X := Matrix.diagonal f)
    (hU := swapMatrix_conjTranspose_mul_self d)]
  rw [traceNormOp_diagonal]
  have hd_pos : 0 < d := lt_trans Nat.zero_lt_one ‹Fact (1 < d)›.out
  have hd_neR : (d : ℝ) ≠ 0 := by
    exact_mod_cast hd_pos.ne'
  have hscalar : ‖((d : ℂ)⁻¹)‖ = (d : ℝ)⁻¹ := by
    rw [norm_inv, Complex.norm_natCast]
  calc
    ∑ i, ‖f i‖
      = ∑ i : Fin d × Fin d, ‖((d : ℂ)⁻¹) * (1 - Ud d i.1 i.1 * star (Ud d i.2 i.2))‖ := by
          rfl
    _ = ∑ i : Fin d × Fin d, ‖((d : ℂ)⁻¹)‖ * ‖1 - Ud d i.1 i.1 * star (Ud d i.2 i.2)‖ := by
          refine Finset.sum_congr rfl ?_
          intro i hi
          rw [norm_mul]
    _ = ‖((d : ℂ)⁻¹)‖ * ∑ i : Fin d × Fin d, ‖1 - Ud d i.1 i.1 * star (Ud d i.2 i.2)‖ := by
          rw [← Finset.mul_sum]
    _ = (d : ℝ)⁻¹ * ∑ i : Fin d × Fin d, ‖1 - Ud d i.1 i.1 * star (Ud d i.2 i.2)‖ := by
          rw [hscalar]
    _ = (d : ℝ)⁻¹ * ((d : ℝ) * ∑ k : Fin d, ‖1 - Ud d k k‖) := by
          congr 1
          calc
            ∑ i : Fin d × Fin d, ‖1 - Ud d i.1 i.1 * star (Ud d i.2 i.2)‖
              = ∑ a : Fin d, ∑ b : Fin d, ‖1 - Ud d a a * star (Ud d b b)‖ := by
                  simp [Fintype.sum_prod_type]
            _ = ∑ b : Fin d, ∑ a : Fin d, ‖1 - Ud d a a * star (Ud d b b)‖ := by
                  simpa using
                    (Finset.sum_comm
                      (s := (Finset.univ : Finset (Fin d)))
                      (t := (Finset.univ : Finset (Fin d)))
                      (f := fun a b => ‖1 - Ud d a a * star (Ud d b b)‖))
            _ = ∑ b : Fin d, ∑ a : Fin d, ‖1 - Ud d a a‖ := by
                  refine Finset.sum_congr rfl ?_
                  intro b hb
                  have hinner :
                      ∑ k : Fin d, ‖1 - Ud d k k * star (Ud d b b)‖ =
                        ∑ a : Fin d, ‖1 - Ud d a a‖ := by
                    exact (Fintype.sum_bijective (fun a => a + b)
                      (AddGroup.addRight_bijective b)
                      (fun a => ‖1 - Ud d a a‖)
                      (fun k => ‖1 - Ud d k k * star (Ud d b b)‖)
                      (fun a => by
                        change ‖1 - Ud d a a‖ =
                          ‖1 - Ud d (a + b) (a + b) * star (Ud d b b)‖
                        rw [ud_add_mul_star_eq])).symm
                  exact hinner
            _ = (d : ℝ) * ∑ a : Fin d, ‖1 - Ud d a a‖ := by
                  rw [Fin.sum_const, nsmul_eq_mul]
    _ = ∑ k : Fin d, ‖1 - Ud d k k‖ := by
          rw [← mul_assoc, inv_mul_cancel₀ hd_neR, one_mul]
```

## Line-by-line explanation

The explanation below follows the declaration one physical line at a time. For long proofs, some lines are tiny bookkeeping steps; those are still explained, but briefly.

1. Code:
```lean
/-- The witness trace norm collapses to the one-dimensional phase sum. -/
```
This is a Lean docstring. It is a human-written comment that tells readers what the declaration is meant to express before the formal code begins.

2. Code:
```lean
theorem explicit_witness_traceNorm_eq_sum (d : ℕ) [Fact (1 < d)] :
```
This line starts the `explicit_witness_traceNorm_eq_sum` declaration. Because it begins with `theorem`, Lean now knows what kind of named object is being introduced.

3. Code:
```lean
    traceNormOp
```
This line is one local step in the declaration. It either refines the formula being defined or advances the proof by a small algebraic or logical move.

4. Code:
```lean
      ((d : ℂ)⁻¹ •
```
This line is one local step in the declaration. It either refines the formula being defined or advances the proof by a small algebraic or logical move.

5. Code:
```lean
        (swapMatrix d - swapMatrix d * ((Ud d)ᵀ ⊗ₖ star (Ud d)))) =
```
This line is one local step in the declaration. It either refines the formula being defined or advances the proof by a small algebraic or logical move.  `Matrix d d ℂ` means a square matrix with complex entries; the index type `d` tells Lean which rows and columns exist.  The symbol `⊗ₖ` is the Kronecker (tensor) product of matrices.  The superscript `ᵀ` means ordinary transpose.

6. Code:
```lean
      ∑ k : Fin d, ‖1 - Ud d k k‖ := by
```
This line says that a proof script begins here. Everything indented underneath is a sequence of instructions that Lean will check step by step.

7. Code:
```lean
  let f : Fin d × Fin d → ℂ := fun ab =>
```
This line gives a temporary name to an expression. Doing that makes later lines shorter and easier to read.

8. Code:
```lean
    (d : ℂ)⁻¹ * (1 - Ud d ab.1 ab.1 * star (Ud d ab.2 ab.2))
```
This line is one local step in the declaration. It either refines the formula being defined or advances the proof by a small algebraic or logical move.

9. Code:
```lean
  rw [explicit_witness_eq_swap_diagonal]
```
This line uses rewriting. Lean replaces one expression by an equal expression using the lemmas listed in brackets.

10. Code:
```lean
  rw [traceNormOp_mul_left_isometry (U := swapMatrix d) (X := Matrix.diagonal f)
```
This line uses rewriting. Lean replaces one expression by an equal expression using the lemmas listed in brackets.  `Matrix d d ℂ` means a square matrix with complex entries; the index type `d` tells Lean which rows and columns exist.

11. Code:
```lean
    (hU := swapMatrix_conjTranspose_mul_self d)]
```
This line is one local step in the declaration. It either refines the formula being defined or advances the proof by a small algebraic or logical move.

12. Code:
```lean
  rw [traceNormOp_diagonal]
```
This line uses rewriting. Lean replaces one expression by an equal expression using the lemmas listed in brackets.

13. Code:
```lean
  have hd_pos : 0 < d := lt_trans Nat.zero_lt_one ‹Fact (1 < d)›.out
```
This line introduces an intermediate claim. The proof pauses to establish a fact that will be used shortly afterwards.

14. Code:
```lean
  have hd_neR : (d : ℝ) ≠ 0 := by
```
This line says that a proof script begins here. Everything indented underneath is a sequence of instructions that Lean will check step by step.

15. Code:
```lean
    exact_mod_cast hd_pos.ne'
```
This line finishes the current goal by giving Lean the exact theorem, lemma, or term that proves it.

16. Code:
```lean
  have hscalar : ‖((d : ℂ)⁻¹)‖ = (d : ℝ)⁻¹ := by
```
This line says that a proof script begins here. Everything indented underneath is a sequence of instructions that Lean will check step by step.

17. Code:
```lean
    rw [norm_inv, Complex.norm_natCast]
```
This line uses rewriting. Lean replaces one expression by an equal expression using the lemmas listed in brackets.

18. Code:
```lean
  calc
```
This line begins a chained calculation. Each displayed step that follows must be justified by the indented proof after `:= by`.

19. Code:
```lean
    ∑ i, ‖f i‖
```
This line is one local step in the declaration. It either refines the formula being defined or advances the proof by a small algebraic or logical move.

20. Code:
```lean
      = ∑ i : Fin d × Fin d, ‖((d : ℂ)⁻¹) * (1 - Ud d i.1 i.1 * star (Ud d i.2 i.2))‖ := by
```
This line says that a proof script begins here. Everything indented underneath is a sequence of instructions that Lean will check step by step.

21. Code:
```lean
          rfl
```
This line closes the goal by reflexivity: after unfolding definitions, both sides are literally the same expression.

22. Code:
```lean
    _ = ∑ i : Fin d × Fin d, ‖((d : ℂ)⁻¹)‖ * ‖1 - Ud d i.1 i.1 * star (Ud d i.2 i.2)‖ := by
```
This line says that a proof script begins here. Everything indented underneath is a sequence of instructions that Lean will check step by step.

23. Code:
```lean
          refine Finset.sum_congr rfl ?_
```
This line is a more controlled version of `apply`. It sets up the proof with a partly specified argument and leaves smaller goals to solve next.

24. Code:
```lean
          intro i hi
```
This line introduces the variable or hypothesis named here into the proof context. In ordinary mathematical prose, it is the same as saying “let” or “assume”.

25. Code:
```lean
          rw [norm_mul]
```
This line uses rewriting. Lean replaces one expression by an equal expression using the lemmas listed in brackets.

26. Code:
```lean
    _ = ‖((d : ℂ)⁻¹)‖ * ∑ i : Fin d × Fin d, ‖1 - Ud d i.1 i.1 * star (Ud d i.2 i.2)‖ := by
```
This line says that a proof script begins here. Everything indented underneath is a sequence of instructions that Lean will check step by step.

27. Code:
```lean
          rw [← Finset.mul_sum]
```
This line uses rewriting. Lean replaces one expression by an equal expression using the lemmas listed in brackets.

28. Code:
```lean
    _ = (d : ℝ)⁻¹ * ∑ i : Fin d × Fin d, ‖1 - Ud d i.1 i.1 * star (Ud d i.2 i.2)‖ := by
```
This line says that a proof script begins here. Everything indented underneath is a sequence of instructions that Lean will check step by step.

29. Code:
```lean
          rw [hscalar]
```
This line uses rewriting. Lean replaces one expression by an equal expression using the lemmas listed in brackets.

30. Code:
```lean
    _ = (d : ℝ)⁻¹ * ((d : ℝ) * ∑ k : Fin d, ‖1 - Ud d k k‖) := by
```
This line says that a proof script begins here. Everything indented underneath is a sequence of instructions that Lean will check step by step.

31. Code:
```lean
          congr 1
```
This line is one local step in the declaration. It either refines the formula being defined or advances the proof by a small algebraic or logical move.

32. Code:
```lean
          calc
```
This line begins a chained calculation. Each displayed step that follows must be justified by the indented proof after `:= by`.

33. Code:
```lean
            ∑ i : Fin d × Fin d, ‖1 - Ud d i.1 i.1 * star (Ud d i.2 i.2)‖
```
This line is one local step in the declaration. It either refines the formula being defined or advances the proof by a small algebraic or logical move.

34. Code:
```lean
              = ∑ a : Fin d, ∑ b : Fin d, ‖1 - Ud d a a * star (Ud d b b)‖ := by
```
This line says that a proof script begins here. Everything indented underneath is a sequence of instructions that Lean will check step by step.

35. Code:
```lean
                  simp [Fintype.sum_prod_type]
```
This line simplifies the goal using definitions and known equalities. `simpa` means that, after simplification, the desired statement matches a theorem Lean already has.  A bracket such as `[Fintype d]` tells Lean that the index set `d` is finite, so sums over all indices make sense.

36. Code:
```lean
            _ = ∑ b : Fin d, ∑ a : Fin d, ‖1 - Ud d a a * star (Ud d b b)‖ := by
```
This line says that a proof script begins here. Everything indented underneath is a sequence of instructions that Lean will check step by step.

37. Code:
```lean
                  simpa using
```
This line simplifies the goal using definitions and known equalities. `simpa` means that, after simplification, the desired statement matches a theorem Lean already has.

38. Code:
```lean
                    (Finset.sum_comm
```
This line is one local step in the declaration. It either refines the formula being defined or advances the proof by a small algebraic or logical move.

39. Code:
```lean
                      (s := (Finset.univ : Finset (Fin d)))
```
This line is one local step in the declaration. It either refines the formula being defined or advances the proof by a small algebraic or logical move.

40. Code:
```lean
                      (t := (Finset.univ : Finset (Fin d)))
```
This line is one local step in the declaration. It either refines the formula being defined or advances the proof by a small algebraic or logical move.

41. Code:
```lean
                      (f := fun a b => ‖1 - Ud d a a * star (Ud d b b)‖))
```
This line is one local step in the declaration. It either refines the formula being defined or advances the proof by a small algebraic or logical move.

42. Code:
```lean
            _ = ∑ b : Fin d, ∑ a : Fin d, ‖1 - Ud d a a‖ := by
```
This line says that a proof script begins here. Everything indented underneath is a sequence of instructions that Lean will check step by step.

43. Code:
```lean
                  refine Finset.sum_congr rfl ?_
```
This line is a more controlled version of `apply`. It sets up the proof with a partly specified argument and leaves smaller goals to solve next.

44. Code:
```lean
                  intro b hb
```
This line introduces the variable or hypothesis named here into the proof context. In ordinary mathematical prose, it is the same as saying “let” or “assume”.

45. Code:
```lean
                  have hinner :
```
This line introduces an intermediate claim. The proof pauses to establish a fact that will be used shortly afterwards.

46. Code:
```lean
                      ∑ k : Fin d, ‖1 - Ud d k k * star (Ud d b b)‖ =
```
This line is one local step in the declaration. It either refines the formula being defined or advances the proof by a small algebraic or logical move.

47. Code:
```lean
                        ∑ a : Fin d, ‖1 - Ud d a a‖ := by
```
This line says that a proof script begins here. Everything indented underneath is a sequence of instructions that Lean will check step by step.

48. Code:
```lean
                    exact (Fintype.sum_bijective (fun a => a + b)
```
This line finishes the current goal by giving Lean the exact theorem, lemma, or term that proves it.

49. Code:
```lean
                      (AddGroup.addRight_bijective b)
```
This line is one local step in the declaration. It either refines the formula being defined or advances the proof by a small algebraic or logical move.

50. Code:
```lean
                      (fun a => ‖1 - Ud d a a‖)
```
This line is one local step in the declaration. It either refines the formula being defined or advances the proof by a small algebraic or logical move.

51. Code:
```lean
                      (fun k => ‖1 - Ud d k k * star (Ud d b b)‖)
```
This line is one local step in the declaration. It either refines the formula being defined or advances the proof by a small algebraic or logical move.

52. Code:
```lean
                      (fun a => by
```
This line is one local step in the declaration. It either refines the formula being defined or advances the proof by a small algebraic or logical move.

53. Code:
```lean
                        change ‖1 - Ud d a a‖ =
```
This line replaces the current goal by a definitionally equal goal that is easier to manipulate.

54. Code:
```lean
                          ‖1 - Ud d (a + b) (a + b) * star (Ud d b b)‖
```
This line is one local step in the declaration. It either refines the formula being defined or advances the proof by a small algebraic or logical move.

55. Code:
```lean
                        rw [ud_add_mul_star_eq])).symm
```
This line uses rewriting. Lean replaces one expression by an equal expression using the lemmas listed in brackets.

56. Code:
```lean
                  exact hinner
```
This line finishes the current goal by giving Lean the exact theorem, lemma, or term that proves it.

57. Code:
```lean
            _ = (d : ℝ) * ∑ a : Fin d, ‖1 - Ud d a a‖ := by
```
This line says that a proof script begins here. Everything indented underneath is a sequence of instructions that Lean will check step by step.

58. Code:
```lean
                  rw [Fin.sum_const, nsmul_eq_mul]
```
This line uses rewriting. Lean replaces one expression by an equal expression using the lemmas listed in brackets.

59. Code:
```lean
    _ = ∑ k : Fin d, ‖1 - Ud d k k‖ := by
```
This line says that a proof script begins here. Everything indented underneath is a sequence of instructions that Lean will check step by step.

60. Code:
```lean
          rw [← mul_assoc, inv_mul_cancel₀ hd_neR, one_mul]
```
This line uses rewriting. Lean replaces one expression by an equal expression using the lemmas listed in brackets.

## Mathematical summary

Restated without Lean syntax, `explicit_witness_traceNorm_eq_sum` is the theorem or lemma written above.

- State the desired identity or inequality in Lean’s syntax.
- Introduce temporary names and intermediate claims that organize the argument.
- Use rewriting, simplification, and earlier lemmas to reduce the goal to standard matrix or norm manipulations.
- Close the remaining algebraic or order-theoretic steps with Lean’s proof tactics.

## Dependencies and downstream use

### Earlier declarations this depends on
- [`traceNormOp`](../../Setups/traceNormOp.md) from `Setups.lean`
- [`Ud`](../../Setups/Ud.md) from `Setups.lean`
- [`traceNormOp_mul_left_isometry`](../../Theorem/Lemma1/traceNormOp_mul_left_isometry.md) from `Theorem/Lemma1.lean`
- [`traceNormOp_diagonal`](../../Theorem/Lemma1/traceNormOp_diagonal.md) from `Theorem/Lemma1.lean`
- [`swapMatrix`](../../PositiveGap/Lemma6/swapMatrix.md) from `PositiveGap/Lemma6.lean`
- [`swapMatrix_conjTranspose_mul_self`](../../PositiveGap/Lemma6/swapMatrix_conjTranspose_mul_self.md) from `PositiveGap/Lemma6.lean`
- [`ud_add_mul_star_eq`](ud_add_mul_star_eq.md) from `EndMatter/Eq7.lean`
- [`explicit_witness_eq_swap_diagonal`](explicit_witness_eq_swap_diagonal.md) from `EndMatter/Eq7.lean`

### Later declarations that use this one
- [`explicit_witness_traceNorm_eq`](explicit_witness_traceNorm_eq.md) in `EndMatter/Eq7.lean`

## Backlinks

- [Back to `INDEX.md`](../../INDEX.md)
- [Back to the `EndMatter/Eq7.lean` section in the index](../../INDEX.md#diamond-endmatter-eq7-lean)
- [Previous declaration in this file](explicit_witness_eq_swap_diagonal.md)
- [Next declaration in this file](norm_one_sub_ud_eq_sin.md)