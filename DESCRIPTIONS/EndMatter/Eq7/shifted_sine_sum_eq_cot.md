# shifted_sine_sum_eq_cot

## Source location

- Original Lean file: `Diamond/EndMatter/Eq7.lean`
- Declaration name: `shifted_sine_sum_eq_cot`
- Declaration kind: `theorem`

## Why this declaration exists

Telescoping evaluation of the shifted finite sine sum.

 In the file `EndMatter/Eq7.lean`, it contributes to the explicit witness construction used to prove the lower bound labelled Eq. (7). Later proofs call this result by name, so documenting it makes the larger argument readable as a mathematical chain rather than as opaque proof script.

## Original code

```lean
/-- Telescoping evaluation of the shifted finite sine sum. -/
theorem shifted_sine_sum_eq_cot (d : ℕ) [Fact (1 < d)] :
    (∑ k ∈ Finset.range (d - 1), Real.sin (Real.pi * (k + 1) / d)) =
      Real.cot (Real.pi / (2 * d)) := by
  have hd_pos : 0 < d := lt_trans Nat.zero_lt_one ‹Fact (1 < d)›.out
  have hd_ne : (d : ℝ) ≠ 0 := by
    exact_mod_cast hd_pos.ne'
  let g : ℕ → ℝ := fun k => Real.cos (Real.pi * (2 * k + 1) / (2 * d))
  have htel :
      (2 * Real.sin (Real.pi / (2 * d))) *
        (∑ k ∈ Finset.range (d - 1), Real.sin (Real.pi * (k + 1) / d)) =
      ∑ k ∈ Finset.range (d - 1), (g k - g (k + 1)) := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl ?_
    intro k hk
    dsimp [g]
    have h := Real.two_mul_sin_mul_sin (Real.pi / (2 * d)) (Real.pi * (k + 1) / d)
    have harg1 :
        Real.pi / (2 * d) - Real.pi * (k + 1) / d =
          -(Real.pi * (2 * k + 1) / (2 * d)) := by
      field_simp [hd_ne]
      ring
    have harg2 :
        Real.pi / (2 * d) + Real.pi * (k + 1) / d =
          Real.pi * (2 * ↑(k + 1) + 1) / (2 * d) := by
      field_simp [hd_ne]
      norm_num [Nat.cast_add, Nat.cast_mul]
      ring
    calc
      2 * Real.sin (Real.pi / (2 * d)) * Real.sin (Real.pi * (k + 1) / d)
        = Real.cos (Real.pi / (2 * d) - Real.pi * (k + 1) / d) -
            Real.cos (Real.pi / (2 * d) + Real.pi * (k + 1) / d) := h
      _ = Real.cos (Real.pi * (2 * k + 1) / (2 * d)) -
            Real.cos (Real.pi * (2 * ↑(k + 1) + 1) / (2 * d)) := by
            rw [harg1, Real.cos_neg, harg2]
  have hsum :
      ∑ k ∈ Finset.range (d - 1), (g k - g (k + 1)) = g 0 - g (d - 1) := by
    simpa using (Finset.sum_range_sub' g (d - 1))
  have hend : g 0 - g (d - 1) = 2 * Real.cos (Real.pi / (2 * d)) := by
    dsimp [g]
    have h0 : Real.pi * (2 * (0 : ℕ) + 1) / (2 * d) = Real.pi / (2 * d) := by
      ring
    have hd_le : 1 ≤ d := Nat.succ_le_of_lt hd_pos
    have harg : Real.pi * (2 * ↑(d - 1) + 1) / (2 * d) = Real.pi - Real.pi / (2 * d) := by
      field_simp [hd_ne]
      norm_num [Nat.cast_sub hd_le, Nat.cast_mul, Nat.cast_add]
      ring
    rw [h0, harg, Real.cos_pi_sub]
    ring
  have hsin_pos : 0 < Real.sin (Real.pi / (2 * d)) := by
    apply Real.sin_pos_of_pos_of_lt_pi
    · positivity
    · have hd_gt_one : (1 : ℝ) < d := by
        exact_mod_cast ‹Fact (1 < d)›.out
      have htwo_d_gt_one : (1 : ℝ) < 2 * d := by
        nlinarith
      have hpos : (0 : ℝ) < 2 * d := by
        positivity
      rw [div_lt_iff₀ hpos]
      nlinarith [Real.pi_pos, htwo_d_gt_one]
  have hmain :
      (2 * Real.sin (Real.pi / (2 * d))) *
        (∑ k ∈ Finset.range (d - 1), Real.sin (Real.pi * (k + 1) / d)) =
      2 * Real.cos (Real.pi / (2 * d)) := by
    rw [htel, hsum, hend]
  rw [Real.cot_eq_cos_div_sin]
  apply (eq_div_iff hsin_pos.ne').2
  nlinarith [hmain]
```

## Line-by-line explanation

The explanation below follows the declaration one physical line at a time. For long proofs, some lines are tiny bookkeeping steps; those are still explained, but briefly.

1. Code:
```lean
/-- Telescoping evaluation of the shifted finite sine sum. -/
```
This is a Lean docstring. It is a human-written comment that tells readers what the declaration is meant to express before the formal code begins.

2. Code:
```lean
theorem shifted_sine_sum_eq_cot (d : ℕ) [Fact (1 < d)] :
```
This line starts the `shifted_sine_sum_eq_cot` declaration. Because it begins with `theorem`, Lean now knows what kind of named object is being introduced.

3. Code:
```lean
    (∑ k ∈ Finset.range (d - 1), Real.sin (Real.pi * (k + 1) / d)) =
```
This line is one local step in the declaration. It either refines the formula being defined or advances the proof by a small algebraic or logical move.

4. Code:
```lean
      Real.cot (Real.pi / (2 * d)) := by
```
This line says that a proof script begins here. Everything indented underneath is a sequence of instructions that Lean will check step by step.

5. Code:
```lean
  have hd_pos : 0 < d := lt_trans Nat.zero_lt_one ‹Fact (1 < d)›.out
```
This line introduces an intermediate claim. The proof pauses to establish a fact that will be used shortly afterwards.

6. Code:
```lean
  have hd_ne : (d : ℝ) ≠ 0 := by
```
This line says that a proof script begins here. Everything indented underneath is a sequence of instructions that Lean will check step by step.

7. Code:
```lean
    exact_mod_cast hd_pos.ne'
```
This line finishes the current goal by giving Lean the exact theorem, lemma, or term that proves it.

8. Code:
```lean
  let g : ℕ → ℝ := fun k => Real.cos (Real.pi * (2 * k + 1) / (2 * d))
```
This line gives a temporary name to an expression. Doing that makes later lines shorter and easier to read.

9. Code:
```lean
  have htel :
```
This line introduces an intermediate claim. The proof pauses to establish a fact that will be used shortly afterwards.

10. Code:
```lean
      (2 * Real.sin (Real.pi / (2 * d))) *
```
This line is one local step in the declaration. It either refines the formula being defined or advances the proof by a small algebraic or logical move.

11. Code:
```lean
        (∑ k ∈ Finset.range (d - 1), Real.sin (Real.pi * (k + 1) / d)) =
```
This line is one local step in the declaration. It either refines the formula being defined or advances the proof by a small algebraic or logical move.

12. Code:
```lean
      ∑ k ∈ Finset.range (d - 1), (g k - g (k + 1)) := by
```
This line says that a proof script begins here. Everything indented underneath is a sequence of instructions that Lean will check step by step.

13. Code:
```lean
    rw [Finset.mul_sum]
```
This line uses rewriting. Lean replaces one expression by an equal expression using the lemmas listed in brackets.

14. Code:
```lean
    refine Finset.sum_congr rfl ?_
```
This line is a more controlled version of `apply`. It sets up the proof with a partly specified argument and leaves smaller goals to solve next.

15. Code:
```lean
    intro k hk
```
This line introduces the variable or hypothesis named here into the proof context. In ordinary mathematical prose, it is the same as saying “let” or “assume”.

16. Code:
```lean
    dsimp [g]
```
This line is one local step in the declaration. It either refines the formula being defined or advances the proof by a small algebraic or logical move.

17. Code:
```lean
    have h := Real.two_mul_sin_mul_sin (Real.pi / (2 * d)) (Real.pi * (k + 1) / d)
```
This line introduces an intermediate claim. The proof pauses to establish a fact that will be used shortly afterwards.

18. Code:
```lean
    have harg1 :
```
This line introduces an intermediate claim. The proof pauses to establish a fact that will be used shortly afterwards.

19. Code:
```lean
        Real.pi / (2 * d) - Real.pi * (k + 1) / d =
```
This line is one local step in the declaration. It either refines the formula being defined or advances the proof by a small algebraic or logical move.

20. Code:
```lean
          -(Real.pi * (2 * k + 1) / (2 * d)) := by
```
This line says that a proof script begins here. Everything indented underneath is a sequence of instructions that Lean will check step by step.

21. Code:
```lean
      field_simp [hd_ne]
```
This line is one local step in the declaration. It either refines the formula being defined or advances the proof by a small algebraic or logical move.

22. Code:
```lean
      ring
```
This line normalizes an algebraic identity in a commutative ring, just as one would expand and collect like terms by hand.

23. Code:
```lean
    have harg2 :
```
This line introduces an intermediate claim. The proof pauses to establish a fact that will be used shortly afterwards.

24. Code:
```lean
        Real.pi / (2 * d) + Real.pi * (k + 1) / d =
```
This line is one local step in the declaration. It either refines the formula being defined or advances the proof by a small algebraic or logical move.

25. Code:
```lean
          Real.pi * (2 * ↑(k + 1) + 1) / (2 * d) := by
```
This line says that a proof script begins here. Everything indented underneath is a sequence of instructions that Lean will check step by step.

26. Code:
```lean
      field_simp [hd_ne]
```
This line is one local step in the declaration. It either refines the formula being defined or advances the proof by a small algebraic or logical move.

27. Code:
```lean
      norm_num [Nat.cast_add, Nat.cast_mul]
```
This line is one local step in the declaration. It either refines the formula being defined or advances the proof by a small algebraic or logical move.

28. Code:
```lean
      ring
```
This line normalizes an algebraic identity in a commutative ring, just as one would expand and collect like terms by hand.

29. Code:
```lean
    calc
```
This line begins a chained calculation. Each displayed step that follows must be justified by the indented proof after `:= by`.

30. Code:
```lean
      2 * Real.sin (Real.pi / (2 * d)) * Real.sin (Real.pi * (k + 1) / d)
```
This line is one local step in the declaration. It either refines the formula being defined or advances the proof by a small algebraic or logical move.

31. Code:
```lean
        = Real.cos (Real.pi / (2 * d) - Real.pi * (k + 1) / d) -
```
This line is one local step in the declaration. It either refines the formula being defined or advances the proof by a small algebraic or logical move.

32. Code:
```lean
            Real.cos (Real.pi / (2 * d) + Real.pi * (k + 1) / d) := h
```
This line is one local step in the declaration. It either refines the formula being defined or advances the proof by a small algebraic or logical move.

33. Code:
```lean
      _ = Real.cos (Real.pi * (2 * k + 1) / (2 * d)) -
```
This line is one step inside a `calc` block. Lean is checking that the new expression really follows from the previous one.

34. Code:
```lean
            Real.cos (Real.pi * (2 * ↑(k + 1) + 1) / (2 * d)) := by
```
This line says that a proof script begins here. Everything indented underneath is a sequence of instructions that Lean will check step by step.

35. Code:
```lean
            rw [harg1, Real.cos_neg, harg2]
```
This line uses rewriting. Lean replaces one expression by an equal expression using the lemmas listed in brackets.

36. Code:
```lean
  have hsum :
```
This line introduces an intermediate claim. The proof pauses to establish a fact that will be used shortly afterwards.

37. Code:
```lean
      ∑ k ∈ Finset.range (d - 1), (g k - g (k + 1)) = g 0 - g (d - 1) := by
```
This line says that a proof script begins here. Everything indented underneath is a sequence of instructions that Lean will check step by step.

38. Code:
```lean
    simpa using (Finset.sum_range_sub' g (d - 1))
```
This line simplifies the goal using definitions and known equalities. `simpa` means that, after simplification, the desired statement matches a theorem Lean already has.

39. Code:
```lean
  have hend : g 0 - g (d - 1) = 2 * Real.cos (Real.pi / (2 * d)) := by
```
This line says that a proof script begins here. Everything indented underneath is a sequence of instructions that Lean will check step by step.

40. Code:
```lean
    dsimp [g]
```
This line is one local step in the declaration. It either refines the formula being defined or advances the proof by a small algebraic or logical move.

41. Code:
```lean
    have h0 : Real.pi * (2 * (0 : ℕ) + 1) / (2 * d) = Real.pi / (2 * d) := by
```
This line says that a proof script begins here. Everything indented underneath is a sequence of instructions that Lean will check step by step.

42. Code:
```lean
      ring
```
This line normalizes an algebraic identity in a commutative ring, just as one would expand and collect like terms by hand.

43. Code:
```lean
    have hd_le : 1 ≤ d := Nat.succ_le_of_lt hd_pos
```
This line introduces an intermediate claim. The proof pauses to establish a fact that will be used shortly afterwards.

44. Code:
```lean
    have harg : Real.pi * (2 * ↑(d - 1) + 1) / (2 * d) = Real.pi - Real.pi / (2 * d) := by
```
This line says that a proof script begins here. Everything indented underneath is a sequence of instructions that Lean will check step by step.

45. Code:
```lean
      field_simp [hd_ne]
```
This line is one local step in the declaration. It either refines the formula being defined or advances the proof by a small algebraic or logical move.

46. Code:
```lean
      norm_num [Nat.cast_sub hd_le, Nat.cast_mul, Nat.cast_add]
```
This line is one local step in the declaration. It either refines the formula being defined or advances the proof by a small algebraic or logical move.

47. Code:
```lean
      ring
```
This line normalizes an algebraic identity in a commutative ring, just as one would expand and collect like terms by hand.

48. Code:
```lean
    rw [h0, harg, Real.cos_pi_sub]
```
This line uses rewriting. Lean replaces one expression by an equal expression using the lemmas listed in brackets.

49. Code:
```lean
    ring
```
This line normalizes an algebraic identity in a commutative ring, just as one would expand and collect like terms by hand.

50. Code:
```lean
  have hsin_pos : 0 < Real.sin (Real.pi / (2 * d)) := by
```
This line says that a proof script begins here. Everything indented underneath is a sequence of instructions that Lean will check step by step.

51. Code:
```lean
    apply Real.sin_pos_of_pos_of_lt_pi
```
This line applies an existing theorem to the current goal. Lean then asks the author to prove the theorem’s hypotheses.

52. Code:
```lean
    · positivity
```
This bullet starts a new subgoal produced by the previous tactic. Lean is now focusing on one branch of the argument.

53. Code:
```lean
    · have hd_gt_one : (1 : ℝ) < d := by
```
This line says that a proof script begins here. Everything indented underneath is a sequence of instructions that Lean will check step by step.

54. Code:
```lean
        exact_mod_cast ‹Fact (1 < d)›.out
```
This line finishes the current goal by giving Lean the exact theorem, lemma, or term that proves it.

55. Code:
```lean
      have htwo_d_gt_one : (1 : ℝ) < 2 * d := by
```
This line says that a proof script begins here. Everything indented underneath is a sequence of instructions that Lean will check step by step.

56. Code:
```lean
        nlinarith
```
This line solves the current numerical inequality by combining the equalities and inequalities already available in the context.

57. Code:
```lean
      have hpos : (0 : ℝ) < 2 * d := by
```
This line says that a proof script begins here. Everything indented underneath is a sequence of instructions that Lean will check step by step.

58. Code:
```lean
        positivity
```
This line asks Lean to prove that the displayed quantity is positive or nonnegative using standard positivity rules.

59. Code:
```lean
      rw [div_lt_iff₀ hpos]
```
This line uses rewriting. Lean replaces one expression by an equal expression using the lemmas listed in brackets.

60. Code:
```lean
      nlinarith [Real.pi_pos, htwo_d_gt_one]
```
This line solves the current numerical inequality by combining the equalities and inequalities already available in the context.

61. Code:
```lean
  have hmain :
```
This line introduces an intermediate claim. The proof pauses to establish a fact that will be used shortly afterwards.

62. Code:
```lean
      (2 * Real.sin (Real.pi / (2 * d))) *
```
This line is one local step in the declaration. It either refines the formula being defined or advances the proof by a small algebraic or logical move.

63. Code:
```lean
        (∑ k ∈ Finset.range (d - 1), Real.sin (Real.pi * (k + 1) / d)) =
```
This line is one local step in the declaration. It either refines the formula being defined or advances the proof by a small algebraic or logical move.

64. Code:
```lean
      2 * Real.cos (Real.pi / (2 * d)) := by
```
This line says that a proof script begins here. Everything indented underneath is a sequence of instructions that Lean will check step by step.

65. Code:
```lean
    rw [htel, hsum, hend]
```
This line uses rewriting. Lean replaces one expression by an equal expression using the lemmas listed in brackets.

66. Code:
```lean
  rw [Real.cot_eq_cos_div_sin]
```
This line uses rewriting. Lean replaces one expression by an equal expression using the lemmas listed in brackets.

67. Code:
```lean
  apply (eq_div_iff hsin_pos.ne').2
```
This line applies an existing theorem to the current goal. Lean then asks the author to prove the theorem’s hypotheses.

68. Code:
```lean
  nlinarith [hmain]
```
This line solves the current numerical inequality by combining the equalities and inequalities already available in the context.

## Mathematical summary

Restated without Lean syntax, `shifted_sine_sum_eq_cot` is the theorem or lemma written above.

- State the desired identity or inequality in Lean’s syntax.
- Introduce temporary names and intermediate claims that organize the argument.
- Use rewriting, simplification, and earlier lemmas to reduce the goal to standard matrix or norm manipulations.
- Close the remaining algebraic or order-theoretic steps with Lean’s proof tactics.

## Dependencies and downstream use

### Earlier declarations this depends on
- This declaration does not explicitly cite an earlier named declaration from the documented tree; it mostly uses Lean primitives or local algebraic steps.

### Later declarations that use this one
- [`norm_one_sub_ud_sum_eq_cot`](norm_one_sub_ud_sum_eq_cot.md) in `EndMatter/Eq7.lean`

## Backlinks

- [Back to `INDEX.md`](../../INDEX.md)
- [Back to the `EndMatter/Eq7.lean` section in the index](../../INDEX.md#diamond-endmatter-eq7-lean)
- [Previous declaration in this file](norm_one_sub_ud_eq_sin.md)
- [Next declaration in this file](norm_one_sub_ud_sum_eq_cot.md)