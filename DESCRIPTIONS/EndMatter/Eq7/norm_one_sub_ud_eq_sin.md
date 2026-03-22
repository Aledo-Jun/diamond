# norm_one_sub_ud_eq_sin

## Source location

- Original Lean file: `Diamond/EndMatter/Eq7.lean`
- Declaration name: `norm_one_sub_ud_eq_sin`
- Declaration kind: `theorem`

## Why this declaration exists

Each phase difference contributes the corresponding sine term.

 In the file `EndMatter/Eq7.lean`, it contributes to the explicit witness construction used to prove the lower bound labelled Eq. (7). Later proofs call this result by name, so documenting it makes the larger argument readable as a mathematical chain rather than as opaque proof script.

## Original code

```lean
/-- Each phase difference contributes the corresponding sine term. -/
theorem norm_one_sub_ud_eq_sin (d : ℕ) [Fact (1 < d)] (k : Fin d) :
    ‖1 - Ud d k k‖ = 2 * Real.sin (Real.pi * (k : ℝ) / d) := by
  have hd_pos : 0 < d := lt_trans Nat.zero_lt_one ‹Fact (1 < d)›.out
  have hnorm := Complex.norm_exp_I_mul_ofReal_sub_one ((2 * Real.pi * (k : ℝ)) / d)
  have hsin_nonneg : 0 ≤ Real.sin (Real.pi * (k : ℝ) / d) := by
    apply Real.sin_nonneg_of_nonneg_of_le_pi
    · positivity
    · have hk_lt : (k : ℝ) < d := by
        exact_mod_cast k.is_lt
      have hk_le : (k : ℝ) ≤ d := le_of_lt hk_lt
      have hd_posR : (0 : ℝ) < d := by
        exact_mod_cast hd_pos
      have hdiv_le : (k : ℝ) / d ≤ 1 := by
        rw [div_le_iff₀ hd_posR]
        linarith
      have harg_le : Real.pi * (k : ℝ) / d ≤ Real.pi := by
        have htmp : Real.pi * ((k : ℝ) / d) ≤ Real.pi := by
          nlinarith [Real.pi_pos, hdiv_le]
        simpa [div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using htmp
      exact harg_le
  calc
    ‖1 - Ud d k k‖ = ‖Ud d k k - 1‖ := by
      rw [norm_sub_rev]
    _ = ‖2 * Real.sin (((2 * Real.pi * (k : ℝ)) / d) / 2)‖ := by
      simpa [Ud, div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using hnorm
    _ = ‖2 * Real.sin (Real.pi * (k : ℝ) / d)‖ := by
      congr 2
      have hd_ne : (d : ℝ) ≠ 0 := by
        exact_mod_cast hd_pos.ne'
      field_simp [hd_ne]
    _ = 2 * Real.sin (Real.pi * (k : ℝ) / d) := by
      rw [Real.norm_eq_abs, abs_of_nonneg]
      exact mul_nonneg (by positivity) hsin_nonneg
```

## Block-by-block explanation

The explanation below follows the declaration block by block. Each block groups a coherent piece of the definition or proof, so the mathematical structure is easier to see than in a strictly line-oriented reading.

1. Code:
```lean
/-- Each phase difference contributes the corresponding sine term. -/
```
This is a Lean docstring. It is a human-written comment that tells readers what the declaration is meant to express before the formal code begins.

2. Code:
```lean
theorem norm_one_sub_ud_eq_sin (d : ℕ) [Fact (1 < d)] (k : Fin d) :
```
This line starts the `norm_one_sub_ud_eq_sin` declaration. Because it begins with `theorem`, Lean now knows what kind of named object is being introduced.

3. Code:
```lean
    ‖1 - Ud d k k‖ = 2 * Real.sin (Real.pi * (k : ℝ) / d) := by
```
This line says that a proof script begins here. Everything indented underneath is a sequence of instructions that Lean will check step by step.

4. Code:
```lean
  have hd_pos : 0 < d := lt_trans Nat.zero_lt_one ‹Fact (1 < d)›.out
```
This line introduces an intermediate claim. The proof pauses to establish a fact that will be used shortly afterwards.

5. Code:
```lean
  have hnorm := Complex.norm_exp_I_mul_ofReal_sub_one ((2 * Real.pi * (k : ℝ)) / d)
```
This line introduces an intermediate claim. The proof pauses to establish a fact that will be used shortly afterwards.

6. Code:
```lean
  have hsin_nonneg : 0 ≤ Real.sin (Real.pi * (k : ℝ) / d) := by
```
This line says that a proof script begins here. Everything indented underneath is a sequence of instructions that Lean will check step by step.

7. Code:
```lean
    apply Real.sin_nonneg_of_nonneg_of_le_pi
```
This line applies an existing theorem to the current goal. Lean then asks the author to prove the theorem’s hypotheses.

8. Code:
```lean
    · positivity
```
This bullet starts a new subgoal produced by the previous tactic. Lean is now focusing on one branch of the argument.

9. Code:
```lean
    · have hk_lt : (k : ℝ) < d := by
```
This line says that a proof script begins here. Everything indented underneath is a sequence of instructions that Lean will check step by step.

10. Code:
```lean
        exact_mod_cast k.is_lt
```
This line finishes the current goal by giving Lean the exact theorem, lemma, or term that proves it.

11. Code:
```lean
      have hk_le : (k : ℝ) ≤ d := le_of_lt hk_lt
```
This line introduces an intermediate claim. The proof pauses to establish a fact that will be used shortly afterwards.

12. Code:
```lean
      have hd_posR : (0 : ℝ) < d := by
```
This line says that a proof script begins here. Everything indented underneath is a sequence of instructions that Lean will check step by step.

13. Code:
```lean
        exact_mod_cast hd_pos
```
This line finishes the current goal by giving Lean the exact theorem, lemma, or term that proves it.

14. Code:
```lean
      have hdiv_le : (k : ℝ) / d ≤ 1 := by
```
This line says that a proof script begins here. Everything indented underneath is a sequence of instructions that Lean will check step by step.

15. Code:
```lean
        rw [div_le_iff₀ hd_posR]
```
This line uses rewriting. Lean replaces one expression by an equal expression using the lemmas listed in brackets.

16. Code:
```lean
        linarith
```
This line solves the current numerical inequality by combining the equalities and inequalities already available in the context.

17. Code:
```lean
      have harg_le : Real.pi * (k : ℝ) / d ≤ Real.pi := by
```
This line says that a proof script begins here. Everything indented underneath is a sequence of instructions that Lean will check step by step.

18. Code:
```lean
        have htmp : Real.pi * ((k : ℝ) / d) ≤ Real.pi := by
```
This line says that a proof script begins here. Everything indented underneath is a sequence of instructions that Lean will check step by step.

19. Code:
```lean
          nlinarith [Real.pi_pos, hdiv_le]
```
This line solves the current numerical inequality by combining the equalities and inequalities already available in the context.

20. Code:
```lean
        simpa [div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using htmp
```
This line simplifies the goal using definitions and known equalities. `simpa` means that, after simplification, the desired statement matches a theorem Lean already has.

21. Code:
```lean
      exact harg_le
```
This line finishes the current goal by giving Lean the exact theorem, lemma, or term that proves it.

22. Code:
```lean
  calc
```
This line begins a chained calculation. Each displayed step that follows must be justified by the indented proof after `:= by`.

23. Code:
```lean
    ‖1 - Ud d k k‖ = ‖Ud d k k - 1‖ := by
```
This line says that a proof script begins here. Everything indented underneath is a sequence of instructions that Lean will check step by step.

24. Code:
```lean
      rw [norm_sub_rev]
```
This line uses rewriting. Lean replaces one expression by an equal expression using the lemmas listed in brackets.

25. Code:
```lean
    _ = ‖2 * Real.sin (((2 * Real.pi * (k : ℝ)) / d) / 2)‖ := by
```
This line says that a proof script begins here. Everything indented underneath is a sequence of instructions that Lean will check step by step.

26. Code:
```lean
      simpa [Ud, div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using hnorm
```
This line simplifies the goal using definitions and known equalities. `simpa` means that, after simplification, the desired statement matches a theorem Lean already has.

27. Code:
```lean
    _ = ‖2 * Real.sin (Real.pi * (k : ℝ) / d)‖ := by
```
This line says that a proof script begins here. Everything indented underneath is a sequence of instructions that Lean will check step by step.

28. Code:
```lean
      congr 2
```
This line is one local step in the declaration. It either refines the formula being defined or advances the proof by a small algebraic or logical move.

29. Code:
```lean
      have hd_ne : (d : ℝ) ≠ 0 := by
```
This line says that a proof script begins here. Everything indented underneath is a sequence of instructions that Lean will check step by step.

30. Code:
```lean
        exact_mod_cast hd_pos.ne'
```
This line finishes the current goal by giving Lean the exact theorem, lemma, or term that proves it.

31. Code:
```lean
      field_simp [hd_ne]
```
This line is one local step in the declaration. It either refines the formula being defined or advances the proof by a small algebraic or logical move.

32. Code:
```lean
    _ = 2 * Real.sin (Real.pi * (k : ℝ) / d) := by
```
This line says that a proof script begins here. Everything indented underneath is a sequence of instructions that Lean will check step by step.

33. Code:
```lean
      rw [Real.norm_eq_abs, abs_of_nonneg]
```
This line uses rewriting. Lean replaces one expression by an equal expression using the lemmas listed in brackets.

34. Code:
```lean
      exact mul_nonneg (by positivity) hsin_nonneg
```
This line finishes the current goal by giving Lean the exact theorem, lemma, or term that proves it.

## Mathematical summary

Restated without Lean syntax, `norm_one_sub_ud_eq_sin` is the theorem or lemma written above.

- State the desired identity or inequality in Lean’s syntax.
- Introduce temporary names and intermediate claims that organize the argument.
- Use rewriting, simplification, and earlier lemmas to reduce the goal to standard matrix or norm manipulations.
- Close the remaining algebraic or order-theoretic steps with Lean’s proof tactics.

## Dependencies and downstream use

### Earlier declarations this depends on
- [`Ud`](../../Setups/Ud.md) from `Setups.lean`

### Later declarations that use this one
- [`norm_one_sub_ud_sum_eq_cot`](norm_one_sub_ud_sum_eq_cot.md) in `EndMatter/Eq7.lean`

## Backlinks

- [Back to `INDEX.md`](../../INDEX.md)
- [Back to the `EndMatter/Eq7.lean` section in the index](../../INDEX.md#diamond-endmatter-eq7-lean)
- [Previous declaration in this file](explicit_witness_traceNorm_eq_sum.md)
- [Next declaration in this file](shifted_sine_sum_eq_cot.md)