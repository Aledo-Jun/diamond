# norm_one_sub_ud_sum_eq_cot

## Source location

- Original Lean file: `Diamond/EndMatter/Eq7.lean`
- Declaration name: `norm_one_sub_ud_sum_eq_cot`
- Declaration kind: `theorem`

## Why this declaration exists

The one-dimensional phase sum evaluates to the cotangent expression in Eq. (7).

 In the file `EndMatter/Eq7.lean`, it contributes to the explicit witness construction used to prove the lower bound labelled Eq. (7). Later proofs call this result by name, so documenting it makes the larger argument readable as a mathematical chain rather than as opaque proof script.

## Original code

```lean
/-- The one-dimensional phase sum evaluates to the cotangent expression in Eq. (7). -/
theorem norm_one_sub_ud_sum_eq_cot (d : ℕ) [Fact (1 < d)] :
    (∑ k : Fin d, ‖1 - Ud d k k‖) = 2 * Real.cot (Real.pi / (2 * d)) := by
  calc
    (∑ k : Fin d, ‖1 - Ud d k k‖)
      = ∑ k : Fin d, 2 * Real.sin (Real.pi * (k : ℝ) / d) := by
          refine Finset.sum_congr rfl ?_
          intro k hk
          exact norm_one_sub_ud_eq_sin d k
    _ = ∑ k ∈ Finset.range d, 2 * Real.sin (Real.pi * k / d) := by
          simpa using (Fin.sum_univ_eq_sum_range (fun k => 2 * Real.sin (Real.pi * k / d)) d)
    _ = 2 * Real.cot (Real.pi / (2 * d)) := by
          have hd_pos : 0 < d := lt_trans Nat.zero_lt_one ‹Fact (1 < d)›.out
          have hd_eq : d = (d - 1) + 1 := by
            simpa [Nat.succ_eq_add_one, Nat.add_comm] using
              (Nat.succ_pred_eq_of_pos hd_pos).symm
          have hd_eqR : (((d - 1 : ℕ) : ℝ) + 1) = d := by
            exact_mod_cast hd_eq.symm
          rw [hd_eq, Finset.sum_range_succ']
          simp only [Nat.cast_add, Nat.cast_one, CharP.cast_eq_zero, mul_zero, zero_div,
            Real.sin_zero, add_zero]
          rw [hd_eqR]
          have hs2 :
              2 * (∑ k ∈ Finset.range (d - 1), Real.sin (Real.pi * (k + 1) / d)) =
                2 * Real.cot (Real.pi / (2 * d)) := by
            nlinarith [shifted_sine_sum_eq_cot d]
          simpa [Finset.mul_sum] using hs2
```

## Block-by-block explanation

The explanation below follows the declaration block by block. Each block groups a coherent piece of the definition or proof, so the mathematical structure is easier to see than in a strictly line-oriented reading.

1. Code:
```lean
/-- The one-dimensional phase sum evaluates to the cotangent expression in Eq. (7). -/
```
This is a Lean docstring. It is a human-written comment that tells readers what the declaration is meant to express before the formal code begins.

2. Code:
```lean
theorem norm_one_sub_ud_sum_eq_cot (d : ℕ) [Fact (1 < d)] :
```
This line starts the `norm_one_sub_ud_sum_eq_cot` declaration. Because it begins with `theorem`, Lean now knows what kind of named object is being introduced.

3. Code:
```lean
    (∑ k : Fin d, ‖1 - Ud d k k‖) = 2 * Real.cot (Real.pi / (2 * d)) := by
```
This line says that a proof script begins here. Everything indented underneath is a sequence of instructions that Lean will check step by step.

4. Code:
```lean
  calc
```
This line begins a chained calculation. Each displayed step that follows must be justified by the indented proof after `:= by`.

5. Code:
```lean
    (∑ k : Fin d, ‖1 - Ud d k k‖)
```
This line is one local step in the declaration. It either refines the formula being defined or advances the proof by a small algebraic or logical move.

6. Code:
```lean
      = ∑ k : Fin d, 2 * Real.sin (Real.pi * (k : ℝ) / d) := by
```
This line says that a proof script begins here. Everything indented underneath is a sequence of instructions that Lean will check step by step.

7. Code:
```lean
          refine Finset.sum_congr rfl ?_
```
This line is a more controlled version of `apply`. It sets up the proof with a partly specified argument and leaves smaller goals to solve next.

8. Code:
```lean
          intro k hk
```
This line introduces the variable or hypothesis named here into the proof context. In ordinary mathematical prose, it is the same as saying “let” or “assume”.

9. Code:
```lean
          exact norm_one_sub_ud_eq_sin d k
```
This line finishes the current goal by giving Lean the exact theorem, lemma, or term that proves it.

10. Code:
```lean
    _ = ∑ k ∈ Finset.range d, 2 * Real.sin (Real.pi * k / d) := by
```
This line says that a proof script begins here. Everything indented underneath is a sequence of instructions that Lean will check step by step.

11. Code:
```lean
          simpa using (Fin.sum_univ_eq_sum_range (fun k => 2 * Real.sin (Real.pi * k / d)) d)
```
This line simplifies the goal using definitions and known equalities. `simpa` means that, after simplification, the desired statement matches a theorem Lean already has.

12. Code:
```lean
    _ = 2 * Real.cot (Real.pi / (2 * d)) := by
```
This line says that a proof script begins here. Everything indented underneath is a sequence of instructions that Lean will check step by step.

13. Code:
```lean
          have hd_pos : 0 < d := lt_trans Nat.zero_lt_one ‹Fact (1 < d)›.out
```
This line introduces an intermediate claim. The proof pauses to establish a fact that will be used shortly afterwards.

14. Code:
```lean
          have hd_eq : d = (d - 1) + 1 := by
```
This line says that a proof script begins here. Everything indented underneath is a sequence of instructions that Lean will check step by step.

15. Code:
```lean
            simpa [Nat.succ_eq_add_one, Nat.add_comm] using
```
This line simplifies the goal using definitions and known equalities. `simpa` means that, after simplification, the desired statement matches a theorem Lean already has.

16. Code:
```lean
              (Nat.succ_pred_eq_of_pos hd_pos).symm
```
This line is one local step in the declaration. It either refines the formula being defined or advances the proof by a small algebraic or logical move.

17. Code:
```lean
          have hd_eqR : (((d - 1 : ℕ) : ℝ) + 1) = d := by
```
This line says that a proof script begins here. Everything indented underneath is a sequence of instructions that Lean will check step by step.

18. Code:
```lean
            exact_mod_cast hd_eq.symm
```
This line finishes the current goal by giving Lean the exact theorem, lemma, or term that proves it.

19. Code:
```lean
          rw [hd_eq, Finset.sum_range_succ']
```
This line uses rewriting. Lean replaces one expression by an equal expression using the lemmas listed in brackets.

20. Code:
```lean
          simp only [Nat.cast_add, Nat.cast_one, CharP.cast_eq_zero, mul_zero, zero_div,
```
This line simplifies the goal using definitions and known equalities. `simpa` means that, after simplification, the desired statement matches a theorem Lean already has.

21. Code:
```lean
            Real.sin_zero, add_zero]
```
This line is one local step in the declaration. It either refines the formula being defined or advances the proof by a small algebraic or logical move.

22. Code:
```lean
          rw [hd_eqR]
```
This line uses rewriting. Lean replaces one expression by an equal expression using the lemmas listed in brackets.

23. Code:
```lean
          have hs2 :
```
This line introduces an intermediate claim. The proof pauses to establish a fact that will be used shortly afterwards.

24. Code:
```lean
              2 * (∑ k ∈ Finset.range (d - 1), Real.sin (Real.pi * (k + 1) / d)) =
```
This line is one local step in the declaration. It either refines the formula being defined or advances the proof by a small algebraic or logical move.

25. Code:
```lean
                2 * Real.cot (Real.pi / (2 * d)) := by
```
This line says that a proof script begins here. Everything indented underneath is a sequence of instructions that Lean will check step by step.

26. Code:
```lean
            nlinarith [shifted_sine_sum_eq_cot d]
```
This line solves the current numerical inequality by combining the equalities and inequalities already available in the context.

27. Code:
```lean
          simpa [Finset.mul_sum] using hs2
```
This line simplifies the goal using definitions and known equalities. `simpa` means that, after simplification, the desired statement matches a theorem Lean already has.

## Mathematical summary

Restated without Lean syntax, `norm_one_sub_ud_sum_eq_cot` is the theorem or lemma written above.

- State the desired identity or inequality in Lean’s syntax.
- Introduce temporary names and intermediate claims that organize the argument.
- Use rewriting, simplification, and earlier lemmas to reduce the goal to standard matrix or norm manipulations.
- Close the remaining algebraic or order-theoretic steps with Lean’s proof tactics.

## Dependencies and downstream use

### Earlier declarations this depends on
- [`Ud`](../../Setups/Ud.md) from `Setups.lean`
- [`norm_one_sub_ud_eq_sin`](norm_one_sub_ud_eq_sin.md) from `EndMatter/Eq7.lean`
- [`shifted_sine_sum_eq_cot`](shifted_sine_sum_eq_cot.md) from `EndMatter/Eq7.lean`

### Later declarations that use this one
- [`explicit_witness_traceNorm_eq`](explicit_witness_traceNorm_eq.md) in `EndMatter/Eq7.lean`

## Backlinks

- [Back to `INDEX.md`](../../INDEX.md)
- [Back to the `EndMatter/Eq7.lean` section in the index](../../INDEX.md#diamond-endmatter-eq7-lean)
- [Previous declaration in this file](shifted_sine_sum_eq_cot.md)
- [Next declaration in this file](explicit_witness_traceNorm_eq.md)