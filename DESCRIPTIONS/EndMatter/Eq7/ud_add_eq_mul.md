# ud_add_eq_mul

## Source location

- Original Lean file: `Diamond/EndMatter/Eq7.lean`
- Declaration name: `ud_add_eq_mul`
- Declaration kind: `theorem`

## Why this declaration exists

The phase diagonal satisfies the expected addition law on `Fin d`.

 In the file `EndMatter/Eq7.lean`, it contributes to the explicit witness construction used to prove the lower bound labelled Eq. (7). Later proofs call this result by name, so documenting it makes the larger argument readable as a mathematical chain rather than as opaque proof script.

## Original code

```lean
/-- The phase diagonal satisfies the expected addition law on `Fin d`. -/
theorem ud_add_eq_mul (d : ℕ) [Fact (1 < d)] (a b : Fin d) :
    Ud d (a + b) (a + b) = Ud d a a * Ud d b b := by
  have hd_pos : 0 < d := lt_trans Nat.zero_lt_one ‹Fact (1 < d)›.out
  have hd_ne : (d : ℂ) ≠ 0 := by
    exact_mod_cast hd_pos.ne'
  let q : ℕ := ((a : ℕ) + (b : ℕ)) / d
  let A : ℂ := (2 * Real.pi * Complex.I * (a : ℂ)) / (d : ℂ)
  let B : ℂ := (2 * Real.pi * Complex.I * (b : ℂ)) / (d : ℂ)
  let Q : ℂ := (q : ℂ) * (2 * Real.pi * Complex.I)
  have hcast :
      (((a + b : Fin d) : ℕ) : ℂ) = (a : ℂ) + (b : ℂ) - (d : ℂ) * (q : ℂ) := by
    have hnat : ((a + b : Fin d) : ℕ) = (a : ℕ) + (b : ℕ) - d * q := by
      simp [Fin.val_add, Nat.mod_eq_sub_mul_div, q]
    have hle : d * q ≤ (a : ℕ) + (b : ℕ) := by
      dsimp [q]
      exact Nat.mul_div_le _ _
    calc
      (((a + b : Fin d) : ℕ) : ℂ)
          = (((a : ℕ) + (b : ℕ) - d * q : ℕ) : ℂ) := by
              exact congrArg (fun n : ℕ => (n : ℂ)) hnat
      _ = (a : ℂ) + (b : ℂ) - (d : ℂ) * (q : ℂ) := by
            norm_num [Nat.cast_sub hle, Nat.cast_add, Nat.cast_mul]
  have hexp :
      (2 * Real.pi * Complex.I * (((a + b : Fin d) : ℕ) : ℂ)) / (d : ℂ) = A + B - Q := by
    rw [hcast]
    dsimp [A, B, Q]
    field_simp [hd_ne]
  have hperiod : Complex.exp (-Q) = 1 := by
    dsimp [Q]
    have h :
        -(↑q * (2 * Real.pi * Complex.I)) =
          (((-(q : ℤ)) : ℂ) * (2 * Real.pi * Complex.I)) := by
      norm_num
    rw [h]
    simpa using (Complex.exp_int_mul_two_pi_mul_I (-(q : ℤ)))
  unfold Ud
  simp only [Matrix.diagonal_apply_eq]
  rw [hexp, sub_eq_add_neg, Complex.exp_add, Complex.exp_add, hperiod]
  simp [A, B, mul_assoc]
```

## Line-by-line explanation

The explanation below follows the declaration one physical line at a time. For long proofs, some lines are tiny bookkeeping steps; those are still explained, but briefly.

1. Code:
```lean
/-- The phase diagonal satisfies the expected addition law on `Fin d`. -/
```
This is a Lean docstring. It is a human-written comment that tells readers what the declaration is meant to express before the formal code begins.

2. Code:
```lean
theorem ud_add_eq_mul (d : ℕ) [Fact (1 < d)] (a b : Fin d) :
```
This line starts the `ud_add_eq_mul` declaration. Because it begins with `theorem`, Lean now knows what kind of named object is being introduced.

3. Code:
```lean
    Ud d (a + b) (a + b) = Ud d a a * Ud d b b := by
```
This line says that a proof script begins here. Everything indented underneath is a sequence of instructions that Lean will check step by step.

4. Code:
```lean
  have hd_pos : 0 < d := lt_trans Nat.zero_lt_one ‹Fact (1 < d)›.out
```
This line introduces an intermediate claim. The proof pauses to establish a fact that will be used shortly afterwards.

5. Code:
```lean
  have hd_ne : (d : ℂ) ≠ 0 := by
```
This line says that a proof script begins here. Everything indented underneath is a sequence of instructions that Lean will check step by step.

6. Code:
```lean
    exact_mod_cast hd_pos.ne'
```
This line finishes the current goal by giving Lean the exact theorem, lemma, or term that proves it.

7. Code:
```lean
  let q : ℕ := ((a : ℕ) + (b : ℕ)) / d
```
This line gives a temporary name to an expression. Doing that makes later lines shorter and easier to read.

8. Code:
```lean
  let A : ℂ := (2 * Real.pi * Complex.I * (a : ℂ)) / (d : ℂ)
```
This line gives a temporary name to an expression. Doing that makes later lines shorter and easier to read.

9. Code:
```lean
  let B : ℂ := (2 * Real.pi * Complex.I * (b : ℂ)) / (d : ℂ)
```
This line gives a temporary name to an expression. Doing that makes later lines shorter and easier to read.

10. Code:
```lean
  let Q : ℂ := (q : ℂ) * (2 * Real.pi * Complex.I)
```
This line gives a temporary name to an expression. Doing that makes later lines shorter and easier to read.

11. Code:
```lean
  have hcast :
```
This line introduces an intermediate claim. The proof pauses to establish a fact that will be used shortly afterwards.

12. Code:
```lean
      (((a + b : Fin d) : ℕ) : ℂ) = (a : ℂ) + (b : ℂ) - (d : ℂ) * (q : ℂ) := by
```
This line says that a proof script begins here. Everything indented underneath is a sequence of instructions that Lean will check step by step.

13. Code:
```lean
    have hnat : ((a + b : Fin d) : ℕ) = (a : ℕ) + (b : ℕ) - d * q := by
```
This line says that a proof script begins here. Everything indented underneath is a sequence of instructions that Lean will check step by step.

14. Code:
```lean
      simp [Fin.val_add, Nat.mod_eq_sub_mul_div, q]
```
This line simplifies the goal using definitions and known equalities. `simpa` means that, after simplification, the desired statement matches a theorem Lean already has.

15. Code:
```lean
    have hle : d * q ≤ (a : ℕ) + (b : ℕ) := by
```
This line says that a proof script begins here. Everything indented underneath is a sequence of instructions that Lean will check step by step.

16. Code:
```lean
      dsimp [q]
```
This line is one local step in the declaration. It either refines the formula being defined or advances the proof by a small algebraic or logical move.

17. Code:
```lean
      exact Nat.mul_div_le _ _
```
This line finishes the current goal by giving Lean the exact theorem, lemma, or term that proves it.

18. Code:
```lean
    calc
```
This line begins a chained calculation. Each displayed step that follows must be justified by the indented proof after `:= by`.

19. Code:
```lean
      (((a + b : Fin d) : ℕ) : ℂ)
```
This line is one local step in the declaration. It either refines the formula being defined or advances the proof by a small algebraic or logical move.

20. Code:
```lean
          = (((a : ℕ) + (b : ℕ) - d * q : ℕ) : ℂ) := by
```
This line says that a proof script begins here. Everything indented underneath is a sequence of instructions that Lean will check step by step.

21. Code:
```lean
              exact congrArg (fun n : ℕ => (n : ℂ)) hnat
```
This line finishes the current goal by giving Lean the exact theorem, lemma, or term that proves it.

22. Code:
```lean
      _ = (a : ℂ) + (b : ℂ) - (d : ℂ) * (q : ℂ) := by
```
This line says that a proof script begins here. Everything indented underneath is a sequence of instructions that Lean will check step by step.

23. Code:
```lean
            norm_num [Nat.cast_sub hle, Nat.cast_add, Nat.cast_mul]
```
This line is one local step in the declaration. It either refines the formula being defined or advances the proof by a small algebraic or logical move.

24. Code:
```lean
  have hexp :
```
This line introduces an intermediate claim. The proof pauses to establish a fact that will be used shortly afterwards.

25. Code:
```lean
      (2 * Real.pi * Complex.I * (((a + b : Fin d) : ℕ) : ℂ)) / (d : ℂ) = A + B - Q := by
```
This line says that a proof script begins here. Everything indented underneath is a sequence of instructions that Lean will check step by step.

26. Code:
```lean
    rw [hcast]
```
This line uses rewriting. Lean replaces one expression by an equal expression using the lemmas listed in brackets.

27. Code:
```lean
    dsimp [A, B, Q]
```
This line is one local step in the declaration. It either refines the formula being defined or advances the proof by a small algebraic or logical move.

28. Code:
```lean
    field_simp [hd_ne]
```
This line is one local step in the declaration. It either refines the formula being defined or advances the proof by a small algebraic or logical move.

29. Code:
```lean
  have hperiod : Complex.exp (-Q) = 1 := by
```
This line says that a proof script begins here. Everything indented underneath is a sequence of instructions that Lean will check step by step.

30. Code:
```lean
    dsimp [Q]
```
This line is one local step in the declaration. It either refines the formula being defined or advances the proof by a small algebraic or logical move.

31. Code:
```lean
    have h :
```
This line introduces an intermediate claim. The proof pauses to establish a fact that will be used shortly afterwards.

32. Code:
```lean
        -(↑q * (2 * Real.pi * Complex.I)) =
```
This line is one local step in the declaration. It either refines the formula being defined or advances the proof by a small algebraic or logical move.

33. Code:
```lean
          (((-(q : ℤ)) : ℂ) * (2 * Real.pi * Complex.I)) := by
```
This line says that a proof script begins here. Everything indented underneath is a sequence of instructions that Lean will check step by step.

34. Code:
```lean
      norm_num
```
This line is one local step in the declaration. It either refines the formula being defined or advances the proof by a small algebraic or logical move.

35. Code:
```lean
    rw [h]
```
This line uses rewriting. Lean replaces one expression by an equal expression using the lemmas listed in brackets.

36. Code:
```lean
    simpa using (Complex.exp_int_mul_two_pi_mul_I (-(q : ℤ)))
```
This line simplifies the goal using definitions and known equalities. `simpa` means that, after simplification, the desired statement matches a theorem Lean already has.

37. Code:
```lean
  unfold Ud
```
This line is one local step in the declaration. It either refines the formula being defined or advances the proof by a small algebraic or logical move.

38. Code:
```lean
  simp only [Matrix.diagonal_apply_eq]
```
This line simplifies the goal using definitions and known equalities. `simpa` means that, after simplification, the desired statement matches a theorem Lean already has.

39. Code:
```lean
  rw [hexp, sub_eq_add_neg, Complex.exp_add, Complex.exp_add, hperiod]
```
This line uses rewriting. Lean replaces one expression by an equal expression using the lemmas listed in brackets.

40. Code:
```lean
  simp [A, B, mul_assoc]
```
This line simplifies the goal using definitions and known equalities. `simpa` means that, after simplification, the desired statement matches a theorem Lean already has.

## Mathematical summary

Restated without Lean syntax, `ud_add_eq_mul` is the theorem or lemma written above.

- State the desired identity or inequality in Lean’s syntax.
- Introduce temporary names and intermediate claims that organize the argument.
- Use rewriting, simplification, and earlier lemmas to reduce the goal to standard matrix or norm manipulations.
- Close the remaining algebraic or order-theoretic steps with Lean’s proof tactics.

## Dependencies and downstream use

### Earlier declarations this depends on
- [`Ud`](../../Setups/Ud.md) from `Setups.lean`

### Later declarations that use this one
- [`ud_add_mul_star_eq`](ud_add_mul_star_eq.md) in `EndMatter/Eq7.lean`

## Backlinks

- [Back to `INDEX.md`](../../INDEX.md)
- [Back to the `EndMatter/Eq7.lean` section in the index](../../INDEX.md#diamond-endmatter-eq7-lean)
- [Previous declaration in this file](theorem_eq7_witness_bound_explicit.md)
- [Next declaration in this file](ud_mul_star_self.md)