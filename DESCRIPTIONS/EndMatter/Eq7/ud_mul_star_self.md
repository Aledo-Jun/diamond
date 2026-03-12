# ud_mul_star_self

## Source location

- Original Lean file: `Diamond/EndMatter/Eq7.lean`
- Declaration name: `ud_mul_star_self`
- Declaration kind: `theorem`

## Why this declaration exists

The phase diagonal has unit-modulus entries.

 In the file `EndMatter/Eq7.lean`, it contributes to the explicit witness construction used to prove the lower bound labelled Eq. (7). Later proofs call this result by name, so documenting it makes the larger argument readable as a mathematical chain rather than as opaque proof script.

## Original code

```lean
/-- The phase diagonal has unit-modulus entries. -/
theorem ud_mul_star_self (d : ℕ) [Fact (1 < d)] (b : Fin d) :
    Ud d b b * star (Ud d b b) = 1 := by
  have hd_pos : 0 < d := lt_trans Nat.zero_lt_one ‹Fact (1 < d)›.out
  have hd_ne : (d : ℂ) ≠ 0 := by
    exact_mod_cast hd_pos.ne'
  have hrew :
      Ud d b b = Complex.exp ((((2 * Real.pi * (b : ℝ)) / d : ℝ) : ℂ) * Complex.I) := by
    simp [Ud]
    congr 1
    field_simp [hd_ne]
  rw [hrew]
  change Complex.exp (↑((2 * Real.pi * ↑b) / d) * Complex.I) *
      (starRingEnd ℂ) (Complex.exp (↑((2 * Real.pi * ↑b) / d) * Complex.I)) = 1
  rw [Complex.mul_conj, Complex.normSq_eq_norm_sq, Complex.norm_exp_ofReal_mul_I]
  norm_num
```

## Line-by-line explanation

The explanation below follows the declaration one physical line at a time. For long proofs, some lines are tiny bookkeeping steps; those are still explained, but briefly.

1. Code:
```lean
/-- The phase diagonal has unit-modulus entries. -/
```
This is a Lean docstring. It is a human-written comment that tells readers what the declaration is meant to express before the formal code begins.

2. Code:
```lean
theorem ud_mul_star_self (d : ℕ) [Fact (1 < d)] (b : Fin d) :
```
This line starts the `ud_mul_star_self` declaration. Because it begins with `theorem`, Lean now knows what kind of named object is being introduced.

3. Code:
```lean
    Ud d b b * star (Ud d b b) = 1 := by
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
  have hrew :
```
This line introduces an intermediate claim. The proof pauses to establish a fact that will be used shortly afterwards.

8. Code:
```lean
      Ud d b b = Complex.exp ((((2 * Real.pi * (b : ℝ)) / d : ℝ) : ℂ) * Complex.I) := by
```
This line says that a proof script begins here. Everything indented underneath is a sequence of instructions that Lean will check step by step.

9. Code:
```lean
    simp [Ud]
```
This line simplifies the goal using definitions and known equalities. `simpa` means that, after simplification, the desired statement matches a theorem Lean already has.

10. Code:
```lean
    congr 1
```
This line is one local step in the declaration. It either refines the formula being defined or advances the proof by a small algebraic or logical move.

11. Code:
```lean
    field_simp [hd_ne]
```
This line is one local step in the declaration. It either refines the formula being defined or advances the proof by a small algebraic or logical move.

12. Code:
```lean
  rw [hrew]
```
This line uses rewriting. Lean replaces one expression by an equal expression using the lemmas listed in brackets.

13. Code:
```lean
  change Complex.exp (↑((2 * Real.pi * ↑b) / d) * Complex.I) *
```
This line replaces the current goal by a definitionally equal goal that is easier to manipulate.

14. Code:
```lean
      (starRingEnd ℂ) (Complex.exp (↑((2 * Real.pi * ↑b) / d) * Complex.I)) = 1
```
This line is one local step in the declaration. It either refines the formula being defined or advances the proof by a small algebraic or logical move.

15. Code:
```lean
  rw [Complex.mul_conj, Complex.normSq_eq_norm_sq, Complex.norm_exp_ofReal_mul_I]
```
This line uses rewriting. Lean replaces one expression by an equal expression using the lemmas listed in brackets.

16. Code:
```lean
  norm_num
```
This line is one local step in the declaration. It either refines the formula being defined or advances the proof by a small algebraic or logical move.

## Mathematical summary

Restated without Lean syntax, `ud_mul_star_self` is the theorem or lemma written above.

- State the desired identity or inequality in Lean’s syntax.
- Introduce temporary names and intermediate claims that organize the argument.
- Use rewriting, simplification, and earlier lemmas to reduce the goal to standard matrix or norm manipulations.
- Close the remaining algebraic or order-theoretic steps with Lean’s proof tactics.

## Dependencies and downstream use

### Earlier declarations this depends on
- [`Ud`](../../Setups/Ud.md) from `Setups.lean`

### Later declarations that use this one
- [`ud_conjTranspose_mul_self`](ud_conjTranspose_mul_self.md) in `EndMatter/Eq7.lean`
- [`ud_add_mul_star_eq`](ud_add_mul_star_eq.md) in `EndMatter/Eq7.lean`

## Backlinks

- [Back to `INDEX.md`](../../INDEX.md)
- [Back to the `EndMatter/Eq7.lean` section in the index](../../INDEX.md#diamond-endmatter-eq7-lean)
- [Previous declaration in this file](ud_add_eq_mul.md)
- [Next declaration in this file](ud_conjTranspose_mul_self.md)