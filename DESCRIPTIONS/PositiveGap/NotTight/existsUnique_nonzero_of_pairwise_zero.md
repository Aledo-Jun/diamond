# existsUnique_nonzero_of_pairwise_zero

## Source location

- Original Lean file: `Diamond/PositiveGap/NotTight.lean`
- Declaration name: `existsUnique_nonzero_of_pairwise_zero`
- Declaration kind: `lemma`

## Why this declaration exists

If at most one entry can be nonzero and some entry is nonzero, then that entry is unique.

 In the file `PositiveGap/NotTight.lean`, it contributes to the finite-dimensional non-tightness argument and the equality-case analysis behind it. Later proofs call this result by name, so documenting it makes the larger argument readable as a mathematical chain rather than as opaque proof script.

## Original code

```lean
/-- If at most one entry can be nonzero and some entry is nonzero, then that entry is unique. -/
private lemma existsUnique_nonzero_of_pairwise_zero
    {ι : Type u} {p : ι → ℝ}
    (hexists : ∃ i, p i ≠ 0)
    (hpair : ∀ i j, i ≠ j → p i = 0 ∨ p j = 0) :
    ∃! i, p i ≠ 0 := by
  rcases hexists with ⟨i, hi⟩
  refine ⟨i, hi, ?_⟩
  intro j hj
  by_cases hji : j = i
  · simpa using hji
  · have hij : i ≠ j := by
      simpa [eq_comm] using hji
    rcases hpair i j hij with hzero | hzero
    · exact (hi hzero).elim
    · exact (hj hzero).elim
```

## Block-by-block explanation

The explanation below follows the declaration block by block. Each block groups a coherent piece of the definition or proof, so the mathematical structure is easier to see than in a strictly line-oriented reading.

1. Code:
```lean
/-- If at most one entry can be nonzero and some entry is nonzero, then that entry is unique. -/
```
This is a Lean docstring. It is a human-written comment that tells readers what the declaration is meant to express before the formal code begins.

2. Code:
```lean
private lemma existsUnique_nonzero_of_pairwise_zero
```
This line starts the `existsUnique_nonzero_of_pairwise_zero` declaration. Because it begins with `lemma`, Lean now knows what kind of named object is being introduced.

3. Code:
```lean
    {ι : Type u} {p : ι → ℝ}
```
This line is one local step in the declaration. It either refines the formula being defined or advances the proof by a small algebraic or logical move.

4. Code:
```lean
    (hexists : ∃ i, p i ≠ 0)
```
This line is one local step in the declaration. It either refines the formula being defined or advances the proof by a small algebraic or logical move.

5. Code:
```lean
    (hpair : ∀ i j, i ≠ j → p i = 0 ∨ p j = 0) :
```
This line is one local step in the declaration. It either refines the formula being defined or advances the proof by a small algebraic or logical move.

6. Code:
```lean
    ∃! i, p i ≠ 0 := by
```
This line says that a proof script begins here. Everything indented underneath is a sequence of instructions that Lean will check step by step.

7. Code:
```lean
  rcases hexists with ⟨i, hi⟩
```
This line is one local step in the declaration. It either refines the formula being defined or advances the proof by a small algebraic or logical move.

8. Code:
```lean
  refine ⟨i, hi, ?_⟩
```
This line is a more controlled version of `apply`. It sets up the proof with a partly specified argument and leaves smaller goals to solve next.

9. Code:
```lean
  intro j hj
```
This line introduces the variable or hypothesis named here into the proof context. In ordinary mathematical prose, it is the same as saying “let” or “assume”.

10. Code:
```lean
  by_cases hji : j = i
```
This line splits the proof into cases according to whether the named proposition is true or false.

11. Code:
```lean
  · simpa using hji
```
This bullet starts a new subgoal produced by the previous tactic. Lean is now focusing on one branch of the argument.

12. Code:
```lean
  · have hij : i ≠ j := by
```
This line says that a proof script begins here. Everything indented underneath is a sequence of instructions that Lean will check step by step.

13. Code:
```lean
      simpa [eq_comm] using hji
```
This line simplifies the goal using definitions and known equalities. `simpa` means that, after simplification, the desired statement matches a theorem Lean already has.

14. Code:
```lean
    rcases hpair i j hij with hzero | hzero
```
This line is one local step in the declaration. It either refines the formula being defined or advances the proof by a small algebraic or logical move.

15. Code:
```lean
    · exact (hi hzero).elim
```
This bullet starts a new subgoal produced by the previous tactic. Lean is now focusing on one branch of the argument.

16. Code:
```lean
    · exact (hj hzero).elim
```
This bullet starts a new subgoal produced by the previous tactic. Lean is now focusing on one branch of the argument.

## Mathematical summary

Restated without Lean syntax, `existsUnique_nonzero_of_pairwise_zero` is the theorem or lemma written above.

- State the desired identity or inequality in Lean’s syntax.
- Introduce temporary names and intermediate claims that organize the argument.
- Use rewriting, simplification, and earlier lemmas to reduce the goal to standard matrix or norm manipulations.
- Close the remaining algebraic or order-theoretic steps with Lean’s proof tactics.

## Dependencies and downstream use

### Earlier declarations this depends on
- This declaration does not explicitly cite an earlier named declaration from the documented tree; it mostly uses Lean primitives or local algebraic steps.

### Later declarations that use this one
- [`lemma1_eq_imp_rank_two`](lemma1_eq_imp_rank_two.md) in `PositiveGap/NotTight.lean`

## Backlinks

- [Back to `INDEX.md`](../../INDEX.md)
- [Back to the `PositiveGap/NotTight.lean` section in the index](../../INDEX.md#diamond-positivegap-nottight-lean)
- [Previous declaration in this file](pairwise_zero_of_sum_sq_eq_sq_sum.md)
- [Next declaration in this file](sum_sq_sub_avg_eq_aux.md)