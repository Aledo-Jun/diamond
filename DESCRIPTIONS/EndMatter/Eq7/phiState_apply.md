# phiState_apply

## Source location

- Original Lean file: `Diamond/EndMatter/Eq7.lean`
- Declaration name: `phiState_apply`
- Declaration kind: `theorem`

## Why this declaration exists

Entrywise formula for the maximally entangled state.

 In the file `EndMatter/Eq7.lean`, it contributes to the explicit witness construction used to prove the lower bound labelled Eq. (7). Later proofs call this result by name, so documenting it makes the larger argument readable as a mathematical chain rather than as opaque proof script.

## Original code

```lean
/-- Entrywise formula for the maximally entangled state. -/
theorem phiState_apply (d : ℕ) [Fact (1 < d)] (a b c e : Fin d) :
    phiState d (c, b) (a, e) = if c = b ∧ a = e then (d : ℂ)⁻¹ else 0 := by
  rw [phiState, Matrix.vecMulVec_apply]
  by_cases hcb : c = b
  · by_cases hae : a = e
    · simp only [omegaVec, hcb, hae, if_true, Pi.star_apply]
      simpa using inv_sqrt_mul_inv_sqrt d
    · simp [omegaVec, hcb, hae]
  · by_cases hae : a = e
    · simp [omegaVec, hcb, hae]
    · simp [omegaVec, hcb, hae]
```

## Block-by-block explanation

The explanation below follows the declaration block by block. Each block groups a coherent piece of the definition or proof, so the mathematical structure is easier to see than in a strictly line-oriented reading.

1. Code:
```lean
/-- Entrywise formula for the maximally entangled state. -/
```
This is a Lean docstring. It is a human-written comment that tells readers what the declaration is meant to express before the formal code begins.

2. Code:
```lean
theorem phiState_apply (d : ℕ) [Fact (1 < d)] (a b c e : Fin d) :
```
This line starts the `phiState_apply` declaration. Because it begins with `theorem`, Lean now knows what kind of named object is being introduced.

3. Code:
```lean
    phiState d (c, b) (a, e) = if c = b ∧ a = e then (d : ℂ)⁻¹ else 0 := by
```
This line says that a proof script begins here. Everything indented underneath is a sequence of instructions that Lean will check step by step.

4. Code:
```lean
  rw [phiState, Matrix.vecMulVec_apply]
```
This line uses rewriting. Lean replaces one expression by an equal expression using the lemmas listed in brackets.

5. Code:
```lean
  by_cases hcb : c = b
```
This line splits the proof into cases according to whether the named proposition is true or false.

6. Code:
```lean
  · by_cases hae : a = e
```
This bullet starts a new subgoal produced by the previous tactic. Lean is now focusing on one branch of the argument.

7. Code:
```lean
    · simp only [omegaVec, hcb, hae, if_true, Pi.star_apply]
```
This bullet starts a new subgoal produced by the previous tactic. Lean is now focusing on one branch of the argument.

8. Code:
```lean
      simpa using inv_sqrt_mul_inv_sqrt d
```
This line simplifies the goal using definitions and known equalities. `simpa` means that, after simplification, the desired statement matches a theorem Lean already has.

9. Code:
```lean
    · simp [omegaVec, hcb, hae]
```
This bullet starts a new subgoal produced by the previous tactic. Lean is now focusing on one branch of the argument.

10. Code:
```lean
  · by_cases hae : a = e
```
This bullet starts a new subgoal produced by the previous tactic. Lean is now focusing on one branch of the argument.

11. Code:
```lean
    · simp [omegaVec, hcb, hae]
```
This bullet starts a new subgoal produced by the previous tactic. Lean is now focusing on one branch of the argument.

12. Code:
```lean
    · simp [omegaVec, hcb, hae]
```
This bullet starts a new subgoal produced by the previous tactic. Lean is now focusing on one branch of the argument.

## Mathematical summary

Restated without Lean syntax, `phiState_apply` is the theorem or lemma written above.

- State the desired identity or inequality in Lean’s syntax.
- Introduce temporary names and intermediate claims that organize the argument.
- Use rewriting, simplification, and earlier lemmas to reduce the goal to standard matrix or norm manipulations.
- Close the remaining algebraic or order-theoretic steps with Lean’s proof tactics.

## Dependencies and downstream use

### Earlier declarations this depends on
- [`omegaVec`](omegaVec.md) from `EndMatter/Eq7.lean`
- [`phiState`](phiState.md) from `EndMatter/Eq7.lean`
- [`inv_sqrt_mul_inv_sqrt`](inv_sqrt_mul_inv_sqrt.md) from `EndMatter/Eq7.lean`

### Later declarations that use this one
- [`transpose_phiState_eq_swap`](transpose_phiState_eq_swap.md) in `EndMatter/Eq7.lean`
- [`transpose_ad_phiState_eq_swap_mul_phase`](transpose_ad_phiState_eq_swap_mul_phase.md) in `EndMatter/Eq7.lean`

## Backlinks

- [Back to `INDEX.md`](../../INDEX.md)
- [Back to the `EndMatter/Eq7.lean` section in the index](../../INDEX.md#diamond-endmatter-eq7-lean)
- [Previous declaration in this file](phiState_isDensityState.md)
- [Next declaration in this file](transpose_phiState_eq_swap.md)