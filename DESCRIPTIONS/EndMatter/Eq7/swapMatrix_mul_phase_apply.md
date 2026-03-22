# swapMatrix_mul_phase_apply

## Source location

- Original Lean file: `Diamond/EndMatter/Eq7.lean`
- Declaration name: `swapMatrix_mul_phase_apply`
- Declaration kind: `theorem`

## Why this declaration exists

This theorem records a reusable fact named `swapMatrix_mul_phase_apply`. Its role is to make the later proof flow easier to state and reuse.

 In the file `EndMatter/Eq7.lean`, it contributes to the explicit witness construction used to prove the lower bound labelled Eq. (7). Later proofs call this result by name, so documenting it makes the larger argument readable as a mathematical chain rather than as opaque proof script.

## Original code

```lean
theorem swapMatrix_mul_phase_apply (d : ℕ) [Fact (1 < d)] (a b c e : Fin d) :
    (swapMatrix d * ((Ud d)ᵀ ⊗ₖ star (Ud d))) (a, b) (c, e) =
      if b = c ∧ a = e then Ud d b b * star (Ud d e e) else 0 := by
  classical
  rw [Matrix.mul_apply]
  rw [Finset.sum_eq_single (b, a)]
  · by_cases hae : a = e
    · simp [swapMatrix, Ud, Matrix.diagonal_apply, hae, and_comm]
    · have hea : ¬ e = a := by
        simpa [eq_comm] using hae
      simp [swapMatrix, Ud, Matrix.diagonal_apply, hae, hea, and_comm]
  · intro x _ hne
    have hswap : ¬ (a = x.2 ∧ b = x.1) := by
      intro hx
      apply hne
      ext <;> simp [hx.1, hx.2]
    simp [swapMatrix, hswap]
  · intro hba
    simp at hba
```

## Block-by-block explanation

The explanation below follows the declaration block by block. Each block groups a coherent piece of the definition or proof, so the mathematical structure is easier to see than in a strictly line-oriented reading.

1. Code:
```lean
theorem swapMatrix_mul_phase_apply (d : ℕ) [Fact (1 < d)] (a b c e : Fin d) :
```
This line starts the `swapMatrix_mul_phase_apply` declaration. Because it begins with `theorem`, Lean now knows what kind of named object is being introduced.

2. Code:
```lean
    (swapMatrix d * ((Ud d)ᵀ ⊗ₖ star (Ud d))) (a, b) (c, e) =
```
This line is one local step in the declaration. It either refines the formula being defined or advances the proof by a small algebraic or logical move.  `Matrix d d ℂ` means a square matrix with complex entries; the index type `d` tells Lean which rows and columns exist.  The symbol `⊗ₖ` is the Kronecker (tensor) product of matrices.  The superscript `ᵀ` means ordinary transpose.

3. Code:
```lean
      if b = c ∧ a = e then Ud d b b * star (Ud d e e) else 0 := by
```
This line says that a proof script begins here. Everything indented underneath is a sequence of instructions that Lean will check step by step.

4. Code:
```lean
  classical
```
This line is one local step in the declaration. It either refines the formula being defined or advances the proof by a small algebraic or logical move.

5. Code:
```lean
  rw [Matrix.mul_apply]
```
This line uses rewriting. Lean replaces one expression by an equal expression using the lemmas listed in brackets.

6. Code:
```lean
  rw [Finset.sum_eq_single (b, a)]
```
This line uses rewriting. Lean replaces one expression by an equal expression using the lemmas listed in brackets.

7. Code:
```lean
  · by_cases hae : a = e
```
This bullet starts a new subgoal produced by the previous tactic. Lean is now focusing on one branch of the argument.

8. Code:
```lean
    · simp [swapMatrix, Ud, Matrix.diagonal_apply, hae, and_comm]
```
This bullet starts a new subgoal produced by the previous tactic. Lean is now focusing on one branch of the argument.

9. Code:
```lean
    · have hea : ¬ e = a := by
```
This line says that a proof script begins here. Everything indented underneath is a sequence of instructions that Lean will check step by step.

10. Code:
```lean
        simpa [eq_comm] using hae
```
This line simplifies the goal using definitions and known equalities. `simpa` means that, after simplification, the desired statement matches a theorem Lean already has.

11. Code:
```lean
      simp [swapMatrix, Ud, Matrix.diagonal_apply, hae, hea, and_comm]
```
This line simplifies the goal using definitions and known equalities. `simpa` means that, after simplification, the desired statement matches a theorem Lean already has.

12. Code:
```lean
  · intro x _ hne
```
This bullet starts a new subgoal produced by the previous tactic. Lean is now focusing on one branch of the argument.

13. Code:
```lean
    have hswap : ¬ (a = x.2 ∧ b = x.1) := by
```
This line says that a proof script begins here. Everything indented underneath is a sequence of instructions that Lean will check step by step.

14. Code:
```lean
      intro hx
```
This line introduces the variable or hypothesis named here into the proof context. In ordinary mathematical prose, it is the same as saying “let” or “assume”.

15. Code:
```lean
      apply hne
```
This line applies an existing theorem to the current goal. Lean then asks the author to prove the theorem’s hypotheses.

16. Code:
```lean
      ext <;> simp [hx.1, hx.2]
```
This line invokes extensionality. To prove two maps or matrices are equal, Lean reduces the problem to checking their values entry by entry.

17. Code:
```lean
    simp [swapMatrix, hswap]
```
This line simplifies the goal using definitions and known equalities. `simpa` means that, after simplification, the desired statement matches a theorem Lean already has.

18. Code:
```lean
  · intro hba
```
This bullet starts a new subgoal produced by the previous tactic. Lean is now focusing on one branch of the argument.

19. Code:
```lean
    simp at hba
```
This line simplifies the goal using definitions and known equalities. `simpa` means that, after simplification, the desired statement matches a theorem Lean already has.

## Mathematical summary

Restated without Lean syntax, `swapMatrix_mul_phase_apply` is the theorem or lemma written above.

- State the desired identity or inequality in Lean’s syntax.
- Introduce temporary names and intermediate claims that organize the argument.
- Use rewriting, simplification, and earlier lemmas to reduce the goal to standard matrix or norm manipulations.
- Close the remaining algebraic or order-theoretic steps with Lean’s proof tactics.

## Dependencies and downstream use

### Earlier declarations this depends on
- [`Ud`](../../Setups/Ud.md) from `Setups.lean`
- [`swapMatrix`](../../PositiveGap/Lemma6/swapMatrix.md) from `PositiveGap/Lemma6.lean`

### Later declarations that use this one
- [`transpose_ad_phiState_eq_swap_mul_phase`](transpose_ad_phiState_eq_swap_mul_phase.md) in `EndMatter/Eq7.lean`
- [`explicit_witness_eq_swap_diagonal`](explicit_witness_eq_swap_diagonal.md) in `EndMatter/Eq7.lean`

## Backlinks

- [Back to `INDEX.md`](../../INDEX.md)
- [Back to the `EndMatter/Eq7.lean` section in the index](../../INDEX.md#diamond-endmatter-eq7-lean)
- [Previous declaration in this file](transpose_phiState_eq_swap.md)
- [Next declaration in this file](transpose_ad_phiState_eq_swap_mul_phase.md)