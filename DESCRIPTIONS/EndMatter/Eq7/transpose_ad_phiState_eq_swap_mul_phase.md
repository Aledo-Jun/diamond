# transpose_ad_phiState_eq_swap_mul_phase

## Source location

- Original Lean file: `Diamond/EndMatter/Eq7.lean`
- Declaration name: `transpose_ad_phiState_eq_swap_mul_phase`
- Declaration kind: `theorem`

## Why this declaration exists

Explicit formula for `((Θ ∘ Ad_U) ⊗ id) (Φ_d)`.

 In the file `EndMatter/Eq7.lean`, it contributes to the explicit witness construction used to prove the lower bound labelled Eq. (7). Later proofs call this result by name, so documenting it makes the larger argument readable as a mathematical chain rather than as opaque proof script.

## Original code

```lean
/-- Explicit formula for `((Θ ∘ Ad_U) ⊗ id) (Φ_d)`. -/
theorem transpose_ad_phiState_eq_swap_mul_phase (d : ℕ) [Fact (1 < d)] :
    tensorWithIdentity
        (Fin d)
        (Fin d)
        ((transposeMap (Fin d)).comp (adMap (Fin d) (Ud d)))
        (phiState d) =
      (d : ℂ)⁻¹ • (swapMatrix d * ((Ud d)ᵀ ⊗ₖ star (Ud d))) := by
  ext i j
  rcases i with ⟨a, b⟩
  rcases j with ⟨c, e⟩
  have hEntry :
      tensorWithIdentity
          (Fin d)
          (Fin d)
          ((transposeMap (Fin d)).comp (adMap (Fin d) (Ud d)))
          (phiState d)
          (a, b)
          (c, e) =
        if b = c ∧ a = e then
          (d : ℂ)⁻¹ * Ud d b b * star (Ud d e e)
        else 0 := by
      by_cases h : b = c ∧ a = e
      · rcases h with ⟨hbc, hae⟩
        simp [tensorWithIdentity, transposeMap, adMap, LinearMap.comp_apply, Matrix.mul_apply,
          phiState_apply, Ud, Matrix.diagonal_apply, hbc, hae, mul_comm, mul_left_comm,
          mul_assoc]
      · have hcases : ¬ c = b ∨ ¬ a = e := by
          by_cases hcb : c = b
          · right
            intro hae
            apply h
            exact ⟨hcb.symm, hae⟩
          · left
            exact hcb
        rcases hcases with hcb | hae
        · have hbc : ¬ b = c := by
            simpa [eq_comm] using hcb
          simp [tensorWithIdentity, transposeMap, adMap, LinearMap.comp_apply,
            Matrix.mul_apply, phiState_apply, Ud, Matrix.diagonal_apply, hcb, hbc]
        · have hea : ¬ e = a := by
            simpa [eq_comm] using hae
          simp [tensorWithIdentity, transposeMap, adMap, LinearMap.comp_apply,
            Matrix.mul_apply, phiState_apply, Ud, Matrix.diagonal_apply, hae]
  calc
    tensorWithIdentity
        (Fin d)
        (Fin d)
        ((transposeMap (Fin d)).comp (adMap (Fin d) (Ud d)))
        (phiState d)
        (a, b)
        (c, e)
      = if b = c ∧ a = e then
          (d : ℂ)⁻¹ * Ud d b b * star (Ud d e e)
        else 0 := hEntry
    _ = ((d : ℂ)⁻¹ • (swapMatrix d * ((Ud d)ᵀ ⊗ₖ star (Ud d)))) (a, b) (c, e) := by
      simp [swapMatrix_mul_phase_apply, and_comm, mul_assoc]
```

## Line-by-line explanation

The explanation below follows the declaration one physical line at a time. For long proofs, some lines are tiny bookkeeping steps; those are still explained, but briefly.

1. Code:
```lean
/-- Explicit formula for `((Θ ∘ Ad_U) ⊗ id) (Φ_d)`. -/
```
This is a Lean docstring. It is a human-written comment that tells readers what the declaration is meant to express before the formal code begins.

2. Code:
```lean
theorem transpose_ad_phiState_eq_swap_mul_phase (d : ℕ) [Fact (1 < d)] :
```
This line starts the `transpose_ad_phiState_eq_swap_mul_phase` declaration. Because it begins with `theorem`, Lean now knows what kind of named object is being introduced.

3. Code:
```lean
    tensorWithIdentity
```
This line is one local step in the declaration. It either refines the formula being defined or advances the proof by a small algebraic or logical move.

4. Code:
```lean
        (Fin d)
```
This line is one local step in the declaration. It either refines the formula being defined or advances the proof by a small algebraic or logical move.

5. Code:
```lean
        (Fin d)
```
This line is one local step in the declaration. It either refines the formula being defined or advances the proof by a small algebraic or logical move.

6. Code:
```lean
        ((transposeMap (Fin d)).comp (adMap (Fin d) (Ud d)))
```
This line is one local step in the declaration. It either refines the formula being defined or advances the proof by a small algebraic or logical move.  `comp` means composition of maps: one map is applied after another.

7. Code:
```lean
        (phiState d) =
```
This line is one local step in the declaration. It either refines the formula being defined or advances the proof by a small algebraic or logical move.

8. Code:
```lean
      (d : ℂ)⁻¹ • (swapMatrix d * ((Ud d)ᵀ ⊗ₖ star (Ud d))) := by
```
This line says that a proof script begins here. Everything indented underneath is a sequence of instructions that Lean will check step by step.  `Matrix d d ℂ` means a square matrix with complex entries; the index type `d` tells Lean which rows and columns exist.  The symbol `⊗ₖ` is the Kronecker (tensor) product of matrices.  The superscript `ᵀ` means ordinary transpose.

9. Code:
```lean
  ext i j
```
This line invokes extensionality. To prove two maps or matrices are equal, Lean reduces the problem to checking their values entry by entry.

10. Code:
```lean
  rcases i with ⟨a, b⟩
```
This line is one local step in the declaration. It either refines the formula being defined or advances the proof by a small algebraic or logical move.

11. Code:
```lean
  rcases j with ⟨c, e⟩
```
This line is one local step in the declaration. It either refines the formula being defined or advances the proof by a small algebraic or logical move.

12. Code:
```lean
  have hEntry :
```
This line introduces an intermediate claim. The proof pauses to establish a fact that will be used shortly afterwards.

13. Code:
```lean
      tensorWithIdentity
```
This line is one local step in the declaration. It either refines the formula being defined or advances the proof by a small algebraic or logical move.

14. Code:
```lean
          (Fin d)
```
This line is one local step in the declaration. It either refines the formula being defined or advances the proof by a small algebraic or logical move.

15. Code:
```lean
          (Fin d)
```
This line is one local step in the declaration. It either refines the formula being defined or advances the proof by a small algebraic or logical move.

16. Code:
```lean
          ((transposeMap (Fin d)).comp (adMap (Fin d) (Ud d)))
```
This line is one local step in the declaration. It either refines the formula being defined or advances the proof by a small algebraic or logical move.  `comp` means composition of maps: one map is applied after another.

17. Code:
```lean
          (phiState d)
```
This line is one local step in the declaration. It either refines the formula being defined or advances the proof by a small algebraic or logical move.

18. Code:
```lean
          (a, b)
```
This line is one local step in the declaration. It either refines the formula being defined or advances the proof by a small algebraic or logical move.

19. Code:
```lean
          (c, e) =
```
This line is one local step in the declaration. It either refines the formula being defined or advances the proof by a small algebraic or logical move.

20. Code:
```lean
        if b = c ∧ a = e then
```
This line is one local step in the declaration. It either refines the formula being defined or advances the proof by a small algebraic or logical move.

21. Code:
```lean
          (d : ℂ)⁻¹ * Ud d b b * star (Ud d e e)
```
This line is one local step in the declaration. It either refines the formula being defined or advances the proof by a small algebraic or logical move.

22. Code:
```lean
        else 0 := by
```
This line says that a proof script begins here. Everything indented underneath is a sequence of instructions that Lean will check step by step.

23. Code:
```lean
      by_cases h : b = c ∧ a = e
```
This line splits the proof into cases according to whether the named proposition is true or false.

24. Code:
```lean
      · rcases h with ⟨hbc, hae⟩
```
This bullet starts a new subgoal produced by the previous tactic. Lean is now focusing on one branch of the argument.

25. Code:
```lean
        simp [tensorWithIdentity, transposeMap, adMap, LinearMap.comp_apply, Matrix.mul_apply,
```
This line simplifies the goal using definitions and known equalities. `simpa` means that, after simplification, the desired statement matches a theorem Lean already has.  `comp` means composition of maps: one map is applied after another.  `LinearMap.comp` is composition of linear maps.

26. Code:
```lean
          phiState_apply, Ud, Matrix.diagonal_apply, hbc, hae, mul_comm, mul_left_comm,
```
This line is one local step in the declaration. It either refines the formula being defined or advances the proof by a small algebraic or logical move.

27. Code:
```lean
          mul_assoc]
```
This line is one local step in the declaration. It either refines the formula being defined or advances the proof by a small algebraic or logical move.

28. Code:
```lean
      · have hcases : ¬ c = b ∨ ¬ a = e := by
```
This line says that a proof script begins here. Everything indented underneath is a sequence of instructions that Lean will check step by step.

29. Code:
```lean
          by_cases hcb : c = b
```
This line splits the proof into cases according to whether the named proposition is true or false.

30. Code:
```lean
          · right
```
This bullet starts a new subgoal produced by the previous tactic. Lean is now focusing on one branch of the argument.

31. Code:
```lean
            intro hae
```
This line introduces the variable or hypothesis named here into the proof context. In ordinary mathematical prose, it is the same as saying “let” or “assume”.

32. Code:
```lean
            apply h
```
This line applies an existing theorem to the current goal. Lean then asks the author to prove the theorem’s hypotheses.

33. Code:
```lean
            exact ⟨hcb.symm, hae⟩
```
This line finishes the current goal by giving Lean the exact theorem, lemma, or term that proves it.

34. Code:
```lean
          · left
```
This bullet starts a new subgoal produced by the previous tactic. Lean is now focusing on one branch of the argument.

35. Code:
```lean
            exact hcb
```
This line finishes the current goal by giving Lean the exact theorem, lemma, or term that proves it.

36. Code:
```lean
        rcases hcases with hcb | hae
```
This line is one local step in the declaration. It either refines the formula being defined or advances the proof by a small algebraic or logical move.

37. Code:
```lean
        · have hbc : ¬ b = c := by
```
This line says that a proof script begins here. Everything indented underneath is a sequence of instructions that Lean will check step by step.

38. Code:
```lean
            simpa [eq_comm] using hcb
```
This line simplifies the goal using definitions and known equalities. `simpa` means that, after simplification, the desired statement matches a theorem Lean already has.

39. Code:
```lean
          simp [tensorWithIdentity, transposeMap, adMap, LinearMap.comp_apply,
```
This line simplifies the goal using definitions and known equalities. `simpa` means that, after simplification, the desired statement matches a theorem Lean already has.  `comp` means composition of maps: one map is applied after another.  `LinearMap.comp` is composition of linear maps.

40. Code:
```lean
            Matrix.mul_apply, phiState_apply, Ud, Matrix.diagonal_apply, hcb, hbc]
```
This line is one local step in the declaration. It either refines the formula being defined or advances the proof by a small algebraic or logical move.

41. Code:
```lean
        · have hea : ¬ e = a := by
```
This line says that a proof script begins here. Everything indented underneath is a sequence of instructions that Lean will check step by step.

42. Code:
```lean
            simpa [eq_comm] using hae
```
This line simplifies the goal using definitions and known equalities. `simpa` means that, after simplification, the desired statement matches a theorem Lean already has.

43. Code:
```lean
          simp [tensorWithIdentity, transposeMap, adMap, LinearMap.comp_apply,
```
This line simplifies the goal using definitions and known equalities. `simpa` means that, after simplification, the desired statement matches a theorem Lean already has.  `comp` means composition of maps: one map is applied after another.  `LinearMap.comp` is composition of linear maps.

44. Code:
```lean
            Matrix.mul_apply, phiState_apply, Ud, Matrix.diagonal_apply, hae]
```
This line is one local step in the declaration. It either refines the formula being defined or advances the proof by a small algebraic or logical move.

45. Code:
```lean
  calc
```
This line begins a chained calculation. Each displayed step that follows must be justified by the indented proof after `:= by`.

46. Code:
```lean
    tensorWithIdentity
```
This line is one local step in the declaration. It either refines the formula being defined or advances the proof by a small algebraic or logical move.

47. Code:
```lean
        (Fin d)
```
This line is one local step in the declaration. It either refines the formula being defined or advances the proof by a small algebraic or logical move.

48. Code:
```lean
        (Fin d)
```
This line is one local step in the declaration. It either refines the formula being defined or advances the proof by a small algebraic or logical move.

49. Code:
```lean
        ((transposeMap (Fin d)).comp (adMap (Fin d) (Ud d)))
```
This line is one local step in the declaration. It either refines the formula being defined or advances the proof by a small algebraic or logical move.  `comp` means composition of maps: one map is applied after another.

50. Code:
```lean
        (phiState d)
```
This line is one local step in the declaration. It either refines the formula being defined or advances the proof by a small algebraic or logical move.

51. Code:
```lean
        (a, b)
```
This line is one local step in the declaration. It either refines the formula being defined or advances the proof by a small algebraic or logical move.

52. Code:
```lean
        (c, e)
```
This line is one local step in the declaration. It either refines the formula being defined or advances the proof by a small algebraic or logical move.

53. Code:
```lean
      = if b = c ∧ a = e then
```
This line is one local step in the declaration. It either refines the formula being defined or advances the proof by a small algebraic or logical move.

54. Code:
```lean
          (d : ℂ)⁻¹ * Ud d b b * star (Ud d e e)
```
This line is one local step in the declaration. It either refines the formula being defined or advances the proof by a small algebraic or logical move.

55. Code:
```lean
        else 0 := hEntry
```
This line is one local step in the declaration. It either refines the formula being defined or advances the proof by a small algebraic or logical move.

56. Code:
```lean
    _ = ((d : ℂ)⁻¹ • (swapMatrix d * ((Ud d)ᵀ ⊗ₖ star (Ud d)))) (a, b) (c, e) := by
```
This line says that a proof script begins here. Everything indented underneath is a sequence of instructions that Lean will check step by step.  `Matrix d d ℂ` means a square matrix with complex entries; the index type `d` tells Lean which rows and columns exist.  The symbol `⊗ₖ` is the Kronecker (tensor) product of matrices.  The superscript `ᵀ` means ordinary transpose.

57. Code:
```lean
      simp [swapMatrix_mul_phase_apply, and_comm, mul_assoc]
```
This line simplifies the goal using definitions and known equalities. `simpa` means that, after simplification, the desired statement matches a theorem Lean already has.

## Mathematical summary

Restated without Lean syntax, `transpose_ad_phiState_eq_swap_mul_phase` is the theorem or lemma written above.

- State the desired identity or inequality in Lean’s syntax.
- Introduce temporary names and intermediate claims that organize the argument.
- Use rewriting, simplification, and earlier lemmas to reduce the goal to standard matrix or norm manipulations.
- Close the remaining algebraic or order-theoretic steps with Lean’s proof tactics.

## Dependencies and downstream use

### Earlier declarations this depends on
- [`transposeMap`](../../Setups/transposeMap.md) from `Setups.lean`
- [`tensorWithIdentity`](../../Setups/tensorWithIdentity.md) from `Setups.lean`
- [`adMap`](../../Setups/adMap.md) from `Setups.lean`
- [`Ud`](../../Setups/Ud.md) from `Setups.lean`
- [`swapMatrix`](../../PositiveGap/Lemma6/swapMatrix.md) from `PositiveGap/Lemma6.lean`
- [`phiState`](phiState.md) from `EndMatter/Eq7.lean`
- [`phiState_apply`](phiState_apply.md) from `EndMatter/Eq7.lean`
- [`swapMatrix_mul_phase_apply`](swapMatrix_mul_phase_apply.md) from `EndMatter/Eq7.lean`

### Later declarations that use this one
- [`lambda_phiState_eq`](lambda_phiState_eq.md) in `EndMatter/Eq7.lean`

## Backlinks

- [Back to `INDEX.md`](../../INDEX.md)
- [Back to the `EndMatter/Eq7.lean` section in the index](../../INDEX.md#diamond-endmatter-eq7-lean)
- [Previous declaration in this file](swapMatrix_mul_phase_apply.md)
- [Next declaration in this file](lambda_phiState_eq.md)