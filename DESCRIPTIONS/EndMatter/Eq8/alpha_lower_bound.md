# alpha_lower_bound

## Source location

- Original Lean file: `Diamond/EndMatter/Eq8.lean`
- Declaration name: `alpha_lower_bound`
- Declaration kind: `theorem`

## Why this declaration exists

This theorem combines Theorem 1 with Eqs. (7) and (8) to show that no dimension-independent constant smaller than $2/\pi$ can work universally.

 In the file `EndMatter/Eq8.lean`, it contributes to the proof of Eq. (8) and the lower bound on the universal constant. Later proofs call this result by name, so documenting it makes the larger argument readable as a mathematical chain rather than as opaque proof script.

## Original code

```lean
/-- The finite-dimensional bounds from Theorem 1, Eq. (7), and Eq. (8)
    force any dimension-independent constant to be at least `2 / π`. -/
theorem alpha_lower_bound :
    (2 : ℝ) / Real.pi ≤ (1 : ℝ) / Real.sqrt 2 := by
  apply asymptotic_cotangent_lower_bound
  intro d hd
  have hd_gt_one : 1 < d := lt_of_lt_of_le Nat.one_lt_two hd
  letI : Fact (1 < d) := ⟨hd_gt_one⟩
  have hd_pos : 0 < d := lt_trans Nat.zero_lt_one hd_gt_one
  letI : Nonempty (Fin d) := ⟨⟨0, hd_pos⟩⟩
  have hU : (Ud d)ᴴ * Ud d = 1 := ud_conjTranspose_mul_self d
  have hchan : IsQuantumChannel (adMap (Fin d) (Ud d)) :=
    adMap_isQuantumChannel (d := Fin d) (U := Ud d) hU
  have htheta : diamondOp (transposeMap (Fin d)) = (d : ℝ) := by
    rw [lemma_transpose_diamond (d := Fin d)]
    simp [Fintype.card_prod, Nat.cast_mul]
  have hmain :
      2 * Real.cot (Real.pi / (2 * (d : ℝ))) ≤
        (1 / Real.sqrt 2) * (d : ℝ) * 2 := by
    calc
      2 * Real.cot (Real.pi / (2 * (d : ℝ))) ≤ diamondOp (Lambda d) := theorem_eq7 d
      _ ≤ (1 / Real.sqrt 2) * diamondOp (transposeMap (Fin d)) *
            diamondOp (idMinus (adMap (Fin d) (Ud d))) := by
              simpa [Lambda] using theorem1 (d := Fin d) (T := adMap (Fin d) (Ud d)) hchan
      _ = (1 / Real.sqrt 2) * (d : ℝ) * 2 := by
            rw [htheta, theorem_eq8 d]
  have hcot :
      Real.cot (Real.pi / (2 * (d : ℝ))) ≤ (1 / Real.sqrt 2) * (d : ℝ) := by
    nlinarith
  have hd_posR : 0 < (d : ℝ) := by
    exact_mod_cast hd_pos
  exact (div_le_iff₀ hd_posR).2 <| by
    simpa [div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using hcot
```

## Line-by-line explanation

The explanation below follows the declaration one physical line at a time. For long proofs, some lines are tiny bookkeeping steps; those are still explained, but briefly.

1. Code:
```lean
/-- The finite-dimensional bounds from Theorem 1, Eq. (7), and Eq. (8)
```
This is a Lean docstring. It is a human-written comment that tells readers what the declaration is meant to express before the formal code begins.

2. Code:
```lean
    force any dimension-independent constant to be at least `2 / π`. -/
```
This line is one local step in the declaration. It either refines the formula being defined or advances the proof by a small algebraic or logical move.

3. Code:
```lean
theorem alpha_lower_bound :
```
This line starts the `alpha_lower_bound` declaration. Because it begins with `theorem`, Lean now knows what kind of named object is being introduced.

4. Code:
```lean
    (2 : ℝ) / Real.pi ≤ (1 : ℝ) / Real.sqrt 2 := by
```
This line says that a proof script begins here. Everything indented underneath is a sequence of instructions that Lean will check step by step.

5. Code:
```lean
  apply asymptotic_cotangent_lower_bound
```
This line applies an existing theorem to the current goal. Lean then asks the author to prove the theorem’s hypotheses.

6. Code:
```lean
  intro d hd
```
This line introduces the variable or hypothesis named here into the proof context. In ordinary mathematical prose, it is the same as saying “let” or “assume”.

7. Code:
```lean
  have hd_gt_one : 1 < d := lt_of_lt_of_le Nat.one_lt_two hd
```
This line introduces an intermediate claim. The proof pauses to establish a fact that will be used shortly afterwards.

8. Code:
```lean
  letI : Fact (1 < d) := ⟨hd_gt_one⟩
```
This line is one local step in the declaration. It either refines the formula being defined or advances the proof by a small algebraic or logical move.

9. Code:
```lean
  have hd_pos : 0 < d := lt_trans Nat.zero_lt_one hd_gt_one
```
This line introduces an intermediate claim. The proof pauses to establish a fact that will be used shortly afterwards.

10. Code:
```lean
  letI : Nonempty (Fin d) := ⟨⟨0, hd_pos⟩⟩
```
This line is one local step in the declaration. It either refines the formula being defined or advances the proof by a small algebraic or logical move.

11. Code:
```lean
  have hU : (Ud d)ᴴ * Ud d = 1 := ud_conjTranspose_mul_self d
```
This line introduces an intermediate claim. The proof pauses to establish a fact that will be used shortly afterwards.  The superscript `ᴴ` means conjugate transpose (also called the adjoint).

12. Code:
```lean
  have hchan : IsQuantumChannel (adMap (Fin d) (Ud d)) :=
```
This line introduces an intermediate claim. The proof pauses to establish a fact that will be used shortly afterwards.  `Channel d` is an abbreviation for a complex-linear map from operators on `d` to operators on `d`.

13. Code:
```lean
    adMap_isQuantumChannel (d := Fin d) (U := Ud d) hU
```
This line is one local step in the declaration. It either refines the formula being defined or advances the proof by a small algebraic or logical move.  `Channel d` is an abbreviation for a complex-linear map from operators on `d` to operators on `d`.

14. Code:
```lean
  have htheta : diamondOp (transposeMap (Fin d)) = (d : ℝ) := by
```
This line says that a proof script begins here. Everything indented underneath is a sequence of instructions that Lean will check step by step.

15. Code:
```lean
    rw [lemma_transpose_diamond (d := Fin d)]
```
This line uses rewriting. Lean replaces one expression by an equal expression using the lemmas listed in brackets.

16. Code:
```lean
    simp [Fintype.card_prod, Nat.cast_mul]
```
This line simplifies the goal using definitions and known equalities. `simpa` means that, after simplification, the desired statement matches a theorem Lean already has.  A bracket such as `[Fintype d]` tells Lean that the index set `d` is finite, so sums over all indices make sense.  `Fintype.card` is the size of a finite index set.

17. Code:
```lean
  have hmain :
```
This line introduces an intermediate claim. The proof pauses to establish a fact that will be used shortly afterwards.

18. Code:
```lean
      2 * Real.cot (Real.pi / (2 * (d : ℝ))) ≤
```
This line is one local step in the declaration. It either refines the formula being defined or advances the proof by a small algebraic or logical move.

19. Code:
```lean
        (1 / Real.sqrt 2) * (d : ℝ) * 2 := by
```
This line says that a proof script begins here. Everything indented underneath is a sequence of instructions that Lean will check step by step.

20. Code:
```lean
    calc
```
This line begins a chained calculation. Each displayed step that follows must be justified by the indented proof after `:= by`.

21. Code:
```lean
      2 * Real.cot (Real.pi / (2 * (d : ℝ))) ≤ diamondOp (Lambda d) := theorem_eq7 d
```
This line is one local step in the declaration. It either refines the formula being defined or advances the proof by a small algebraic or logical move.

22. Code:
```lean
      _ ≤ (1 / Real.sqrt 2) * diamondOp (transposeMap (Fin d)) *
```
This line is one step inside a `calc` block. Lean is checking that the new expression really follows from the previous one.

23. Code:
```lean
            diamondOp (idMinus (adMap (Fin d) (Ud d))) := by
```
This line says that a proof script begins here. Everything indented underneath is a sequence of instructions that Lean will check step by step.

24. Code:
```lean
              simpa [Lambda] using theorem1 (d := Fin d) (T := adMap (Fin d) (Ud d)) hchan
```
This line simplifies the goal using definitions and known equalities. `simpa` means that, after simplification, the desired statement matches a theorem Lean already has.

25. Code:
```lean
      _ = (1 / Real.sqrt 2) * (d : ℝ) * 2 := by
```
This line says that a proof script begins here. Everything indented underneath is a sequence of instructions that Lean will check step by step.

26. Code:
```lean
            rw [htheta, theorem_eq8 d]
```
This line uses rewriting. Lean replaces one expression by an equal expression using the lemmas listed in brackets.

27. Code:
```lean
  have hcot :
```
This line introduces an intermediate claim. The proof pauses to establish a fact that will be used shortly afterwards.

28. Code:
```lean
      Real.cot (Real.pi / (2 * (d : ℝ))) ≤ (1 / Real.sqrt 2) * (d : ℝ) := by
```
This line says that a proof script begins here. Everything indented underneath is a sequence of instructions that Lean will check step by step.

29. Code:
```lean
    nlinarith
```
This line solves the current numerical inequality by combining the equalities and inequalities already available in the context.

30. Code:
```lean
  have hd_posR : 0 < (d : ℝ) := by
```
This line says that a proof script begins here. Everything indented underneath is a sequence of instructions that Lean will check step by step.

31. Code:
```lean
    exact_mod_cast hd_pos
```
This line finishes the current goal by giving Lean the exact theorem, lemma, or term that proves it.

32. Code:
```lean
  exact (div_le_iff₀ hd_posR).2 <| by
```
This line finishes the current goal by giving Lean the exact theorem, lemma, or term that proves it.

33. Code:
```lean
    simpa [div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using hcot
```
This line simplifies the goal using definitions and known equalities. `simpa` means that, after simplification, the desired statement matches a theorem Lean already has.

## Mathematical summary

Restated without Lean syntax, `alpha_lower_bound` is the theorem or lemma written above.

- Apply Theorem 1 to the special unitary channel `adMap (Fin d) (Ud d)`.
- Insert the explicit lower bound from Eq. (7) and the exact distance from Eq. (8).
- Rearrange the resulting inequality into a bound on $\cot(\pi/(2d))/d$.
- Use the asymptotic cotangent lower-bound axiom to pass to the universal constant $2/\pi$.

## Dependencies and downstream use

### Earlier declarations this depends on
- [`IsQuantumChannel`](../../Setups/IsQuantumChannel.md) from `Setups.lean`
- [`transposeMap`](../../Setups/transposeMap.md) from `Setups.lean`
- [`diamondOp`](../../Setups/diamondOp.md) from `Setups.lean`
- [`idMinus`](../../Setups/idMinus.md) from `Setups.lean`
- [`adMap`](../../Setups/adMap.md) from `Setups.lean`
- [`Ud`](../../Setups/Ud.md) from `Setups.lean`
- [`Lambda`](../../Setups/Lambda.md) from `Setups.lean`
- [`adMap_isQuantumChannel`](../../StandardFacts/adMap_isQuantumChannel.md) from `StandardFacts.lean`
- [`lemma_transpose_diamond`](../../StandardFacts/lemma_transpose_diamond.md) from `StandardFacts.lean`
- [`asymptotic_cotangent_lower_bound`](../../StandardFacts/asymptotic_cotangent_lower_bound.md) from `StandardFacts.lean`
- [`theorem1`](../../Theorem/Theorem1/theorem1.md) from `Theorem/Theorem1.lean`
- [`ud_conjTranspose_mul_self`](../Eq7/ud_conjTranspose_mul_self.md) from `EndMatter/Eq7.lean`
- [`theorem_eq7`](../Eq7/theorem_eq7.md) from `EndMatter/Eq7.lean`
- [`theorem_eq8`](theorem_eq8.md) from `EndMatter/Eq8.lean`

### Later declarations that use this one
- No later documented declaration mentions this name explicitly.

## Backlinks

- [Back to `INDEX.md`](../../INDEX.md)
- [Back to the `EndMatter/Eq8.lean` section in the index](../../INDEX.md#diamond-endmatter-eq8-lean)
- [Previous declaration in this file](theorem_eq8.md)