# lemma1_eq_imp_rank_two

## Source location

- Original Lean file: `Diamond/PositiveGap/NotTight.lean`
- Declaration name: `lemma1_eq_imp_rank_two`
- Declaration kind: `theorem`

## Why this declaration exists

This theorem identifies the equality case of Lemma 1: saturation forces rank two.

 In the file `PositiveGap/NotTight.lean`, it contributes to the finite-dimensional non-tightness argument and the equality-case analysis behind it. Later proofs call this result by name, so documenting it makes the larger argument readable as a mathematical chain rather than as opaque proof script.

## Original code

```lean
/-- Equality case of paper Lemma 1:
    a nonzero traceless Hermitian matrix saturating Lemma 1 has rank `2`. -/
theorem lemma1_eq_imp_rank_two
    {d : Type u} [Fintype d] [DecidableEq d]
    {X : Matrix (d × d) (d × d) ℂ}
    (hXh : Matrix.IsHermitian X) (htr : Matrix.trace X = 0) (hX0 : X ≠ 0)
    (heq : hsNormOp X = (1 / Real.sqrt 2) * traceNormOp X) :
    Matrix.rank X = 2 := by
  let p : d × d → ℝ := fun i => max (hXh.eigenvalues i) 0
  let q : d × d → ℝ := fun i => max (-hXh.eigenvalues i) 0
  have hp_nonneg : ∀ i, 0 ≤ p i := by
    intro i
    simp [p]
  have hq_nonneg : ∀ i, 0 ≤ q i := by
    intro i
    simp [q]
  have habs : ∀ i, |hXh.eigenvalues i| = p i + q i := by
    intro i
    by_cases hi : 0 ≤ hXh.eigenvalues i
    · simp [p, q, hi, abs_of_nonneg hi]
    · have hi' : hXh.eigenvalues i < 0 := lt_of_not_ge hi
      simp [p, q, hi'.le, abs_of_neg hi']
  have hsub : ∀ i, hXh.eigenvalues i = p i - q i := by
    intro i
    by_cases hi : 0 ≤ hXh.eigenvalues i
    · simp [p, q, hi]
    · have hi' : hXh.eigenvalues i < 0 := lt_of_not_ge hi
      simp [p, q, hi'.le]
  have hsq : ∀ i, (hXh.eigenvalues i) ^ 2 = (p i) ^ 2 + (q i) ^ 2 := by
    intro i
    by_cases hi : 0 ≤ hXh.eigenvalues i
    · simp [p, q, hi, pow_two]
    · have hi' : hXh.eigenvalues i < 0 := lt_of_not_ge hi
      simp [p, q, hi'.le, pow_two]
  have hsum_zero : ∑ i, hXh.eigenvalues i = 0 := by
    have htraceC : (∑ i, ((hXh.eigenvalues i : ℝ) : ℂ)) = 0 := by
      simpa [hXh.trace_eq_sum_eigenvalues] using htr
    exact_mod_cast congrArg Complex.re htraceC
  have hpq : ∑ i, p i = ∑ i, q i := by
    have hsum_sub : ∑ i, (p i - q i) = 0 := by
      simpa [hsub] using hsum_zero
    rw [Finset.sum_sub_distrib] at hsum_sub
    linarith
  have htraceNorm : traceNormOp X = 2 * ∑ i, p i := by
    calc
      traceNormOp X = ∑ i, |hXh.eigenvalues i| := by
        simpa using traceNormOp_hermitian_eq_sum_abs_eigenvalues hXh
      _ = ∑ i, (p i + q i) := by
        simp [habs]
      _ = ∑ i, p i + ∑ i, q i := by
        rw [Finset.sum_add_distrib]
      _ = 2 * ∑ i, p i := by
        rw [hpq]
        ring
  have hhsNormSq : hsNormOp X ^ 2 = ∑ i, (hXh.eigenvalues i) ^ 2 := by
    rw [hsNorm_sq_eq_re_trace_conjTranspose_mul_self,
      hermitian_re_trace_conjTranspose_mul_self_eq_sum_sq_eigenvalues hXh]
  have hmain_eq : ∑ i, (hXh.eigenvalues i) ^ 2 = 2 * (∑ i, p i) ^ 2 := by
    have hsqrt2_ne : Real.sqrt 2 ≠ 0 := by
      positivity
    have hsqeq : hsNormOp X ^ 2 = ((1 / Real.sqrt 2) * traceNormOp X) ^ 2 := by
      exact congrArg (fun t : ℝ => t ^ 2) heq
    rw [hhsNormSq, htraceNorm] at hsqeq
    have hrhs : ((1 / Real.sqrt 2) * (2 * ∑ i, p i)) ^ 2 = 2 * (∑ i, p i) ^ 2 := by
      field_simp [pow_two, hsqrt2_ne]
      nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 2 by positivity)]
    rw [hrhs] at hsqeq
    exact hsqeq
  have hp_eq : (∑ i, (p i) ^ 2) = (∑ i, p i) ^ 2 := by
    have hp_le : ∑ i, (p i) ^ 2 ≤ (∑ i, p i) ^ 2 :=
      Finset.sum_sq_le_sq_sum_of_nonneg (fun i _ => hp_nonneg i)
    have hq_le : ∑ i, (q i) ^ 2 ≤ (∑ i, q i) ^ 2 :=
      Finset.sum_sq_le_sq_sum_of_nonneg (fun i _ => hq_nonneg i)
    have hq_le' : ∑ i, (q i) ^ 2 ≤ (∑ i, p i) ^ 2 := by
      simpa [hpq] using hq_le
    have haux : ∑ i, (p i) ^ 2 + ∑ i, (q i) ^ 2 = 2 * (∑ i, p i) ^ 2 := by
      calc
        ∑ i, (p i) ^ 2 + ∑ i, (q i) ^ 2 = ∑ i, (hXh.eigenvalues i) ^ 2 := by
          symm
          simp [hsq, Finset.sum_add_distrib]
        _ = 2 * (∑ i, p i) ^ 2 := hmain_eq
    nlinarith
  have hq_eq : (∑ i, (q i) ^ 2) = (∑ i, q i) ^ 2 := by
    have hp_le : ∑ i, (p i) ^ 2 ≤ (∑ i, p i) ^ 2 :=
      Finset.sum_sq_le_sq_sum_of_nonneg (fun i _ => hp_nonneg i)
    have hp_le' : ∑ i, (p i) ^ 2 ≤ (∑ i, q i) ^ 2 := by
      simpa [hpq] using hp_le
    have hq_le : ∑ i, (q i) ^ 2 ≤ (∑ i, q i) ^ 2 :=
      Finset.sum_sq_le_sq_sum_of_nonneg (fun i _ => hq_nonneg i)
    have haux : ∑ i, (p i) ^ 2 + ∑ i, (q i) ^ 2 = 2 * (∑ i, q i) ^ 2 := by
      calc
        ∑ i, (p i) ^ 2 + ∑ i, (q i) ^ 2 = ∑ i, (hXh.eigenvalues i) ^ 2 := by
          symm
          simp [hsq, Finset.sum_add_distrib]
        _ = 2 * (∑ i, p i) ^ 2 := hmain_eq
        _ = 2 * (∑ i, q i) ^ 2 := by
          rw [hpq]
    nlinarith
  have hp_pair : ∀ i j, i ≠ j → p i = 0 ∨ p j = 0 :=
    pairwise_zero_of_sum_sq_eq_sq_sum hp_nonneg hp_eq
  have hq_pair : ∀ i j, i ≠ j → q i = 0 ∨ q j = 0 :=
    pairwise_zero_of_sum_sq_eq_sq_sum hq_nonneg hq_eq
  have hsum_p_ne : ∑ i, p i ≠ 0 := by
    intro hp0
    have hsum_abs0 : ∑ i, |hXh.eigenvalues i| = 0 := by
      rw [← traceNormOp_hermitian_eq_sum_abs_eigenvalues hXh, htraceNorm, hp0]
      ring
    have habs0 : ∀ i, |hXh.eigenvalues i| = 0 := by
      intro i
      exact
        (Finset.sum_eq_zero_iff_of_nonneg (fun j hj => abs_nonneg _)).1 hsum_abs0 i (by simp)
    have heig0 : hXh.eigenvalues = 0 := by
      funext i
      exact abs_eq_zero.mp (habs0 i)
    exact hX0 ((Matrix.IsHermitian.eigenvalues_eq_zero_iff hXh).1 heig0)
  have hsum_q_ne : ∑ i, q i ≠ 0 := by
    rw [← hpq]
    exact hsum_p_ne
  obtain ⟨iPos, hiPos, hiPos_unique⟩ :=
    existsUnique_nonzero_of_pairwise_zero
      (by
        rcases Finset.exists_ne_zero_of_sum_ne_zero hsum_p_ne with ⟨i, _, hi⟩
        exact ⟨i, hi⟩) hp_pair
  obtain ⟨iNeg, hiNeg, hiNeg_unique⟩ :=
    existsUnique_nonzero_of_pairwise_zero
      (by
        rcases Finset.exists_ne_zero_of_sum_ne_zero hsum_q_ne with ⟨i, _, hi⟩
        exact ⟨i, hi⟩) hq_pair
  have hPos_eig_nonzero : hXh.eigenvalues iPos ≠ 0 := by
    by_cases hnonneg : 0 ≤ hXh.eigenvalues iPos
    · have hpval : p iPos = hXh.eigenvalues iPos := by
        simp [p, hnonneg]
      exact hpval ▸ hiPos
    · have hneg : hXh.eigenvalues iPos < 0 := lt_of_not_ge hnonneg
      have hpzero : p iPos = 0 := by
        simp [p, hneg.le]
      exact (hiPos hpzero).elim
  have hNeg_eig_nonzero : hXh.eigenvalues iNeg ≠ 0 := by
    by_cases hnonneg : 0 ≤ hXh.eigenvalues iNeg
    · have hqzero : q iNeg = 0 := by
        simp [q, hnonneg]
      exact (hiNeg hqzero).elim
    · have hneg : hXh.eigenvalues iNeg < 0 := lt_of_not_ge hnonneg
      have hqval : q iNeg = -hXh.eigenvalues iNeg := by
        simp [q, hneg.le]
      intro heig
      apply hiNeg
      simp [hqval, heig]
  have hij : iPos ≠ iNeg := by
    intro hijEq
    subst iNeg
    by_cases hnonneg : 0 ≤ hXh.eigenvalues iPos
    · have hqzero : q iPos = 0 := by
        simp [q, hnonneg]
      exact hiNeg hqzero
    · have hneg : hXh.eigenvalues iPos < 0 := lt_of_not_ge hnonneg
      have hpzero : p iPos = 0 := by
        simp [p, hneg.le]
      exact hiPos hpzero
  have hsupport : ∀ i, hXh.eigenvalues i ≠ 0 → i = iPos ∨ i = iNeg := by
    intro i hi
    by_cases hnonneg : 0 ≤ hXh.eigenvalues i
    · left
      have hp_i : p i ≠ 0 := by
        have hpval : p i = hXh.eigenvalues i := by
          simp [p, hnonneg]
        exact hpval ▸ hi
      exact hiPos_unique i hp_i
    · right
      have hneg : hXh.eigenvalues i < 0 := lt_of_not_ge hnonneg
      have hq_i : q i ≠ 0 := by
        have hqval : q i = -hXh.eigenvalues i := by
          simp [q, hneg.le]
        rw [hqval]
        exact neg_ne_zero.mpr hi
      exact hiNeg_unique i hq_i
  have hle : Fintype.card {i : d × d // hXh.eigenvalues i ≠ 0} ≤ 2 := by
    classical
    let f : {i : d × d // hXh.eigenvalues i ≠ 0} → {i : d × d // i = iPos ∨ i = iNeg} :=
      fun i => ⟨i.1, hsupport i.1 i.2⟩
    have hf : Function.Injective f := by
      intro a b h
      apply Subtype.ext
      simpa using congrArg (fun z => z.1) h
    have hcard := Fintype.card_le_of_injective f hf
    simpa [Fintype.card_subtype_eq_or_eq_of_ne hij] using hcard
  have hge : 2 ≤ Fintype.card {i : d × d // hXh.eigenvalues i ≠ 0} := by
    classical
    let g : Bool → {i : d × d // hXh.eigenvalues i ≠ 0} :=
      fun b => cond b ⟨iPos, hPos_eig_nonzero⟩ ⟨iNeg, hNeg_eig_nonzero⟩
    have hg : Function.Injective g := by
      intro a b h
      cases a <;> cases b
      · rfl
      · have h' : iNeg = iPos := by simpa [g] using h
        exact (hij h'.symm).elim
      · have h' : iPos = iNeg := by simpa [g] using h
        exact (hij h').elim
      · rfl
    have hcard := Fintype.card_le_of_injective g hg
    simpa using hcard
  have hcard : Fintype.card {i : d × d // hXh.eigenvalues i ≠ 0} = 2 := by
    omega
  rw [hXh.rank_eq_card_non_zero_eigs, hcard]
```

## Block-by-block explanation

The explanation below follows the declaration block by block. Each block groups a coherent piece of the definition or proof, so the mathematical structure is easier to see than in a strictly line-oriented reading.

1. Code:
```lean
/-- Equality case of paper Lemma 1:
```
This is a Lean docstring. It is a human-written comment that tells readers what the declaration is meant to express before the formal code begins.

2. Code:
```lean
    a nonzero traceless Hermitian matrix saturating Lemma 1 has rank `2`. -/
```
This line is one local step in the declaration. It either refines the formula being defined or advances the proof by a small algebraic or logical move.

3. Code:
```lean
theorem lemma1_eq_imp_rank_two
```
This line starts the `lemma1_eq_imp_rank_two` declaration. Because it begins with `theorem`, Lean now knows what kind of named object is being introduced.

4. Code:
```lean
    {d : Type u} [Fintype d] [DecidableEq d]
```
This line is one local step in the declaration. It either refines the formula being defined or advances the proof by a small algebraic or logical move.  A bracket such as `[Fintype d]` tells Lean that the index set `d` is finite, so sums over all indices make sense.  A bracket such as `[DecidableEq d]` tells Lean that it can decide whether two indices are equal.

5. Code:
```lean
    {X : Matrix (d × d) (d × d) ℂ}
```
This line is one local step in the declaration. It either refines the formula being defined or advances the proof by a small algebraic or logical move.  `Matrix d d ℂ` means a square matrix with complex entries; the index type `d` tells Lean which rows and columns exist.

6. Code:
```lean
    (hXh : Matrix.IsHermitian X) (htr : Matrix.trace X = 0) (hX0 : X ≠ 0)
```
This line is one local step in the declaration. It either refines the formula being defined or advances the proof by a small algebraic or logical move.

7. Code:
```lean
    (heq : hsNormOp X = (1 / Real.sqrt 2) * traceNormOp X) :
```
This line is one local step in the declaration. It either refines the formula being defined or advances the proof by a small algebraic or logical move.

8. Code:
```lean
    Matrix.rank X = 2 := by
```
This line says that a proof script begins here. Everything indented underneath is a sequence of instructions that Lean will check step by step.

9. Code:
```lean
  let p : d × d → ℝ := fun i => max (hXh.eigenvalues i) 0
```
This line gives a temporary name to an expression. Doing that makes later lines shorter and easier to read.

10. Code:
```lean
  let q : d × d → ℝ := fun i => max (-hXh.eigenvalues i) 0
```
This line gives a temporary name to an expression. Doing that makes later lines shorter and easier to read.

11. Code:
```lean
  have hp_nonneg : ∀ i, 0 ≤ p i := by
```
This line says that a proof script begins here. Everything indented underneath is a sequence of instructions that Lean will check step by step.

12. Code:
```lean
    intro i
```
This line introduces the variable or hypothesis named here into the proof context. In ordinary mathematical prose, it is the same as saying “let” or “assume”.

13. Code:
```lean
    simp [p]
```
This line simplifies the goal using definitions and known equalities. `simpa` means that, after simplification, the desired statement matches a theorem Lean already has.

14. Code:
```lean
  have hq_nonneg : ∀ i, 0 ≤ q i := by
```
This line says that a proof script begins here. Everything indented underneath is a sequence of instructions that Lean will check step by step.

15. Code:
```lean
    intro i
```
This line introduces the variable or hypothesis named here into the proof context. In ordinary mathematical prose, it is the same as saying “let” or “assume”.

16. Code:
```lean
    simp [q]
```
This line simplifies the goal using definitions and known equalities. `simpa` means that, after simplification, the desired statement matches a theorem Lean already has.

17. Code:
```lean
  have habs : ∀ i, |hXh.eigenvalues i| = p i + q i := by
```
This line says that a proof script begins here. Everything indented underneath is a sequence of instructions that Lean will check step by step.

18. Code:
```lean
    intro i
```
This line introduces the variable or hypothesis named here into the proof context. In ordinary mathematical prose, it is the same as saying “let” or “assume”.

19. Code:
```lean
    by_cases hi : 0 ≤ hXh.eigenvalues i
```
This line splits the proof into cases according to whether the named proposition is true or false.

20. Code:
```lean
    · simp [p, q, hi, abs_of_nonneg hi]
```
This bullet starts a new subgoal produced by the previous tactic. Lean is now focusing on one branch of the argument.

21. Code:
```lean
    · have hi' : hXh.eigenvalues i < 0 := lt_of_not_ge hi
```
This bullet starts a new subgoal produced by the previous tactic. Lean is now focusing on one branch of the argument.

22. Code:
```lean
      simp [p, q, hi'.le, abs_of_neg hi']
```
This line simplifies the goal using definitions and known equalities. `simpa` means that, after simplification, the desired statement matches a theorem Lean already has.

23. Code:
```lean
  have hsub : ∀ i, hXh.eigenvalues i = p i - q i := by
```
This line says that a proof script begins here. Everything indented underneath is a sequence of instructions that Lean will check step by step.

24. Code:
```lean
    intro i
```
This line introduces the variable or hypothesis named here into the proof context. In ordinary mathematical prose, it is the same as saying “let” or “assume”.

25. Code:
```lean
    by_cases hi : 0 ≤ hXh.eigenvalues i
```
This line splits the proof into cases according to whether the named proposition is true or false.

26. Code:
```lean
    · simp [p, q, hi]
```
This bullet starts a new subgoal produced by the previous tactic. Lean is now focusing on one branch of the argument.

27. Code:
```lean
    · have hi' : hXh.eigenvalues i < 0 := lt_of_not_ge hi
```
This bullet starts a new subgoal produced by the previous tactic. Lean is now focusing on one branch of the argument.

28. Code:
```lean
      simp [p, q, hi'.le]
```
This line simplifies the goal using definitions and known equalities. `simpa` means that, after simplification, the desired statement matches a theorem Lean already has.

29. Code:
```lean
  have hsq : ∀ i, (hXh.eigenvalues i) ^ 2 = (p i) ^ 2 + (q i) ^ 2 := by
```
This line says that a proof script begins here. Everything indented underneath is a sequence of instructions that Lean will check step by step.

30. Code:
```lean
    intro i
```
This line introduces the variable or hypothesis named here into the proof context. In ordinary mathematical prose, it is the same as saying “let” or “assume”.

31. Code:
```lean
    by_cases hi : 0 ≤ hXh.eigenvalues i
```
This line splits the proof into cases according to whether the named proposition is true or false.

32. Code:
```lean
    · simp [p, q, hi, pow_two]
```
This bullet starts a new subgoal produced by the previous tactic. Lean is now focusing on one branch of the argument.

33. Code:
```lean
    · have hi' : hXh.eigenvalues i < 0 := lt_of_not_ge hi
```
This bullet starts a new subgoal produced by the previous tactic. Lean is now focusing on one branch of the argument.

34. Code:
```lean
      simp [p, q, hi'.le, pow_two]
```
This line simplifies the goal using definitions and known equalities. `simpa` means that, after simplification, the desired statement matches a theorem Lean already has.

35. Code:
```lean
  have hsum_zero : ∑ i, hXh.eigenvalues i = 0 := by
```
This line says that a proof script begins here. Everything indented underneath is a sequence of instructions that Lean will check step by step.

36. Code:
```lean
    have htraceC : (∑ i, ((hXh.eigenvalues i : ℝ) : ℂ)) = 0 := by
```
This line says that a proof script begins here. Everything indented underneath is a sequence of instructions that Lean will check step by step.

37. Code:
```lean
      simpa [hXh.trace_eq_sum_eigenvalues] using htr
```
This line simplifies the goal using definitions and known equalities. `simpa` means that, after simplification, the desired statement matches a theorem Lean already has.

38. Code:
```lean
    exact_mod_cast congrArg Complex.re htraceC
```
This line finishes the current goal by giving Lean the exact theorem, lemma, or term that proves it.

39. Code:
```lean
  have hpq : ∑ i, p i = ∑ i, q i := by
```
This line says that a proof script begins here. Everything indented underneath is a sequence of instructions that Lean will check step by step.

40. Code:
```lean
    have hsum_sub : ∑ i, (p i - q i) = 0 := by
```
This line says that a proof script begins here. Everything indented underneath is a sequence of instructions that Lean will check step by step.

41. Code:
```lean
      simpa [hsub] using hsum_zero
```
This line simplifies the goal using definitions and known equalities. `simpa` means that, after simplification, the desired statement matches a theorem Lean already has.

42. Code:
```lean
    rw [Finset.sum_sub_distrib] at hsum_sub
```
This line uses rewriting. Lean replaces one expression by an equal expression using the lemmas listed in brackets.

43. Code:
```lean
    linarith
```
This line solves the current numerical inequality by combining the equalities and inequalities already available in the context.

44. Code:
```lean
  have htraceNorm : traceNormOp X = 2 * ∑ i, p i := by
```
This line says that a proof script begins here. Everything indented underneath is a sequence of instructions that Lean will check step by step.

45. Code:
```lean
    calc
```
This line begins a chained calculation. Each displayed step that follows must be justified by the indented proof after `:= by`.

46. Code:
```lean
      traceNormOp X = ∑ i, |hXh.eigenvalues i| := by
```
This line says that a proof script begins here. Everything indented underneath is a sequence of instructions that Lean will check step by step.

47. Code:
```lean
        simpa using traceNormOp_hermitian_eq_sum_abs_eigenvalues hXh
```
This line simplifies the goal using definitions and known equalities. `simpa` means that, after simplification, the desired statement matches a theorem Lean already has.

48. Code:
```lean
      _ = ∑ i, (p i + q i) := by
```
This line says that a proof script begins here. Everything indented underneath is a sequence of instructions that Lean will check step by step.

49. Code:
```lean
        simp [habs]
```
This line simplifies the goal using definitions and known equalities. `simpa` means that, after simplification, the desired statement matches a theorem Lean already has.

50. Code:
```lean
      _ = ∑ i, p i + ∑ i, q i := by
```
This line says that a proof script begins here. Everything indented underneath is a sequence of instructions that Lean will check step by step.

51. Code:
```lean
        rw [Finset.sum_add_distrib]
```
This line uses rewriting. Lean replaces one expression by an equal expression using the lemmas listed in brackets.

52. Code:
```lean
      _ = 2 * ∑ i, p i := by
```
This line says that a proof script begins here. Everything indented underneath is a sequence of instructions that Lean will check step by step.

53. Code:
```lean
        rw [hpq]
```
This line uses rewriting. Lean replaces one expression by an equal expression using the lemmas listed in brackets.

54. Code:
```lean
        ring
```
This line normalizes an algebraic identity in a commutative ring, just as one would expand and collect like terms by hand.

55. Code:
```lean
  have hhsNormSq : hsNormOp X ^ 2 = ∑ i, (hXh.eigenvalues i) ^ 2 := by
```
This line says that a proof script begins here. Everything indented underneath is a sequence of instructions that Lean will check step by step.

56. Code:
```lean
    rw [hsNorm_sq_eq_re_trace_conjTranspose_mul_self,
```
This line uses rewriting. Lean replaces one expression by an equal expression using the lemmas listed in brackets.

57. Code:
```lean
      hermitian_re_trace_conjTranspose_mul_self_eq_sum_sq_eigenvalues hXh]
```
This line is one local step in the declaration. It either refines the formula being defined or advances the proof by a small algebraic or logical move.

58. Code:
```lean
  have hmain_eq : ∑ i, (hXh.eigenvalues i) ^ 2 = 2 * (∑ i, p i) ^ 2 := by
```
This line says that a proof script begins here. Everything indented underneath is a sequence of instructions that Lean will check step by step.

59. Code:
```lean
    have hsqrt2_ne : Real.sqrt 2 ≠ 0 := by
```
This line says that a proof script begins here. Everything indented underneath is a sequence of instructions that Lean will check step by step.

60. Code:
```lean
      positivity
```
This line asks Lean to prove that the displayed quantity is positive or nonnegative using standard positivity rules.

61. Code:
```lean
    have hsqeq : hsNormOp X ^ 2 = ((1 / Real.sqrt 2) * traceNormOp X) ^ 2 := by
```
This line says that a proof script begins here. Everything indented underneath is a sequence of instructions that Lean will check step by step.

62. Code:
```lean
      exact congrArg (fun t : ℝ => t ^ 2) heq
```
This line finishes the current goal by giving Lean the exact theorem, lemma, or term that proves it.

63. Code:
```lean
    rw [hhsNormSq, htraceNorm] at hsqeq
```
This line uses rewriting. Lean replaces one expression by an equal expression using the lemmas listed in brackets.

64. Code:
```lean
    have hrhs : ((1 / Real.sqrt 2) * (2 * ∑ i, p i)) ^ 2 = 2 * (∑ i, p i) ^ 2 := by
```
This line says that a proof script begins here. Everything indented underneath is a sequence of instructions that Lean will check step by step.

65. Code:
```lean
      field_simp [pow_two, hsqrt2_ne]
```
This line is one local step in the declaration. It either refines the formula being defined or advances the proof by a small algebraic or logical move.

66. Code:
```lean
      nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 2 by positivity)]
```
This line solves the current numerical inequality by combining the equalities and inequalities already available in the context.

67. Code:
```lean
    rw [hrhs] at hsqeq
```
This line uses rewriting. Lean replaces one expression by an equal expression using the lemmas listed in brackets.

68. Code:
```lean
    exact hsqeq
```
This line finishes the current goal by giving Lean the exact theorem, lemma, or term that proves it.

69. Code:
```lean
  have hp_eq : (∑ i, (p i) ^ 2) = (∑ i, p i) ^ 2 := by
```
This line says that a proof script begins here. Everything indented underneath is a sequence of instructions that Lean will check step by step.

70. Code:
```lean
    have hp_le : ∑ i, (p i) ^ 2 ≤ (∑ i, p i) ^ 2 :=
```
This line introduces an intermediate claim. The proof pauses to establish a fact that will be used shortly afterwards.

71. Code:
```lean
      Finset.sum_sq_le_sq_sum_of_nonneg (fun i _ => hp_nonneg i)
```
This line is one local step in the declaration. It either refines the formula being defined or advances the proof by a small algebraic or logical move.

72. Code:
```lean
    have hq_le : ∑ i, (q i) ^ 2 ≤ (∑ i, q i) ^ 2 :=
```
This line introduces an intermediate claim. The proof pauses to establish a fact that will be used shortly afterwards.

73. Code:
```lean
      Finset.sum_sq_le_sq_sum_of_nonneg (fun i _ => hq_nonneg i)
```
This line is one local step in the declaration. It either refines the formula being defined or advances the proof by a small algebraic or logical move.

74. Code:
```lean
    have hq_le' : ∑ i, (q i) ^ 2 ≤ (∑ i, p i) ^ 2 := by
```
This line says that a proof script begins here. Everything indented underneath is a sequence of instructions that Lean will check step by step.

75. Code:
```lean
      simpa [hpq] using hq_le
```
This line simplifies the goal using definitions and known equalities. `simpa` means that, after simplification, the desired statement matches a theorem Lean already has.

76. Code:
```lean
    have haux : ∑ i, (p i) ^ 2 + ∑ i, (q i) ^ 2 = 2 * (∑ i, p i) ^ 2 := by
```
This line says that a proof script begins here. Everything indented underneath is a sequence of instructions that Lean will check step by step.

77. Code:
```lean
      calc
```
This line begins a chained calculation. Each displayed step that follows must be justified by the indented proof after `:= by`.

78. Code:
```lean
        ∑ i, (p i) ^ 2 + ∑ i, (q i) ^ 2 = ∑ i, (hXh.eigenvalues i) ^ 2 := by
```
This line says that a proof script begins here. Everything indented underneath is a sequence of instructions that Lean will check step by step.

79. Code:
```lean
          symm
```
This line is one local step in the declaration. It either refines the formula being defined or advances the proof by a small algebraic or logical move.

80. Code:
```lean
          simp [hsq, Finset.sum_add_distrib]
```
This line simplifies the goal using definitions and known equalities. `simpa` means that, after simplification, the desired statement matches a theorem Lean already has.

81. Code:
```lean
        _ = 2 * (∑ i, p i) ^ 2 := hmain_eq
```
This line is one step inside a `calc` block. Lean is checking that the new expression really follows from the previous one.

82. Code:
```lean
    nlinarith
```
This line solves the current numerical inequality by combining the equalities and inequalities already available in the context.

83. Code:
```lean
  have hq_eq : (∑ i, (q i) ^ 2) = (∑ i, q i) ^ 2 := by
```
This line says that a proof script begins here. Everything indented underneath is a sequence of instructions that Lean will check step by step.

84. Code:
```lean
    have hp_le : ∑ i, (p i) ^ 2 ≤ (∑ i, p i) ^ 2 :=
```
This line introduces an intermediate claim. The proof pauses to establish a fact that will be used shortly afterwards.

85. Code:
```lean
      Finset.sum_sq_le_sq_sum_of_nonneg (fun i _ => hp_nonneg i)
```
This line is one local step in the declaration. It either refines the formula being defined or advances the proof by a small algebraic or logical move.

86. Code:
```lean
    have hp_le' : ∑ i, (p i) ^ 2 ≤ (∑ i, q i) ^ 2 := by
```
This line says that a proof script begins here. Everything indented underneath is a sequence of instructions that Lean will check step by step.

87. Code:
```lean
      simpa [hpq] using hp_le
```
This line simplifies the goal using definitions and known equalities. `simpa` means that, after simplification, the desired statement matches a theorem Lean already has.

88. Code:
```lean
    have hq_le : ∑ i, (q i) ^ 2 ≤ (∑ i, q i) ^ 2 :=
```
This line introduces an intermediate claim. The proof pauses to establish a fact that will be used shortly afterwards.

89. Code:
```lean
      Finset.sum_sq_le_sq_sum_of_nonneg (fun i _ => hq_nonneg i)
```
This line is one local step in the declaration. It either refines the formula being defined or advances the proof by a small algebraic or logical move.

90. Code:
```lean
    have haux : ∑ i, (p i) ^ 2 + ∑ i, (q i) ^ 2 = 2 * (∑ i, q i) ^ 2 := by
```
This line says that a proof script begins here. Everything indented underneath is a sequence of instructions that Lean will check step by step.

91. Code:
```lean
      calc
```
This line begins a chained calculation. Each displayed step that follows must be justified by the indented proof after `:= by`.

92. Code:
```lean
        ∑ i, (p i) ^ 2 + ∑ i, (q i) ^ 2 = ∑ i, (hXh.eigenvalues i) ^ 2 := by
```
This line says that a proof script begins here. Everything indented underneath is a sequence of instructions that Lean will check step by step.

93. Code:
```lean
          symm
```
This line is one local step in the declaration. It either refines the formula being defined or advances the proof by a small algebraic or logical move.

94. Code:
```lean
          simp [hsq, Finset.sum_add_distrib]
```
This line simplifies the goal using definitions and known equalities. `simpa` means that, after simplification, the desired statement matches a theorem Lean already has.

95. Code:
```lean
        _ = 2 * (∑ i, p i) ^ 2 := hmain_eq
```
This line is one step inside a `calc` block. Lean is checking that the new expression really follows from the previous one.

96. Code:
```lean
        _ = 2 * (∑ i, q i) ^ 2 := by
```
This line says that a proof script begins here. Everything indented underneath is a sequence of instructions that Lean will check step by step.

97. Code:
```lean
          rw [hpq]
```
This line uses rewriting. Lean replaces one expression by an equal expression using the lemmas listed in brackets.

98. Code:
```lean
    nlinarith
```
This line solves the current numerical inequality by combining the equalities and inequalities already available in the context.

99. Code:
```lean
  have hp_pair : ∀ i j, i ≠ j → p i = 0 ∨ p j = 0 :=
```
This line introduces an intermediate claim. The proof pauses to establish a fact that will be used shortly afterwards.

100. Code:
```lean
    pairwise_zero_of_sum_sq_eq_sq_sum hp_nonneg hp_eq
```
This line is one local step in the declaration. It either refines the formula being defined or advances the proof by a small algebraic or logical move.

101. Code:
```lean
  have hq_pair : ∀ i j, i ≠ j → q i = 0 ∨ q j = 0 :=
```
This line introduces an intermediate claim. The proof pauses to establish a fact that will be used shortly afterwards.

102. Code:
```lean
    pairwise_zero_of_sum_sq_eq_sq_sum hq_nonneg hq_eq
```
This line is one local step in the declaration. It either refines the formula being defined or advances the proof by a small algebraic or logical move.

103. Code:
```lean
  have hsum_p_ne : ∑ i, p i ≠ 0 := by
```
This line says that a proof script begins here. Everything indented underneath is a sequence of instructions that Lean will check step by step.

104. Code:
```lean
    intro hp0
```
This line introduces the variable or hypothesis named here into the proof context. In ordinary mathematical prose, it is the same as saying “let” or “assume”.

105. Code:
```lean
    have hsum_abs0 : ∑ i, |hXh.eigenvalues i| = 0 := by
```
This line says that a proof script begins here. Everything indented underneath is a sequence of instructions that Lean will check step by step.

106. Code:
```lean
      rw [← traceNormOp_hermitian_eq_sum_abs_eigenvalues hXh, htraceNorm, hp0]
```
This line uses rewriting. Lean replaces one expression by an equal expression using the lemmas listed in brackets.

107. Code:
```lean
      ring
```
This line normalizes an algebraic identity in a commutative ring, just as one would expand and collect like terms by hand.

108. Code:
```lean
    have habs0 : ∀ i, |hXh.eigenvalues i| = 0 := by
```
This line says that a proof script begins here. Everything indented underneath is a sequence of instructions that Lean will check step by step.

109. Code:
```lean
      intro i
```
This line introduces the variable or hypothesis named here into the proof context. In ordinary mathematical prose, it is the same as saying “let” or “assume”.

110. Code:
```lean
      exact
```
This line finishes the current goal by giving Lean the exact theorem, lemma, or term that proves it.

111. Code:
```lean
        (Finset.sum_eq_zero_iff_of_nonneg (fun j hj => abs_nonneg _)).1 hsum_abs0 i (by simp)
```
This line is one local step in the declaration. It either refines the formula being defined or advances the proof by a small algebraic or logical move.

112. Code:
```lean
    have heig0 : hXh.eigenvalues = 0 := by
```
This line says that a proof script begins here. Everything indented underneath is a sequence of instructions that Lean will check step by step.

113. Code:
```lean
      funext i
```
This line uses function extensionality: to prove two functions are equal, it is enough to show they agree on every input.

114. Code:
```lean
      exact abs_eq_zero.mp (habs0 i)
```
This line finishes the current goal by giving Lean the exact theorem, lemma, or term that proves it.

115. Code:
```lean
    exact hX0 ((Matrix.IsHermitian.eigenvalues_eq_zero_iff hXh).1 heig0)
```
This line finishes the current goal by giving Lean the exact theorem, lemma, or term that proves it.

116. Code:
```lean
  have hsum_q_ne : ∑ i, q i ≠ 0 := by
```
This line says that a proof script begins here. Everything indented underneath is a sequence of instructions that Lean will check step by step.

117. Code:
```lean
    rw [← hpq]
```
This line uses rewriting. Lean replaces one expression by an equal expression using the lemmas listed in brackets.

118. Code:
```lean
    exact hsum_p_ne
```
This line finishes the current goal by giving Lean the exact theorem, lemma, or term that proves it.

119. Code:
```lean
  obtain ⟨iPos, hiPos, hiPos_unique⟩ :=
```
This line unpacks an existential statement or tuple into named pieces.

120. Code:
```lean
    existsUnique_nonzero_of_pairwise_zero
```
This line is one local step in the declaration. It either refines the formula being defined or advances the proof by a small algebraic or logical move.

121. Code:
```lean
      (by
```
This line is one local step in the declaration. It either refines the formula being defined or advances the proof by a small algebraic or logical move.

122. Code:
```lean
        rcases Finset.exists_ne_zero_of_sum_ne_zero hsum_p_ne with ⟨i, _, hi⟩
```
This line is one local step in the declaration. It either refines the formula being defined or advances the proof by a small algebraic or logical move.

123. Code:
```lean
        exact ⟨i, hi⟩) hp_pair
```
This line finishes the current goal by giving Lean the exact theorem, lemma, or term that proves it.

124. Code:
```lean
  obtain ⟨iNeg, hiNeg, hiNeg_unique⟩ :=
```
This line unpacks an existential statement or tuple into named pieces.

125. Code:
```lean
    existsUnique_nonzero_of_pairwise_zero
```
This line is one local step in the declaration. It either refines the formula being defined or advances the proof by a small algebraic or logical move.

126. Code:
```lean
      (by
```
This line is one local step in the declaration. It either refines the formula being defined or advances the proof by a small algebraic or logical move.

127. Code:
```lean
        rcases Finset.exists_ne_zero_of_sum_ne_zero hsum_q_ne with ⟨i, _, hi⟩
```
This line is one local step in the declaration. It either refines the formula being defined or advances the proof by a small algebraic or logical move.

128. Code:
```lean
        exact ⟨i, hi⟩) hq_pair
```
This line finishes the current goal by giving Lean the exact theorem, lemma, or term that proves it.

129. Code:
```lean
  have hPos_eig_nonzero : hXh.eigenvalues iPos ≠ 0 := by
```
This line says that a proof script begins here. Everything indented underneath is a sequence of instructions that Lean will check step by step.

130. Code:
```lean
    by_cases hnonneg : 0 ≤ hXh.eigenvalues iPos
```
This line splits the proof into cases according to whether the named proposition is true or false.

131. Code:
```lean
    · have hpval : p iPos = hXh.eigenvalues iPos := by
```
This line says that a proof script begins here. Everything indented underneath is a sequence of instructions that Lean will check step by step.

132. Code:
```lean
        simp [p, hnonneg]
```
This line simplifies the goal using definitions and known equalities. `simpa` means that, after simplification, the desired statement matches a theorem Lean already has.

133. Code:
```lean
      exact hpval ▸ hiPos
```
This line finishes the current goal by giving Lean the exact theorem, lemma, or term that proves it.

134. Code:
```lean
    · have hneg : hXh.eigenvalues iPos < 0 := lt_of_not_ge hnonneg
```
This bullet starts a new subgoal produced by the previous tactic. Lean is now focusing on one branch of the argument.

135. Code:
```lean
      have hpzero : p iPos = 0 := by
```
This line says that a proof script begins here. Everything indented underneath is a sequence of instructions that Lean will check step by step.

136. Code:
```lean
        simp [p, hneg.le]
```
This line simplifies the goal using definitions and known equalities. `simpa` means that, after simplification, the desired statement matches a theorem Lean already has.

137. Code:
```lean
      exact (hiPos hpzero).elim
```
This line finishes the current goal by giving Lean the exact theorem, lemma, or term that proves it.

138. Code:
```lean
  have hNeg_eig_nonzero : hXh.eigenvalues iNeg ≠ 0 := by
```
This line says that a proof script begins here. Everything indented underneath is a sequence of instructions that Lean will check step by step.

139. Code:
```lean
    by_cases hnonneg : 0 ≤ hXh.eigenvalues iNeg
```
This line splits the proof into cases according to whether the named proposition is true or false.

140. Code:
```lean
    · have hqzero : q iNeg = 0 := by
```
This line says that a proof script begins here. Everything indented underneath is a sequence of instructions that Lean will check step by step.

141. Code:
```lean
        simp [q, hnonneg]
```
This line simplifies the goal using definitions and known equalities. `simpa` means that, after simplification, the desired statement matches a theorem Lean already has.

142. Code:
```lean
      exact (hiNeg hqzero).elim
```
This line finishes the current goal by giving Lean the exact theorem, lemma, or term that proves it.

143. Code:
```lean
    · have hneg : hXh.eigenvalues iNeg < 0 := lt_of_not_ge hnonneg
```
This bullet starts a new subgoal produced by the previous tactic. Lean is now focusing on one branch of the argument.

144. Code:
```lean
      have hqval : q iNeg = -hXh.eigenvalues iNeg := by
```
This line says that a proof script begins here. Everything indented underneath is a sequence of instructions that Lean will check step by step.

145. Code:
```lean
        simp [q, hneg.le]
```
This line simplifies the goal using definitions and known equalities. `simpa` means that, after simplification, the desired statement matches a theorem Lean already has.

146. Code:
```lean
      intro heig
```
This line introduces the variable or hypothesis named here into the proof context. In ordinary mathematical prose, it is the same as saying “let” or “assume”.

147. Code:
```lean
      apply hiNeg
```
This line applies an existing theorem to the current goal. Lean then asks the author to prove the theorem’s hypotheses.

148. Code:
```lean
      simp [hqval, heig]
```
This line simplifies the goal using definitions and known equalities. `simpa` means that, after simplification, the desired statement matches a theorem Lean already has.

149. Code:
```lean
  have hij : iPos ≠ iNeg := by
```
This line says that a proof script begins here. Everything indented underneath is a sequence of instructions that Lean will check step by step.

150. Code:
```lean
    intro hijEq
```
This line introduces the variable or hypothesis named here into the proof context. In ordinary mathematical prose, it is the same as saying “let” or “assume”.

151. Code:
```lean
    subst iNeg
```
This line substitutes an equality into the goal and context, replacing one symbol by an equal one everywhere.

152. Code:
```lean
    by_cases hnonneg : 0 ≤ hXh.eigenvalues iPos
```
This line splits the proof into cases according to whether the named proposition is true or false.

153. Code:
```lean
    · have hqzero : q iPos = 0 := by
```
This line says that a proof script begins here. Everything indented underneath is a sequence of instructions that Lean will check step by step.

154. Code:
```lean
        simp [q, hnonneg]
```
This line simplifies the goal using definitions and known equalities. `simpa` means that, after simplification, the desired statement matches a theorem Lean already has.

155. Code:
```lean
      exact hiNeg hqzero
```
This line finishes the current goal by giving Lean the exact theorem, lemma, or term that proves it.

156. Code:
```lean
    · have hneg : hXh.eigenvalues iPos < 0 := lt_of_not_ge hnonneg
```
This bullet starts a new subgoal produced by the previous tactic. Lean is now focusing on one branch of the argument.

157. Code:
```lean
      have hpzero : p iPos = 0 := by
```
This line says that a proof script begins here. Everything indented underneath is a sequence of instructions that Lean will check step by step.

158. Code:
```lean
        simp [p, hneg.le]
```
This line simplifies the goal using definitions and known equalities. `simpa` means that, after simplification, the desired statement matches a theorem Lean already has.

159. Code:
```lean
      exact hiPos hpzero
```
This line finishes the current goal by giving Lean the exact theorem, lemma, or term that proves it.

160. Code:
```lean
  have hsupport : ∀ i, hXh.eigenvalues i ≠ 0 → i = iPos ∨ i = iNeg := by
```
This line says that a proof script begins here. Everything indented underneath is a sequence of instructions that Lean will check step by step.

161. Code:
```lean
    intro i hi
```
This line introduces the variable or hypothesis named here into the proof context. In ordinary mathematical prose, it is the same as saying “let” or “assume”.

162. Code:
```lean
    by_cases hnonneg : 0 ≤ hXh.eigenvalues i
```
This line splits the proof into cases according to whether the named proposition is true or false.

163. Code:
```lean
    · left
```
This bullet starts a new subgoal produced by the previous tactic. Lean is now focusing on one branch of the argument.

164. Code:
```lean
      have hp_i : p i ≠ 0 := by
```
This line says that a proof script begins here. Everything indented underneath is a sequence of instructions that Lean will check step by step.

165. Code:
```lean
        have hpval : p i = hXh.eigenvalues i := by
```
This line says that a proof script begins here. Everything indented underneath is a sequence of instructions that Lean will check step by step.

166. Code:
```lean
          simp [p, hnonneg]
```
This line simplifies the goal using definitions and known equalities. `simpa` means that, after simplification, the desired statement matches a theorem Lean already has.

167. Code:
```lean
        exact hpval ▸ hi
```
This line finishes the current goal by giving Lean the exact theorem, lemma, or term that proves it.

168. Code:
```lean
      exact hiPos_unique i hp_i
```
This line finishes the current goal by giving Lean the exact theorem, lemma, or term that proves it.

169. Code:
```lean
    · right
```
This bullet starts a new subgoal produced by the previous tactic. Lean is now focusing on one branch of the argument.

170. Code:
```lean
      have hneg : hXh.eigenvalues i < 0 := lt_of_not_ge hnonneg
```
This line introduces an intermediate claim. The proof pauses to establish a fact that will be used shortly afterwards.

171. Code:
```lean
      have hq_i : q i ≠ 0 := by
```
This line says that a proof script begins here. Everything indented underneath is a sequence of instructions that Lean will check step by step.

172. Code:
```lean
        have hqval : q i = -hXh.eigenvalues i := by
```
This line says that a proof script begins here. Everything indented underneath is a sequence of instructions that Lean will check step by step.

173. Code:
```lean
          simp [q, hneg.le]
```
This line simplifies the goal using definitions and known equalities. `simpa` means that, after simplification, the desired statement matches a theorem Lean already has.

174. Code:
```lean
        rw [hqval]
```
This line uses rewriting. Lean replaces one expression by an equal expression using the lemmas listed in brackets.

175. Code:
```lean
        exact neg_ne_zero.mpr hi
```
This line finishes the current goal by giving Lean the exact theorem, lemma, or term that proves it.

176. Code:
```lean
      exact hiNeg_unique i hq_i
```
This line finishes the current goal by giving Lean the exact theorem, lemma, or term that proves it.

177. Code:
```lean
  have hle : Fintype.card {i : d × d // hXh.eigenvalues i ≠ 0} ≤ 2 := by
```
This line says that a proof script begins here. Everything indented underneath is a sequence of instructions that Lean will check step by step.  `Fintype.card` is the size of a finite index set.

178. Code:
```lean
    classical
```
This line is one local step in the declaration. It either refines the formula being defined or advances the proof by a small algebraic or logical move.

179. Code:
```lean
    let f : {i : d × d // hXh.eigenvalues i ≠ 0} → {i : d × d // i = iPos ∨ i = iNeg} :=
```
This line gives a temporary name to an expression. Doing that makes later lines shorter and easier to read.

180. Code:
```lean
      fun i => ⟨i.1, hsupport i.1 i.2⟩
```
This line is one local step in the declaration. It either refines the formula being defined or advances the proof by a small algebraic or logical move.

181. Code:
```lean
    have hf : Function.Injective f := by
```
This line says that a proof script begins here. Everything indented underneath is a sequence of instructions that Lean will check step by step.

182. Code:
```lean
      intro a b h
```
This line introduces the variable or hypothesis named here into the proof context. In ordinary mathematical prose, it is the same as saying “let” or “assume”.

183. Code:
```lean
      apply Subtype.ext
```
This line applies an existing theorem to the current goal. Lean then asks the author to prove the theorem’s hypotheses.

184. Code:
```lean
      simpa using congrArg (fun z => z.1) h
```
This line simplifies the goal using definitions and known equalities. `simpa` means that, after simplification, the desired statement matches a theorem Lean already has.

185. Code:
```lean
    have hcard := Fintype.card_le_of_injective f hf
```
This line introduces an intermediate claim. The proof pauses to establish a fact that will be used shortly afterwards.  `Fintype.card` is the size of a finite index set.

186. Code:
```lean
    simpa [Fintype.card_subtype_eq_or_eq_of_ne hij] using hcard
```
This line simplifies the goal using definitions and known equalities. `simpa` means that, after simplification, the desired statement matches a theorem Lean already has.  A bracket such as `[Fintype d]` tells Lean that the index set `d` is finite, so sums over all indices make sense.  `Fintype.card` is the size of a finite index set.

187. Code:
```lean
  have hge : 2 ≤ Fintype.card {i : d × d // hXh.eigenvalues i ≠ 0} := by
```
This line says that a proof script begins here. Everything indented underneath is a sequence of instructions that Lean will check step by step.  `Fintype.card` is the size of a finite index set.

188. Code:
```lean
    classical
```
This line is one local step in the declaration. It either refines the formula being defined or advances the proof by a small algebraic or logical move.

189. Code:
```lean
    let g : Bool → {i : d × d // hXh.eigenvalues i ≠ 0} :=
```
This line gives a temporary name to an expression. Doing that makes later lines shorter and easier to read.

190. Code:
```lean
      fun b => cond b ⟨iPos, hPos_eig_nonzero⟩ ⟨iNeg, hNeg_eig_nonzero⟩
```
This line is one local step in the declaration. It either refines the formula being defined or advances the proof by a small algebraic or logical move.

191. Code:
```lean
    have hg : Function.Injective g := by
```
This line says that a proof script begins here. Everything indented underneath is a sequence of instructions that Lean will check step by step.

192. Code:
```lean
      intro a b h
```
This line introduces the variable or hypothesis named here into the proof context. In ordinary mathematical prose, it is the same as saying “let” or “assume”.

193. Code:
```lean
      cases a <;> cases b
```
This line breaks a structured object into cases or components so that each can be handled separately.

194. Code:
```lean
      · rfl
```
This bullet starts a new subgoal produced by the previous tactic. Lean is now focusing on one branch of the argument.

195. Code:
```lean
      · have h' : iNeg = iPos := by simpa [g] using h
```
This bullet starts a new subgoal produced by the previous tactic. Lean is now focusing on one branch of the argument.

196. Code:
```lean
        exact (hij h'.symm).elim
```
This line finishes the current goal by giving Lean the exact theorem, lemma, or term that proves it.

197. Code:
```lean
      · have h' : iPos = iNeg := by simpa [g] using h
```
This bullet starts a new subgoal produced by the previous tactic. Lean is now focusing on one branch of the argument.

198. Code:
```lean
        exact (hij h').elim
```
This line finishes the current goal by giving Lean the exact theorem, lemma, or term that proves it.

199. Code:
```lean
      · rfl
```
This bullet starts a new subgoal produced by the previous tactic. Lean is now focusing on one branch of the argument.

200. Code:
```lean
    have hcard := Fintype.card_le_of_injective g hg
```
This line introduces an intermediate claim. The proof pauses to establish a fact that will be used shortly afterwards.  `Fintype.card` is the size of a finite index set.

201. Code:
```lean
    simpa using hcard
```
This line simplifies the goal using definitions and known equalities. `simpa` means that, after simplification, the desired statement matches a theorem Lean already has.

202. Code:
```lean
  have hcard : Fintype.card {i : d × d // hXh.eigenvalues i ≠ 0} = 2 := by
```
This line says that a proof script begins here. Everything indented underneath is a sequence of instructions that Lean will check step by step.  `Fintype.card` is the size of a finite index set.

203. Code:
```lean
    omega
```
This line is one local step in the declaration. It either refines the formula being defined or advances the proof by a small algebraic or logical move.

204. Code:
```lean
  rw [hXh.rank_eq_card_non_zero_eigs, hcard]
```
This line uses rewriting. Lean replaces one expression by an equal expression using the lemmas listed in brackets.

## Mathematical summary

Restated without Lean syntax, `lemma1_eq_imp_rank_two` is the theorem or lemma written above.

- State the desired identity or inequality in Lean’s syntax.
- Introduce temporary names and intermediate claims that organize the argument.
- Use rewriting, simplification, and earlier lemmas to reduce the goal to standard matrix or norm manipulations.
- Close the remaining algebraic or order-theoretic steps with Lean’s proof tactics.

## Dependencies and downstream use

### Earlier declarations this depends on
- [`traceNormOp`](../../Setups/traceNormOp.md) from `Setups.lean`
- [`hsNormOp`](../../Setups/hsNormOp.md) from `Setups.lean`
- [`hsNorm_sq_eq_re_trace_conjTranspose_mul_self`](../../Theorem/Lemma1/hsNorm_sq_eq_re_trace_conjTranspose_mul_self.md) from `Theorem/Lemma1.lean`
- [`hermitian_re_trace_conjTranspose_mul_self_eq_sum_sq_eigenvalues`](../../Theorem/Lemma1/hermitian_re_trace_conjTranspose_mul_self_eq_sum_sq_eigenvalues.md) from `Theorem/Lemma1.lean`
- [`traceNormOp_hermitian_eq_sum_abs_eigenvalues`](../../Theorem/Lemma1/traceNormOp_hermitian_eq_sum_abs_eigenvalues.md) from `Theorem/Lemma1.lean`
- [`hsNorm_sq_eq_re_trace_conjTranspose_mul_self`](../../Theorem/Lemma2/hsNorm_sq_eq_re_trace_conjTranspose_mul_self.md) from `Theorem/Lemma2.lean`
- [`pairwise_zero_of_sum_sq_eq_sq_sum`](pairwise_zero_of_sum_sq_eq_sq_sum.md) from `PositiveGap/NotTight.lean`
- [`existsUnique_nonzero_of_pairwise_zero`](existsUnique_nonzero_of_pairwise_zero.md) from `PositiveGap/NotTight.lean`

### Later declarations that use this one
- [`theorem_not_tight`](theorem_not_tight.md) in `PositiveGap/NotTight.lean`

## Backlinks

- [Back to `INDEX.md`](../../INDEX.md)
- [Back to the `PositiveGap/NotTight.lean` section in the index](../../INDEX.md#diamond-positivegap-nottight-lean)
- [Previous declaration in this file](all_equal_of_sq_sum_eq_card_mul_sum_sq.md)
- [Next declaration in this file](lemma2_eq_imp_full_rank.md)