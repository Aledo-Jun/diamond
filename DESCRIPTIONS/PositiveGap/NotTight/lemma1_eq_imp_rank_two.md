---
layout: default
---

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

## How To Read This Declaration

This page now uses a concise reading guide instead of a line-by-line Lean walkthrough.
The best way to read the declaration is:

1. read the **Why this declaration exists** section for the mathematical role,
2. read the **Original code** block as the exact formal statement or construction,
3. treat the proof as a small number of conceptual moves rather than a commentary on each Lean line.

## Proof / Construction Shape

Most declarations in this repository follow the same pattern:

- **setup**: introduce the ambient spaces, matrices, channels, or witnesses,
- **reduction**: rewrite the goal into a standard matrix, trace, or diamond-norm form,
- **core step**: apply previously proved lemmas from the same module or an earlier one,
- **finish**: simplify the remaining algebra with `rw`, `simp`, `calc`, or `ext`.

## Lean Cues

- `let` names an intermediate mathematical object.
- `have` records a useful subclaim.
- `calc` is a displayed derivation written as a chain of equalities or inequalities.
- `rw` rewrites using an identity.
- `simp` performs controlled simplification.
- `ext` means the proof is reduced to entrywise or pointwise equality.

For the math-first reading path, start from `DESCRIPTIONS/INDEX.md` and use the module overviews and flagship theorem pages before coming back to individual declaration pages.
