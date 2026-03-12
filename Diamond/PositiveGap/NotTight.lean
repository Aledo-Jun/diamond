import Diamond.Setups
import Diamond.StandardFacts
import Diamond.Theorem.Lemma1
import Diamond.Theorem.Lemma2
import Diamond.Theorem.Lemma3
import Diamond.Theorem.Theorem1
import Diamond.PositiveGap.Lemma5
import Diamond.PositiveGap.Lemma6
import Diamond.PositiveGap.Lemma7
import Diamond.PositiveGap.Corollary1

open scoped BigOperators
open scoped ComplexOrder
open scoped Kronecker
open scoped MatrixOrder
open scoped Matrix.Norms.Frobenius
open Matrix

namespace Diamond

universe u

noncomputable section

/-- Expand a square of a finite sum into diagonal and off-diagonal parts. -/
private lemma sq_sum_expand_offDiag
    {ι : Type u} [Fintype ι] (p : ι → ℝ) :
    (∑ i, p i) ^ 2 =
      (∑ i, (p i) ^ 2) + ∑ x ∈ (Finset.univ : Finset ι).offDiag, p x.1 * p x.2 := by
  classical
  calc
    (∑ i, p i) ^ 2 = (∑ i, p i) * (∑ j, p j) := by
      ring
    _ = ∑ x ∈ ((Finset.univ : Finset ι) ×ˢ (Finset.univ : Finset ι)), p x.1 * p x.2 := by
      calc
        (∑ i, p i) * (∑ j, p j) = ∑ i, ∑ j, p i * p j := by
          simpa using (Fintype.sum_mul_sum p p)
        _ = ∑ x ∈ ((Finset.univ : Finset ι) ×ˢ (Finset.univ : Finset ι)), p x.1 * p x.2 := by
          rw [← Finset.sum_product']
    _ = ∑ x ∈ (Finset.univ : Finset ι).diag ∪ (Finset.univ : Finset ι).offDiag,
          p x.1 * p x.2 := by
      rw [← Finset.diag_union_offDiag]
    _ = (∑ x ∈ (Finset.univ : Finset ι).diag, p x.1 * p x.2) +
          ∑ x ∈ (Finset.univ : Finset ι).offDiag, p x.1 * p x.2 := by
      rw [Finset.sum_union (Finset.disjoint_diag_offDiag (s := (Finset.univ : Finset ι)))]
    _ = (∑ i, (p i) ^ 2) + ∑ x ∈ (Finset.univ : Finset ι).offDiag, p x.1 * p x.2 := by
      rw [Finset.sum_diag]
      simp [pow_two]

/-- Equality in `∑ p_i^2 ≤ (∑ p_i)^2` forces all mixed terms to vanish. -/
private lemma pairwise_zero_of_sum_sq_eq_sq_sum
    {ι : Type u} [Fintype ι] {p : ι → ℝ}
    (hp : ∀ i, 0 ≤ p i)
    (heq : (∑ i, (p i) ^ 2) = (∑ i, p i) ^ 2) :
    ∀ i j, i ≠ j → p i = 0 ∨ p j = 0 := by
  classical
  have hoffDiag_zero : ∑ x ∈ (Finset.univ : Finset ι).offDiag, p x.1 * p x.2 = 0 := by
    have hexpand := sq_sum_expand_offDiag p
    linarith
  have hpair_zero :
      ∀ x ∈ (Finset.univ : Finset ι).offDiag, p x.1 * p x.2 = 0 := by
    exact
      (Finset.sum_eq_zero_iff_of_nonneg
        (fun x hx => mul_nonneg (hp x.1) (hp x.2))).1 hoffDiag_zero
  intro i j hij
  have hmem : (i, j) ∈ (Finset.univ : Finset ι).offDiag := by
    exact Finset.mem_offDiag.2 ⟨Finset.mem_univ i, Finset.mem_univ j, hij⟩
  have hmul : p i * p j = 0 := hpair_zero (i, j) hmem
  by_cases hi : p i = 0
  · exact Or.inl hi
  · right
    exact mul_eq_zero.mp hmul |>.resolve_left hi

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

/-- Algebraic variance identity for finite real families. -/
private lemma sum_sq_sub_avg_eq_aux
    {ι : Type u} [Fintype ι] [Nonempty ι] {a : ι → ℝ} :
    let avg : ℝ := (∑ i, a i) / (Fintype.card ι : ℝ)
    ∑ i, (a i) ^ 2 - 2 * avg * ∑ i, a i + (Fintype.card ι : ℝ) * avg ^ 2 =
      ∑ i, (a i) ^ 2 - (∑ i, a i) ^ 2 / (Fintype.card ι : ℝ) := by
  let avg : ℝ := (∑ i, a i) / (Fintype.card ι : ℝ)
  have hcard_ne : (Fintype.card ι : ℝ) ≠ 0 := by
    positivity
  field_simp [avg, hcard_ne]
  ring

/-- The sum of squared deviations from the average. -/
private lemma sum_sq_sub_avg_eq
    {ι : Type u} [Fintype ι] [Nonempty ι] {a : ι → ℝ} :
    let avg : ℝ := (∑ i, a i) / (Fintype.card ι : ℝ)
    ∑ i, (a i - avg) ^ 2 =
      ∑ i, (a i) ^ 2 - (∑ i, a i) ^ 2 / (Fintype.card ι : ℝ) := by
  let avg : ℝ := (∑ i, a i) / (Fintype.card ι : ℝ)
  calc
    ∑ i, (a i - avg) ^ 2 =
        ∑ i, (a i) ^ 2 - 2 * avg * ∑ i, a i + (Fintype.card ι : ℝ) * avg ^ 2 := by
          calc
            ∑ i, (a i - avg) ^ 2 = ∑ i, ((a i) ^ 2 - 2 * a i * avg + avg ^ 2) := by
              refine Finset.sum_congr rfl ?_
              intro i hi
              ring
            _ = ∑ i, (a i) ^ 2 - 2 * avg * ∑ i, a i + (Fintype.card ι : ℝ) * avg ^ 2 := by
              simp [Finset.sum_sub_distrib, Finset.sum_add_distrib, Finset.sum_mul,
                mul_comm, mul_left_comm]
    _ = ∑ i, (a i) ^ 2 - (∑ i, a i) ^ 2 / (Fintype.card ι : ℝ) := by
      simpa using (sum_sq_sub_avg_eq_aux (a := a))

/-- Equality in Cauchy--Schwarz for a finite real family forces all entries to be equal. -/
private lemma all_equal_of_sq_sum_eq_card_mul_sum_sq
    {ι : Type u} [Fintype ι] [Nonempty ι] {a : ι → ℝ}
    (heq : (∑ i, a i) ^ 2 = (Fintype.card ι : ℝ) * ∑ i, (a i) ^ 2) :
    ∀ i j, a i = a j := by
  let avg : ℝ := (∑ i, a i) / (Fintype.card ι : ℝ)
  have hzero : ∑ i, (a i - avg) ^ 2 = 0 := by
    rw [sum_sq_sub_avg_eq]
    have hcard_ne : (Fintype.card ι : ℝ) ≠ 0 := by
      positivity
    have hdiv : (∑ i, a i) ^ 2 / (Fintype.card ι : ℝ) = ∑ i, (a i) ^ 2 := by
      exact (div_eq_iff hcard_ne).2 (by simpa [mul_comm] using heq)
    linarith
  have hsq_zero' := (Finset.sum_eq_zero_iff_of_nonneg (fun i hi => sq_nonneg _)).1 hzero
  intro i j
  have hi : a i = avg := by
    have hsq : (a i - avg) ^ 2 = 0 := hsq_zero' i (by simp)
    nlinarith
  have hj : a j = avg := by
    have hsq : (a j - avg) ^ 2 = 0 := hsq_zero' j (by simp)
    nlinarith
  linarith

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

/-- Equality case of paper Lemma 2:
    a nonzero matrix saturating Lemma 2 has full rank. -/
theorem lemma2_eq_imp_full_rank
    {d : Type u} [Fintype d] [DecidableEq d]
    [Nonempty d]
    {Y : Matrix (d × d) (d × d) ℂ} (hY0 : Y ≠ 0)
    (heq : traceNormOp Y =
      Real.sqrt (Fintype.card (d × d) : ℝ) * hsNormOp Y) :
    Matrix.rank Y = Fintype.card (d × d) := by
  let μ : d × d → ℝ := (Matrix.isHermitian_conjTranspose_mul_self Y).eigenvalues
  have hμ_nonneg : ∀ i, 0 ≤ μ i := by
    intro i
    exact Matrix.eigenvalues_conjTranspose_mul_self_nonneg Y i
  have hnorm_sq : hsNormOp Y ^ 2 = ∑ i, μ i := by
    calc
      hsNormOp Y ^ 2 = Complex.re (Matrix.trace (Yᴴ * Y)) := by
        exact hsNorm_sq_eq_re_trace_conjTranspose_mul_self Y
      _ = ∑ i, μ i := by
        rw [(Matrix.isHermitian_conjTranspose_mul_self Y).trace_eq_sum_eigenvalues]
        simp [μ]
  have hsqeq : (∑ i, Real.sqrt (μ i)) ^ 2 = (Fintype.card (d × d) : ℝ) * ∑ i, μ i := by
    have hsq := congrArg (fun t : ℝ => t ^ 2) heq
    calc
      (∑ i, Real.sqrt (μ i)) ^ 2 = (traceNormOp Y) ^ 2 := by
        rfl
      _ = (Real.sqrt (Fintype.card (d × d) : ℝ) * hsNormOp Y) ^ 2 := by
        simpa using hsq
      _ = (Fintype.card (d × d) : ℝ) * ∑ i, μ i := by
        rw [show (Real.sqrt (Fintype.card (d × d) : ℝ) * hsNormOp Y) ^ 2 =
              (Real.sqrt (Fintype.card (d × d) : ℝ)) ^ 2 * (hsNormOp Y) ^ 2 by ring]
        rw [Real.sq_sqrt (by positivity), hnorm_sq]
  have hall : ∀ i j, Real.sqrt (μ i) = Real.sqrt (μ j) := by
    have hsqeq' :
        (∑ i, Real.sqrt (μ i)) ^ 2 =
          (Fintype.card (d × d) : ℝ) * ∑ i, (Real.sqrt (μ i)) ^ 2 := by
      calc
        (∑ i, Real.sqrt (μ i)) ^ 2 = (Fintype.card (d × d) : ℝ) * ∑ i, μ i := hsqeq
        _ = (Fintype.card (d × d) : ℝ) * ∑ i, (Real.sqrt (μ i)) ^ 2 := by
          refine congrArg ((Fintype.card (d × d) : ℝ) * ·) ?_
          refine Finset.sum_congr rfl ?_
          intro i hi
          exact (Real.sq_sqrt (hμ_nonneg i)).symm
    exact all_equal_of_sq_sum_eq_card_mul_sum_sq hsqeq'
  have hμ_not_zero_fun : μ ≠ 0 := by
    intro hμ0
    have hzeroMat : Yᴴ * Y = 0 := by
      exact
        (Matrix.IsHermitian.eigenvalues_eq_zero_iff
          (Matrix.isHermitian_conjTranspose_mul_self Y)).1 hμ0
    exact hY0 ((Matrix.conjTranspose_mul_self_eq_zero).1 hzeroMat)
  classical
  have hex : ∃ i, μ i ≠ 0 := by
    by_contra h
    push_neg at h
    exact hμ_not_zero_fun (funext h)
  rcases hex with ⟨i0, hi0⟩
  have hsqrt_pos : 0 < Real.sqrt (μ i0) := by
    apply Real.sqrt_pos.2
    exact lt_of_le_of_ne (hμ_nonneg i0) (by simpa [eq_comm] using hi0)
  have hμ_ne : ∀ i, μ i ≠ 0 := by
    intro i
    have hsqrt_eq : Real.sqrt (μ i) = Real.sqrt (μ i0) := hall i i0
    intro hzi
    rw [hzi, Real.sqrt_zero] at hsqrt_eq
    linarith
  have hcard : Fintype.card {i : d × d // μ i ≠ 0} = Fintype.card (d × d) := by
    classical
    exact
      Fintype.card_of_subtype
        (s := (Finset.univ : Finset (d × d)))
        (H := fun i => by simp [hμ_ne i])
  calc
    Y.rank = (Yᴴ * Y).rank := by
      symm
      exact Matrix.rank_conjTranspose_mul_self Y
    _ = Fintype.card {i : d × d // μ i ≠ 0} := by
      rw [(Matrix.isHermitian_conjTranspose_mul_self Y).rank_eq_card_non_zero_eigs]
    _ = Fintype.card (d × d) := hcard

/-- Partial transpose preserves nonzeroness because it preserves the Hilbert--Schmidt norm. -/
private lemma partialTranspose_ne_zero_of_ne_zero
    {d k : Type u} [Fintype d] [DecidableEq d] [Fintype k] [DecidableEq k]
    {X : Matrix (d × k) (d × k) ℂ} (hX : X ≠ 0) :
    partialTransposeMap d k X ≠ 0 := by
  intro hzero
  have hnormY : hsNormOp (partialTransposeMap d k X) = 0 := by
    exact (hsNormOp_eq_zero_iff).2 hzero
  have hnormX : hsNormOp X = 0 := by
    rw [lemma3 (d := d) (k := k) X] at hnormY
    exact hnormY
  exact hX ((hsNormOp_eq_zero_iff).1 hnormX)

/-- Generic vectorization used for the local positive-gap rank argument. -/
private def vecKetGen
    {d : Type u} [Fintype d] [DecidableEq d] (A : Matrix d d ℂ) : d × d → ℂ :=
  fun ij => A ij.1 ij.2

/-- Generic swap operator on `d × d`. -/
private def swapMatrixGen
    (d : Type u) [Fintype d] [DecidableEq d] : Matrix (d × d) (d × d) ℂ :=
  fun i j => if i.1 = j.2 ∧ i.2 = j.1 then 1 else 0

/-- Generic form of Lemma 6. -/
private theorem lemma6_gen
    {d : Type u} [Fintype d] [DecidableEq d]
    (X Y : Matrix d d ℂ) :
    swapMatrixGen d * (X ⊗ₖ Y) = (Y ⊗ₖ X) * swapMatrixGen d := by
  ext i j
  rcases i with ⟨a, b⟩
  rcases j with ⟨c, e⟩
  have hleft :
      (swapMatrixGen d * (X ⊗ₖ Y)) (a, b) (c, e) = X b c * Y a e := by
    rw [Matrix.mul_apply]
    rw [Finset.sum_eq_single (b, a)]
    · simp [swapMatrixGen, Matrix.kroneckerMap_apply]
    · intro x _ hx
      have hzero : ¬ (a = x.2 ∧ b = x.1) := by
        intro h
        apply hx
        ext <;> simp [h.1, h.2]
      simp [swapMatrixGen, Matrix.kroneckerMap_apply, hzero]
    · intro hba
      simp at hba
  have hright :
      ((Y ⊗ₖ X) * swapMatrixGen d) (a, b) (c, e) = Y a e * X b c := by
    rw [Matrix.mul_apply]
    rw [Finset.sum_eq_single (e, c)]
    · simp [swapMatrixGen, Matrix.kroneckerMap_apply]
    · intro x _ hx
      have hzero : ¬ (x.1 = e ∧ x.2 = c) := by
        intro h
        apply hx
        ext <;> simp [h.1, h.2]
      simp [swapMatrixGen, Matrix.kroneckerMap_apply, hzero]
    · intro hec
      simp at hec
  rw [hleft, hright, mul_comm]

/-- Entrywise helper for the generic form of Lemma 7. -/
private theorem oneKronecker_mul_swap_apply_gen
    {d : Type u} [Fintype d] [DecidableEq d]
    (A : Matrix d d ℂ) (a b c e : d) :
    (((1 : Matrix d d ℂ) ⊗ₖ A) * swapMatrixGen d) (a, b) (c, e) =
      if a = e then A b c else 0 := by
  rw [Matrix.mul_apply]
  rw [Finset.sum_eq_single (e, c)]
  · simp [swapMatrixGen, Matrix.kroneckerMap_apply, Matrix.one_apply]
  · intro x _ hx
    have hzero : ¬ (x.1 = e ∧ x.2 = c) := by
      intro h
      apply hx
      ext <;> simp [h.1, h.2]
    simp [swapMatrixGen, Matrix.kroneckerMap_apply, Matrix.one_apply, hzero]
  · intro hec
    simp at hec

/-- Generic form of Lemma 7. -/
private theorem lemma7_gen
    {d : Type u} [Fintype d] [DecidableEq d]
    (A B : Matrix d d ℂ) :
    partialTransposeMap d d (Matrix.vecMulVec (vecKetGen A) (star (vecKetGen B))) =
      (((1 : Matrix d d ℂ) ⊗ₖ Aᵀ) * swapMatrixGen d) *
        ((1 : Matrix d d ℂ) ⊗ₖ B.map star) := by
  ext i j
  rcases i with ⟨p, i⟩
  rcases j with ⟨q, j⟩
  have hleft :
      partialTransposeMap d d (Matrix.vecMulVec (vecKetGen A) (star (vecKetGen B))) (p, i) (q, j) =
        A q i * star (B p j) := by
    simp [partialTransposeMap, Matrix.vecMulVec_apply, vecKetGen]
  have hright :
      ((((1 : Matrix d d ℂ) ⊗ₖ Aᵀ) * swapMatrixGen d) *
          ((1 : Matrix d d ℂ) ⊗ₖ B.map star))
          (p, i) (q, j) =
        A q i * star (B p j) := by
    rw [Matrix.mul_apply]
    rw [Finset.sum_eq_single (q, p)]
    · simp [oneKronecker_mul_swap_apply_gen, Matrix.kroneckerMap_apply]
    · intro x _ hx
      by_cases hx1 : x.1 = q
      · by_cases hx2 : x.2 = p
        · apply (hx <| by ext <;> simp [hx1, hx2]).elim
        · have hleftzero :
              (((1 : Matrix d d ℂ) ⊗ₖ Aᵀ) * swapMatrixGen d) (p, i) x = 0 := by
            rw [oneKronecker_mul_swap_apply_gen]
            simp [show ¬ p = x.2 by simpa [eq_comm] using hx2]
          simp [hleftzero, Matrix.kroneckerMap_apply, Matrix.one_apply, hx1]
      · have hrightzero :
            (((1 : Matrix d d ℂ) ⊗ₖ B.map star) x (q, j)) = 0 := by
          simp [Matrix.kroneckerMap_apply, hx1]
        rw [hrightzero]
        simp
    · intro hqp
      simp at hqp
  rw [hleft, hright]

/-- Rank bound for the diagonal tensor-difference matrix coming from a unitary diagonalization. -/
private theorem rank_diagonal_tensor_difference_upper_bound
    {d : Type u} [Fintype d] [DecidableEq d]
    (ω : d → ℂ) (hω : ∀ i, ω i * star (ω i) = 1) :
    (Matrix.diagonal fun ij : d × d => 1 - ω ij.1 * star (ω ij.2)).rank ≤
      Fintype.card (d × d) - Fintype.card d := by
  let p : d × d → Prop := fun ij => 1 - ω ij.1 * star (ω ij.2) ≠ 0
  have hzeroCard : Fintype.card d ≤ Fintype.card {ij : d × d // ¬ p ij} := by
    let f : d → {ij : d × d // ¬ p ij} := fun i =>
      ⟨(i, i), by
        dsimp [p]
        exact not_not.mpr (sub_eq_zero.mpr (hω i).symm)⟩
    have hf : Function.Injective f := by
      intro i j h
      simpa using congrArg Prod.fst (congrArg Subtype.val h)
    exact Fintype.card_le_of_injective f hf
  have hcompl :
      Fintype.card {ij : d × d // ¬ p ij} =
        Fintype.card (d × d) - Fintype.card {ij : d × d // p ij} := by
    simpa [p] using (Fintype.card_subtype_compl p)
  have hp_le : Fintype.card {ij : d × d // p ij} ≤ Fintype.card (d × d) :=
    Fintype.card_subtype_le p
  have hsum :
      Fintype.card {ij : d × d // p ij} + Fintype.card {ij : d × d // ¬ p ij} =
        Fintype.card (d × d) := by
    omega
  have hcount :
      Fintype.card {ij : d × d // p ij} ≤ Fintype.card (d × d) - Fintype.card d := by
    omega
  simpa [p] using
    (show
      (Matrix.diagonal fun ij : d × d => 1 - ω ij.1 * star (ω ij.2)).rank ≤
        Fintype.card (d × d) - Fintype.card d by
      rw [Matrix.rank_diagonal]
      exact hcount)

/-- Rank bound for `I - Uᵀ ⊗ U*` obtained from diagonalizing the unitary `U`. -/
private theorem rank_tensor_difference_upper_bound
    {d : Type u} [Fintype d] [DecidableEq d]
    (U : Matrix d d ℂ) (hU : Uᴴ * U = 1) :
    ((1 : Matrix (d × d) (d × d) ℂ) - (Uᵀ ⊗ₖ U.map star)).rank ≤
      Fintype.card (d × d) - Fintype.card d := by
  obtain ⟨V, ω, hV, hω, hdiagU⟩ := unitary_diagonalization U hU
  let P : Matrix (d × d) (d × d) ℂ := V.map star ⊗ₖ V.map star
  let D : Matrix (d × d) (d × d) ℂ :=
    Matrix.diagonal fun ij : d × d => ω ij.1 * star (ω ij.2)
  let Q : Matrix (d × d) (d × d) ℂ := Vᵀ ⊗ₖ Vᵀ
  have hVmem : V ∈ Matrix.unitaryGroup d ℂ := (Matrix.mem_unitaryGroup_iff').2 hV
  have hVright : V * Vᴴ = 1 := (Matrix.mem_unitaryGroup_iff.mp hVmem)
  have hPQ0 : V.map star * Vᵀ = 1 := by
    simpa using congrArg Matrix.transpose hVright
  have hPQt : P * Q = 1 := by
    calc
      P * Q = (V.map star * Vᵀ) ⊗ₖ (V.map star * Vᵀ) := by
        simp [P, Q, Matrix.mul_kronecker_mul]
      _ = (1 : Matrix d d ℂ) ⊗ₖ (1 : Matrix d d ℂ) := by
        ext i j
        rw [Matrix.kroneckerMap_apply, Matrix.kroneckerMap_apply]
        rw [show (V.map star * Vᵀ) i.1 j.1 = (1 : Matrix d d ℂ) i.1 j.1 by
              simpa using congrArg (fun M => M i.1 j.1) hPQ0]
        rw [show (V.map star * Vᵀ) i.2 j.2 = (1 : Matrix d d ℂ) i.2 j.2 by
              simpa using congrArg (fun M => M i.2 j.2) hPQ0]
      _ = 1 := by
        exact one_kronecker_one (α := ℂ) (m := d) (n := d)
  have hUt : Uᵀ = V.map star * Matrix.diagonal ω * Vᵀ := by
    simpa [Matrix.transpose_mul, Matrix.mul_assoc] using congrArg Matrix.transpose hdiagU
  have hUs : U.map star = V.map star * Matrix.diagonal (fun i => star (ω i)) * Vᵀ := by
    simpa [Matrix.conjTranspose, Matrix.mul_assoc, Function.comp_def] using
      congrArg (fun M => M.map star) hdiagU
  have hTensor : Uᵀ ⊗ₖ U.map star = P * D * Q := by
    calc
      Uᵀ ⊗ₖ U.map star =
          (V.map star * Matrix.diagonal ω * Vᵀ) ⊗ₖ
            (V.map star * Matrix.diagonal (fun i => star (ω i)) * Vᵀ) := by
              rw [hUt, hUs]
      _ = ((V.map star * Matrix.diagonal ω) ⊗ₖ
            (V.map star * Matrix.diagonal (fun i => star (ω i)))) * (Vᵀ ⊗ₖ Vᵀ) := by
              rw [mul_kronecker_mul]
      _ = ((V.map star ⊗ₖ V.map star) *
            (Matrix.diagonal ω ⊗ₖ Matrix.diagonal (fun i => star (ω i)))) * (Vᵀ ⊗ₖ Vᵀ) := by
              rw [mul_kronecker_mul]
      _ = P * D * Q := by
              simp [P, D, Q, diagonal_kronecker_diagonal, Matrix.mul_assoc]
  have hDiff :
      (1 : Matrix (d × d) (d × d) ℂ) - (Uᵀ ⊗ₖ U.map star) = P * ((1 : Matrix _ _ ℂ) - D) * Q := by
    calc
      (1 : Matrix (d × d) (d × d) ℂ) - (Uᵀ ⊗ₖ U.map star) = P * Q - P * D * Q := by
        rw [hPQt, hTensor]
      _ = P * Q - P * (D * Q) := by
        simp [Matrix.mul_assoc]
      _ = P * (Q - D * Q) := by
        rw [← Matrix.mul_sub]
      _ = P * (((1 : Matrix (d × d) (d × d) ℂ) - D) * Q) := by
        simp [Matrix.sub_mul]
      _ = P * ((1 : Matrix (d × d) (d × d) ℂ) - D) * Q := by
        simp [Matrix.mul_assoc]
  let E : Matrix (d × d) (d × d) ℂ :=
    Matrix.diagonal fun ij : d × d => 1 - ω ij.1 * star (ω ij.2)
  have hED : (1 : Matrix (d × d) (d × d) ℂ) - D = E := by
    ext i j
    by_cases hij : i = j <;> simp [D, E, hij]
  have hRank :
      ((1 : Matrix (d × d) (d × d) ℂ) - (Uᵀ ⊗ₖ U.map star)).rank ≤ E.rank := by
    rw [hDiff, hED]
    calc
      (P * E * Q).rank ≤ (P * E).rank := by
        simpa [Matrix.mul_assoc] using Matrix.rank_mul_le_left (P * E) Q
      _ ≤ E.rank := Matrix.rank_mul_le_right P E
  exact le_trans hRank (rank_diagonal_tensor_difference_upper_bound ω hω)

/-- The vectorization/Uhlmann part of the positive-gap contradiction, proved locally
    from standard background inputs. -/
private theorem partialTranspose_rank_upper_bound
    {d : Type u} [Fintype d] [DecidableEq d] [Nonempty d]
    {X : Matrix (d × d) (d × d) ℂ} :
    X ≠ 0 →
    Matrix.IsHermitian X →
    Matrix.trace X = 0 →
    partialTraceLeft d d X = 0 →
    X.rank = 2 →
    (partialTransposeMap d d X).rank ≤ Fintype.card (d × d) - Fintype.card d := by
  intro hX0 hXh htr hpt hr
  obtain ⟨c, ψ, φ, hc, hdecomp⟩ :=
    rank_two_traceless_hermitian_decomposition hX0 hXh htr hr
  have hred :
      partialTraceLeft d d (Matrix.vecMulVec ψ (star ψ)) =
        partialTraceLeft d d (Matrix.vecMulVec φ (star φ)) := by
    have hptLin :
        partialTraceLeft d d
            (c • (Matrix.vecMulVec ψ (star ψ) - Matrix.vecMulVec φ (star φ))) =
          c •
            (partialTraceLeft d d (Matrix.vecMulVec ψ (star ψ)) -
              partialTraceLeft d d (Matrix.vecMulVec φ (star φ))) := by
      ext i j
      calc
        (∑ x, c * (Matrix.vecMulVec ψ (star ψ) (x, i) (x, j) -
              Matrix.vecMulVec φ (star φ) (x, i) (x, j))) =
            ∑ x, (c * Matrix.vecMulVec ψ (star ψ) (x, i) (x, j) -
              c * Matrix.vecMulVec φ (star φ) (x, i) (x, j)) := by
                refine Finset.sum_congr rfl ?_
                intro x hx
                ring
        _ = ∑ x, c * Matrix.vecMulVec ψ (star ψ) (x, i) (x, j) -
              ∑ x, c * Matrix.vecMulVec φ (star φ) (x, i) (x, j) := by
                rw [Finset.sum_sub_distrib]
        _ = c * (∑ a, Matrix.vecMulVec ψ (star ψ) (a, i) (a, j) -
              ∑ a, Matrix.vecMulVec φ (star φ) (a, i) (a, j)) := by
                rw [← Finset.mul_sum, ← Finset.mul_sum]
                ring
    have hzero :
        c •
          (partialTraceLeft d d (Matrix.vecMulVec ψ (star ψ)) -
            partialTraceLeft d d (Matrix.vecMulVec φ (star φ))) = 0 := by
      rw [← hptLin]
      simpa [hdecomp] using hpt
    have hsub :
        partialTraceLeft d d (Matrix.vecMulVec ψ (star ψ)) -
          partialTraceLeft d d (Matrix.vecMulVec φ (star φ)) = 0 :=
      (smul_eq_zero.mp hzero).resolve_left hc
    exact sub_eq_zero.mp hsub
  obtain ⟨U, hU, hphi⟩ := uhlmann_theorem_pure ψ φ hred
  let A : Matrix d d ℂ := fun i j => ψ (i, j)
  have hphiA : φ = vecKetGen (U * A) := by
    funext ij
    rw [hphi]
    simp [vecKetGen, A, Matrix.mul_apply]
  let L : Matrix (d × d) (d × d) ℂ := ((1 : Matrix d d ℂ) ⊗ₖ Aᵀ) * swapMatrixGen d
  let R : Matrix (d × d) (d × d) ℂ := (1 : Matrix d d ℂ) ⊗ₖ A.map star
  let M : Matrix (d × d) (d × d) ℂ := (1 : Matrix (d × d) (d × d) ℂ) - (Uᵀ ⊗ₖ U.map star)
  have hKrLeft :
      ((1 : Matrix d d ℂ) ⊗ₖ (Aᵀ * Uᵀ)) =
        (((1 : Matrix d d ℂ) ⊗ₖ Aᵀ) * ((1 : Matrix d d ℂ) ⊗ₖ Uᵀ)) := by
    simpa using
      (mul_kronecker_mul
        (1 : Matrix d d ℂ) (1 : Matrix d d ℂ) Aᵀ Uᵀ)
  have hKrRight :
      ((1 : Matrix d d ℂ) ⊗ₖ (U.map star * A.map star)) =
        (((1 : Matrix d d ℂ) ⊗ₖ U.map star) * ((1 : Matrix d d ℂ) ⊗ₖ A.map star)) := by
    simpa using
      (mul_kronecker_mul
        (1 : Matrix d d ℂ) (1 : Matrix d d ℂ) (U.map star) (A.map star))
  have hKrMiddle :
      ((Uᵀ ⊗ₖ (1 : Matrix d d ℂ)) * ((1 : Matrix d d ℂ) ⊗ₖ U.map star)) =
        (Uᵀ ⊗ₖ U.map star) := by
    simpa using
      (mul_kronecker_mul
        Uᵀ (1 : Matrix d d ℂ) (1 : Matrix d d ℂ) (U.map star)).symm
  have hSecond :
      (((1 : Matrix d d ℂ) ⊗ₖ (U * A)ᵀ) * swapMatrixGen d) *
          ((1 : Matrix d d ℂ) ⊗ₖ (U * A).map star) =
        L * (Uᵀ ⊗ₖ U.map star) * R := by
    calc
      (((1 : Matrix d d ℂ) ⊗ₖ (U * A)ᵀ) * swapMatrixGen d) *
          ((1 : Matrix d d ℂ) ⊗ₖ (U * A).map star)
        = ((((1 : Matrix d d ℂ) ⊗ₖ Aᵀ) * ((1 : Matrix d d ℂ) ⊗ₖ Uᵀ)) *
            swapMatrixGen d) *
            (((1 : Matrix d d ℂ) ⊗ₖ U.map star) * ((1 : Matrix d d ℂ) ⊗ₖ A.map star)) := by
              rw [show (U * A)ᵀ = Aᵀ * Uᵀ by simp [Matrix.transpose_mul]]
              rw [show (U * A).map star = U.map star * A.map star by
                    ext i j
                    simp [Matrix.mul_apply]]
              rw [hKrLeft, hKrRight]
      _ = ((((1 : Matrix d d ℂ) ⊗ₖ Aᵀ) * (((1 : Matrix d d ℂ) ⊗ₖ Uᵀ) * swapMatrixGen d)) *
            ((1 : Matrix d d ℂ) ⊗ₖ U.map star)) *
            ((1 : Matrix d d ℂ) ⊗ₖ A.map star) := by
              simp [Matrix.mul_assoc]
      _ = ((((1 : Matrix d d ℂ) ⊗ₖ Aᵀ) * (swapMatrixGen d * (Uᵀ ⊗ₖ (1 : Matrix d d ℂ)))) *
            ((1 : Matrix d d ℂ) ⊗ₖ U.map star)) *
            ((1 : Matrix d d ℂ) ⊗ₖ A.map star) := by
              rw [← lemma6_gen (d := d) (X := Uᵀ) (Y := (1 : Matrix d d ℂ))]
      _ = ((((1 : Matrix d d ℂ) ⊗ₖ Aᵀ) * swapMatrixGen d) *
            ((Uᵀ ⊗ₖ (1 : Matrix d d ℂ)) * ((1 : Matrix d d ℂ) ⊗ₖ U.map star))) *
            ((1 : Matrix d d ℂ) ⊗ₖ A.map star) := by
              simp [Matrix.mul_assoc]
      _ = ((((1 : Matrix d d ℂ) ⊗ₖ Aᵀ) * swapMatrixGen d) * (Uᵀ ⊗ₖ U.map star)) *
            ((1 : Matrix d d ℂ) ⊗ₖ A.map star) := by
              rw [hKrMiddle]
      _ = L * (Uᵀ ⊗ₖ U.map star) * R := by
              simp [L, R, Matrix.mul_assoc]
  have hFactor :
      partialTransposeMap d d X = c • (L * M * R) := by
    have hdecompA :
        X =
          c •
            (Matrix.vecMulVec (vecKetGen A) (star (vecKetGen A)) -
              Matrix.vecMulVec (vecKetGen (U * A)) (star (vecKetGen (U * A)))) := by
      simpa [vecKetGen, A, hphiA] using hdecomp
    rw [hdecompA]
    have hinner :
        L * R - L * (Uᵀ ⊗ₖ U.map star) * R =
          L * M * R := by
      calc
        L * R - L * (Uᵀ ⊗ₖ U.map star) * R =
            L * R - L * ((Uᵀ ⊗ₖ U.map star) * R) := by
              simp [Matrix.mul_assoc]
        _ = L * (R - (Uᵀ ⊗ₖ U.map star) * R) := by
          rw [← Matrix.mul_sub]
        _ = L * (M * R) := by
          simp [M, Matrix.sub_mul]
        _ = L * M * R := by
          simp [Matrix.mul_assoc]
    calc
      partialTransposeMap d d
          (c •
            (Matrix.vecMulVec (vecKetGen A) (star (vecKetGen A)) -
              Matrix.vecMulVec (vecKetGen (U * A)) (star (vecKetGen (U * A))))) =
          c •
            (partialTransposeMap d d (Matrix.vecMulVec (vecKetGen A) (star (vecKetGen A))) -
              partialTransposeMap d d
                (Matrix.vecMulVec (vecKetGen (U * A)) (star (vecKetGen (U * A))))) := by
              simp
      _ = c •
            ((((1 : Matrix d d ℂ) ⊗ₖ Aᵀ) * swapMatrixGen d) * ((1 : Matrix d d ℂ) ⊗ₖ A.map star) -
              (((1 : Matrix d d ℂ) ⊗ₖ (U * A)ᵀ) * swapMatrixGen d) *
                ((1 : Matrix d d ℂ) ⊗ₖ (U * A).map star)) := by
              rw [lemma7_gen (d := d) A A, lemma7_gen (d := d) (U * A) (U * A)]
      _ = c • (L * M * R) := by
              have hinner' :
                  ((((1 : Matrix d d ℂ) ⊗ₖ Aᵀ) * swapMatrixGen d) *
                      ((1 : Matrix d d ℂ) ⊗ₖ A.map star)) -
                    (((1 : Matrix d d ℂ) ⊗ₖ (U * A)ᵀ) * swapMatrixGen d) *
                      ((1 : Matrix d d ℂ) ⊗ₖ (U * A).map star) =
                    L * M * R := by
                      rw [hSecond]
                      simpa [L, R] using hinner
              exact congrArg (fun Z => c • Z) hinner'
  have hRank :
      (partialTransposeMap d d X).rank ≤ M.rank := by
    rw [hFactor]
    calc
      ((c • (L * M * R))).rank ≤ (L * M * R).rank := by
        simpa [Algebra.smul_def, Matrix.mul_assoc] using
          Matrix.rank_mul_le_right (c • (1 : Matrix (d × d) (d × d) ℂ)) (L * M * R)
      _ ≤ (L * M).rank := by
        simpa [Matrix.mul_assoc] using Matrix.rank_mul_le_left (L * M) R
      _ ≤ M.rank := Matrix.rank_mul_le_right L M
  exact le_trans hRank (rank_tensor_difference_upper_bound U hU)

/-- The strictness theorem for Theorem 1 in finite dimensions, proved from the paper's
    maximizer and Uhlmann/rank-bound background inputs. -/
theorem theorem_not_tight
    {d : Type u} [Fintype d] [DecidableEq d] [Nonempty d]
    (T : Channel d) (hT : IsQuantumChannel T) (hΦ : idMinus T ≠ 0) :
    diamondOp ((transposeMap d).comp (idMinus T))
      < (1 / Real.sqrt 2) * diamondOp (transposeMap d) * diamondOp (idMinus T) := by
  refine lt_of_le_of_ne (theorem1 T hT) ?_
  intro hEq
  let Φ : Channel d := idMinus T
  let LΦ : Channel d := (transposeMap d).comp Φ
  obtain ⟨ρ, hYmax, hXnonzero⟩ := exists_maximizing_state T hT hΦ
  let X : Matrix (d × d) (d × d) ℂ := tensorWithIdentity d d Φ ρ.1
  let Y : Matrix (d × d) (d × d) ℂ := partialTransposeMap d d X
  have hrewrite : tensorWithIdentity d d LΦ ρ.1 = Y := by
    simpa [LΦ, Φ, X, Y, LinearMap.comp_apply] using
      congrArg (fun Ψ : Channel (d × d) => Ψ ρ.1)
        (tensorWithIdentity_comp_transpose (d := d) (k := d) (Φ := Φ))
  have hYmax : traceNormOp Y = diamondOp LΦ := by
    simpa [Y, hrewrite] using hYmax
  have hTraceX : Matrix.trace X = 0 := by
    simpa [X, Φ] using
      tensorWithIdentity_trace_zero (d := d) (k := d)
        (idMinus T) (idMinus_isTraceAnnihilating T hT) ρ.1
  have hHermX : Matrix.IsHermitian X := by
    simpa [X, Φ] using
      tensorWithIdentity_hermitian (d := d) (k := d)
        (Ψ := idMinus T) (idMinus_isHermiticityPreserving T hT) ρ.1 ρ.2
  have hPartialTraceX : partialTraceLeft d d X = 0 := by
    simpa [X, Φ] using corollary1 T hT ρ.1
  have hYnonzero : Y ≠ 0 := by
    exact partialTranspose_ne_zero_of_ne_zero (d := d) (k := d) hXnonzero
  have hYle :
      traceNormOp Y ≤ Real.sqrt (Fintype.card (d × d) : ℝ) * hsNormOp X := by
    have htmp :
        traceNormOp Y ≤ Real.sqrt (Fintype.card (d × d) : ℝ) * hsNormOp Y := by
      simpa [Y] using lemma2 (Y := Y)
    have hpt : hsNormOp Y = hsNormOp X := by
      simpa [X, Y] using lemma3 (d := d) (k := d) X
    simpa [hpt] using htmp
  have hXle : hsNormOp X ≤ (1 / Real.sqrt 2) * traceNormOp X := by
    simpa [X] using lemma1 (X := X) hHermX hTraceX
  have hRle : traceNormOp X ≤ diamondOp Φ := by
    simpa [X, Φ, diamondOp] using
      traceNorm_apply_le_diamond (d := d) (k := d) (Φ := Φ) (ρ := ρ)
  have hYtarget :
      traceNormOp Y =
        Real.sqrt (Fintype.card (d × d) : ℝ) * ((1 / Real.sqrt 2) * diamondOp Φ) := by
    calc
      traceNormOp Y = diamondOp LΦ := hYmax
      _ = (1 / Real.sqrt 2) * diamondOp (transposeMap d) * diamondOp Φ := by
        simpa [LΦ, Φ] using hEq
      _ = Real.sqrt (Fintype.card (d × d) : ℝ) * ((1 / Real.sqrt 2) * diamondOp Φ) := by
        rw [lemma_transpose_diamond (d := d)]
        ring
  have hYeq : traceNormOp Y = Real.sqrt (Fintype.card (d × d) : ℝ) * hsNormOp X := by
    apply le_antisymm hYle
    calc
      Real.sqrt (Fintype.card (d × d) : ℝ) * hsNormOp X
          ≤ Real.sqrt (Fintype.card (d × d) : ℝ) * ((1 / Real.sqrt 2) * diamondOp Φ) := by
            apply mul_le_mul_of_nonneg_left
            · exact le_trans hXle (mul_le_mul_of_nonneg_left hRle (by positivity))
            · exact Real.sqrt_nonneg _
      _ = traceNormOp Y := by
        symm
        exact hYtarget
  have hsqrt_pos : 0 < Real.sqrt (Fintype.card (d × d) : ℝ) := by
    positivity
  have hhs_eq : hsNormOp X = (1 / Real.sqrt 2) * diamondOp Φ := by
    nlinarith [hYeq, hYtarget, hsqrt_pos]
  have htrace_ge : diamondOp Φ ≤ traceNormOp X := by
    have hscaled : (1 / Real.sqrt 2) * diamondOp Φ ≤ (1 / Real.sqrt 2) * traceNormOp X := by
      simpa [hhs_eq] using hXle
    have hfac : 0 < (1 / Real.sqrt 2 : ℝ) := by positivity
    exact le_of_mul_le_mul_left hscaled hfac
  have htrace_eq : traceNormOp X = diamondOp Φ := by
    exact le_antisymm hRle htrace_ge
  have hlemma1eq : hsNormOp X = (1 / Real.sqrt 2) * traceNormOp X := by
    calc
      hsNormOp X = (1 / Real.sqrt 2) * diamondOp Φ := hhs_eq
      _ = (1 / Real.sqrt 2) * traceNormOp X := by rw [htrace_eq]
  have hlemma2eq :
      traceNormOp Y = Real.sqrt (Fintype.card (d × d) : ℝ) * hsNormOp Y := by
    have hpt : hsNormOp Y = hsNormOp X := by
      simpa [X, Y] using lemma3 (d := d) (k := d) X
    simpa [hpt] using hYeq
  have hrankX : X.rank = 2 :=
    lemma1_eq_imp_rank_two hHermX hTraceX hXnonzero hlemma1eq
  have hrankY : Y.rank = Fintype.card (d × d) :=
    lemma2_eq_imp_full_rank (d := d) (Y := Y) hYnonzero hlemma2eq
  have hupper : Y.rank ≤ Fintype.card (d × d) - Fintype.card d := by
    simpa [X, Y] using
      partialTranspose_rank_upper_bound (d := d) hXnonzero hHermX hTraceX hPartialTraceX hrankX
  have hd_pos : 0 < Fintype.card d := Fintype.card_pos_iff.mpr inferInstance
  have hlt : Fintype.card (d × d) - Fintype.card d < Fintype.card (d × d) := by
    exact Nat.sub_lt (by positivity) hd_pos
  have : Fintype.card (d × d) < Fintype.card (d × d) := by
    simpa [hrankY] using lt_of_le_of_lt hupper hlt
  exact (lt_irrefl _ this).elim

end
end Diamond
