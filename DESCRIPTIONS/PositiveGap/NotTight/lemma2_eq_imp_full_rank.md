---
layout: default
---

# lemma2_eq_imp_full_rank

## Source location

- Original Lean file: `Diamond/PositiveGap/NotTight.lean`
- Declaration name: `lemma2_eq_imp_full_rank`
- Declaration kind: `theorem`

## Why this declaration exists

This theorem identifies the equality case of Lemma 2: saturation forces full rank.

 In the file `PositiveGap/NotTight.lean`, it contributes to the finite-dimensional non-tightness argument and the equality-case analysis behind it. Later proofs call this result by name, so documenting it makes the larger argument readable as a mathematical chain rather than as opaque proof script.

## Original code

```lean
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
