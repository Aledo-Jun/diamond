# traceNormOp_diagonal

## Source location

- Original Lean file: `Diamond/Theorem/Lemma1.lean`
- Declaration name: `traceNormOp_diagonal`
- Declaration kind: `theorem`

## Why this declaration exists

Trace norm of a diagonal matrix is the sum of the absolute values of its diagonal entries.

 In the file `Theorem/Lemma1.lean`, it contributes to the proof infrastructure for the first norm inequality and the public theorem `lemma1`. Later proofs call this result by name, so documenting it makes the larger argument readable as a mathematical chain rather than as opaque proof script.

## Original code

```lean
/-- Trace norm of a diagonal matrix is the sum of the absolute values of its diagonal entries. -/
theorem traceNormOp_diagonal
    {d : Type u} [Fintype d] [DecidableEq d] (z : d → ℂ) :
    traceNormOp (Matrix.diagonal z) = ∑ i, ‖z i‖ := by
  let hDiag :
      Matrix.IsHermitian
        (Matrix.diagonal fun i => ((Complex.normSq (z i) : ℂ))) :=
    Matrix.isHermitian_diagonal_of_self_adjoint
      (fun i => ((Complex.normSq (z i) : ℂ))) (by
        ext i
        simp)
  have hmat :
      (Matrix.diagonal z)ᴴ * Matrix.diagonal z =
        Matrix.diagonal fun i => ((Complex.normSq (z i) : ℂ)) := by
    ext i j
    by_cases hij : i = j
    · subst hij
      simp [Complex.normSq_eq_conj_mul_self]
    · simp [hij]
  have hEig :
      (Matrix.isHermitian_conjTranspose_mul_self (Matrix.diagonal z)).eigenvalues =
        hDiag.eigenvalues := by
    apply
      (Matrix.IsHermitian.eigenvalues_eq_eigenvalues_iff
        (Matrix.isHermitian_conjTranspose_mul_self (Matrix.diagonal z))
        hDiag).2
    exact congrArg Matrix.charpoly hmat
  dsimp [traceNormOp, traceNorm]
  rw [hEig]
  have hmultiset :
      Multiset.map hDiag.eigenvalues Finset.univ.val =
        Multiset.map (fun i => Complex.normSq (z i)) Finset.univ.val := by
    have hroots :
        Multiset.map Complex.re
            ((Matrix.diagonal fun i => ((Complex.normSq (z i) : ℂ))).charpoly.roots) =
          Multiset.map (fun i => Complex.normSq (z i)) Finset.univ.val := by
      rw [show
            (Matrix.diagonal fun i => ((Complex.normSq (z i) : ℂ))).charpoly.roots =
              Multiset.map (fun i => ((Complex.normSq (z i) : ℂ))) Finset.univ.val by
            simpa [Matrix.charpoly_diagonal] using
              (Polynomial.roots_multiset_prod_X_sub_C
                (s := Multiset.map
                  (fun i => ((Complex.normSq (z i) : ℂ))) Finset.univ.val))]
      simp
    rw [Matrix.IsHermitian.roots_charpoly_eq_eigenvalues hDiag] at hroots
    simpa [Multiset.map_map, Function.comp_def] using hroots
  have hsqrt := congrArg (Multiset.map Real.sqrt) hmultiset
  have hsum :
      ∑ i, Real.sqrt (hDiag.eigenvalues i) =
        ∑ i, Real.sqrt (Complex.normSq (z i)) := by
    simpa [Multiset.map_map] using congrArg Multiset.sum hsqrt
  simpa [RCLike.sqrt_normSq_eq_norm] using hsum
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
