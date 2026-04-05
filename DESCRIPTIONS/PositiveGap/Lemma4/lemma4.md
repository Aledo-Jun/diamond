---
layout: default
---

# lemma4

## Source location

- Original Lean file: `Diamond/PositiveGap/Lemma4.lean`
- Declaration name: `lemma4`
- Declaration kind: `theorem`

## Why this declaration exists

This lemma proves that tensoring a quantum channel with the identity does not change the partial trace over the channel side.

 In the file `PositiveGap/Lemma4.lean`, it contributes to the partial-trace identity for tensoring a quantum channel with the identity. Later proofs call this result by name, so documenting it makes the larger argument readable as a mathematical chain rather than as opaque proof script.

## Original code

```lean
/-- Paper Lemma 4: partial trace on the left is unchanged by tensoring with a quantum channel. -/
theorem lemma4
    {d : Type u} [Fintype d] [DecidableEq d]
    (T : Channel d) (hT : IsQuantumChannel T)
    {k : Type u} [Fintype k] [DecidableEq k]
    (Z : Matrix (d × k) (d × k) ℂ) :
    partialTraceLeft d k (tensorWithIdentity d k T Z) = partialTraceLeft d k Z := by
  obtain ⟨r, E, hmap, hcomplete⟩ := quantumChannel_has_kraus (T := T) hT
  ext i j
  let A : Matrix d d ℂ := fun a b => Z (a, i) (b, j)
  calc
    partialTraceLeft d k (tensorWithIdentity d k T Z) i j = Matrix.trace (T A) := by
      simp [partialTraceLeft, tensorWithIdentity, A, Matrix.trace]
    _ = Matrix.trace (∑ n : Fin r, E n * A * (E n)ᴴ) := by
      simp [hmap]
    _ = ∑ n : Fin r, Matrix.trace (E n * A * (E n)ᴴ) := by
      simpa using (Matrix.trace_sum (s := (Finset.univ : Finset (Fin r)))
        (f := fun n => E n * A * (E n)ᴴ))
    _ = ∑ n : Fin r, Matrix.trace (A * ((E n)ᴴ * E n)) := by
      refine Finset.sum_congr rfl ?_
      intro n hn
      calc
        Matrix.trace (E n * A * (E n)ᴴ)
            = Matrix.trace (((E n)ᴴ * E n) * A) := by
              simpa [Matrix.mul_assoc] using (Matrix.trace_mul_cycle (E n) A (E n)ᴴ)
        _ = Matrix.trace (A * ((E n)ᴴ * E n)) := by
              simpa [Matrix.mul_assoc] using (Matrix.trace_mul_comm ((E n)ᴴ * E n) A)
    _ = Matrix.trace (∑ n : Fin r, A * ((E n)ᴴ * E n)) := by
      simpa using
        (Matrix.trace_sum (s := (Finset.univ : Finset (Fin r))
          )
          (f := fun n => A * ((E n)ᴴ * E n))).symm
    _ = Matrix.trace (A * (∑ n : Fin r, (E n)ᴴ * E n)) := by
      simp [Matrix.mul_sum]
    _ = Matrix.trace (A * 1) := by
      rw [hcomplete]
    _ = partialTraceLeft d k Z i j := by
      simp [A, partialTraceLeft, Matrix.trace]
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
