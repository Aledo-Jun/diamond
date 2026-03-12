# theorem_eq7

## Source location

- Original Lean file: `Diamond/EndMatter/Eq7.lean`
- Declaration name: `theorem_eq7`
- Declaration kind: `theorem`

## Why this declaration exists

This theorem proves the lower bound labelled Eq. (7) by evaluating the witness state explicitly.

 In the file `EndMatter/Eq7.lean`, it contributes to the explicit witness construction used to prove the lower bound labelled Eq. (7). Later proofs call this result by name, so documenting it makes the larger argument readable as a mathematical chain rather than as opaque proof script.

## Original code

```lean
/-- Paper Eq. (7): lower bound on `‖Λ_d‖⋄`. -/
theorem theorem_eq7 (d : ℕ) [Fact (1 < d)] :
    2 * Real.cot (Real.pi / (2 * (d : ℝ))) ≤ diamondOp (Lambda d) := by
  calc
    2 * Real.cot (Real.pi / (2 * (d : ℝ)))
      = traceNormOp
          ((d : ℂ)⁻¹ •
            (swapMatrix d - swapMatrix d * ((Ud d)ᵀ ⊗ₖ star (Ud d)))) := by
              symm
              exact explicit_witness_traceNorm_eq d
    _ ≤ diamondOp (Lambda d) := theorem_eq7_witness_bound_explicit d
```

## Line-by-line explanation

The explanation below follows the declaration one physical line at a time. For long proofs, some lines are tiny bookkeeping steps; those are still explained, but briefly.

1. Code:
```lean
/-- Paper Eq. (7): lower bound on `‖Λ_d‖⋄`. -/
```
This is a Lean docstring. It is a human-written comment that tells readers what the declaration is meant to express before the formal code begins.

2. Code:
```lean
theorem theorem_eq7 (d : ℕ) [Fact (1 < d)] :
```
This line starts the `theorem_eq7` declaration. Because it begins with `theorem`, Lean now knows what kind of named object is being introduced.

3. Code:
```lean
    2 * Real.cot (Real.pi / (2 * (d : ℝ))) ≤ diamondOp (Lambda d) := by
```
This line says that a proof script begins here. Everything indented underneath is a sequence of instructions that Lean will check step by step.

4. Code:
```lean
  calc
```
This line begins a chained calculation. Each displayed step that follows must be justified by the indented proof after `:= by`.

5. Code:
```lean
    2 * Real.cot (Real.pi / (2 * (d : ℝ)))
```
This line is one local step in the declaration. It either refines the formula being defined or advances the proof by a small algebraic or logical move.

6. Code:
```lean
      = traceNormOp
```
This line is one local step in the declaration. It either refines the formula being defined or advances the proof by a small algebraic or logical move.

7. Code:
```lean
          ((d : ℂ)⁻¹ •
```
This line is one local step in the declaration. It either refines the formula being defined or advances the proof by a small algebraic or logical move.

8. Code:
```lean
            (swapMatrix d - swapMatrix d * ((Ud d)ᵀ ⊗ₖ star (Ud d)))) := by
```
This line says that a proof script begins here. Everything indented underneath is a sequence of instructions that Lean will check step by step.  `Matrix d d ℂ` means a square matrix with complex entries; the index type `d` tells Lean which rows and columns exist.  The symbol `⊗ₖ` is the Kronecker (tensor) product of matrices.  The superscript `ᵀ` means ordinary transpose.

9. Code:
```lean
              symm
```
This line is one local step in the declaration. It either refines the formula being defined or advances the proof by a small algebraic or logical move.

10. Code:
```lean
              exact explicit_witness_traceNorm_eq d
```
This line finishes the current goal by giving Lean the exact theorem, lemma, or term that proves it.

11. Code:
```lean
    _ ≤ diamondOp (Lambda d) := theorem_eq7_witness_bound_explicit d
```
This line is one step inside a `calc` block. Lean is checking that the new expression really follows from the previous one.

## Mathematical summary

Restated without Lean syntax, `theorem_eq7` is the theorem or lemma written above.

- Build the maximally entangled witness state $\Phi_d = |\Omega_d\rangle\langle\Omega_d|$.
- Compute explicitly what `Lambda d` does to that witness.
- Recognize the result as a swap matrix multiplied by a diagonal phase matrix.
- Evaluate the trace norm of that explicit matrix by reducing it to a finite trigonometric sum.
- Use the witness inequality to conclude the diamond norm lower bound.

## Dependencies and downstream use

### Earlier declarations this depends on
- [`traceNormOp`](../../Setups/traceNormOp.md) from `Setups.lean`
- [`diamondOp`](../../Setups/diamondOp.md) from `Setups.lean`
- [`Ud`](../../Setups/Ud.md) from `Setups.lean`
- [`Lambda`](../../Setups/Lambda.md) from `Setups.lean`
- [`swapMatrix`](../../PositiveGap/Lemma6/swapMatrix.md) from `PositiveGap/Lemma6.lean`
- [`theorem_eq7_witness_bound_explicit`](theorem_eq7_witness_bound_explicit.md) from `EndMatter/Eq7.lean`
- [`explicit_witness_traceNorm_eq`](explicit_witness_traceNorm_eq.md) from `EndMatter/Eq7.lean`

### Later declarations that use this one
- [`alpha_lower_bound`](../Eq8/alpha_lower_bound.md) in `EndMatter/Eq8.lean`

## Backlinks

- [Back to `INDEX.md`](../../INDEX.md)
- [Back to the `EndMatter/Eq7.lean` section in the index](../../INDEX.md#diamond-endmatter-eq7-lean)
- [Previous declaration in this file](explicit_witness_traceNorm_eq.md)