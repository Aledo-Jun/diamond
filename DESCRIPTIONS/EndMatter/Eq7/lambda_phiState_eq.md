# lambda_phiState_eq

## Source location

- Original Lean file: `Diamond/EndMatter/Eq7.lean`
- Declaration name: `lambda_phiState_eq`
- Declaration kind: `theorem`

## Why this declaration exists

Explicit formula for `((Λ_d ⊗ id) (Φ_d))` in matrix form.

 In the file `EndMatter/Eq7.lean`, it contributes to the explicit witness construction used to prove the lower bound labelled Eq. (7). Later proofs call this result by name, so documenting it makes the larger argument readable as a mathematical chain rather than as opaque proof script.

## Original code

```lean
/-- Explicit formula for `((Λ_d ⊗ id) (Φ_d))` in matrix form. -/
theorem lambda_phiState_eq (d : ℕ) [Fact (1 < d)] :
    tensorWithIdentity (Fin d) (Fin d) (Lambda d) (phiState d) =
      (d : ℂ)⁻¹ •
        (swapMatrix d - swapMatrix d * ((Ud d)ᵀ ⊗ₖ star (Ud d))) := by
  calc
    tensorWithIdentity (Fin d) (Fin d) (Lambda d) (phiState d)
      =
        tensorWithIdentity (Fin d) (Fin d) (transposeMap (Fin d)) (phiState d) -
          tensorWithIdentity
            (Fin d)
            (Fin d)
            ((transposeMap (Fin d)).comp (adMap (Fin d) (Ud d)))
            (phiState d) := by
              ext i j
              simp [Lambda, idMinus, tensorWithIdentity, transposeMap, adMap,
                LinearMap.comp_apply]
    _ =
        (d : ℂ)⁻¹ • swapMatrix d -
          (d : ℂ)⁻¹ • (swapMatrix d * ((Ud d)ᵀ ⊗ₖ star (Ud d))) := by
            rw [transpose_phiState_eq_swap, transpose_ad_phiState_eq_swap_mul_phase]
    _ =
        (d : ℂ)⁻¹ •
          (swapMatrix d - swapMatrix d * ((Ud d)ᵀ ⊗ₖ star (Ud d))) := by
            simp [smul_sub]
```

## Line-by-line explanation

The explanation below follows the declaration one physical line at a time. For long proofs, some lines are tiny bookkeeping steps; those are still explained, but briefly.

1. Code:
```lean
/-- Explicit formula for `((Λ_d ⊗ id) (Φ_d))` in matrix form. -/
```
This is a Lean docstring. It is a human-written comment that tells readers what the declaration is meant to express before the formal code begins.

2. Code:
```lean
theorem lambda_phiState_eq (d : ℕ) [Fact (1 < d)] :
```
This line starts the `lambda_phiState_eq` declaration. Because it begins with `theorem`, Lean now knows what kind of named object is being introduced.

3. Code:
```lean
    tensorWithIdentity (Fin d) (Fin d) (Lambda d) (phiState d) =
```
This line is one local step in the declaration. It either refines the formula being defined or advances the proof by a small algebraic or logical move.

4. Code:
```lean
      (d : ℂ)⁻¹ •
```
This line is one local step in the declaration. It either refines the formula being defined or advances the proof by a small algebraic or logical move.

5. Code:
```lean
        (swapMatrix d - swapMatrix d * ((Ud d)ᵀ ⊗ₖ star (Ud d))) := by
```
This line says that a proof script begins here. Everything indented underneath is a sequence of instructions that Lean will check step by step.  `Matrix d d ℂ` means a square matrix with complex entries; the index type `d` tells Lean which rows and columns exist.  The symbol `⊗ₖ` is the Kronecker (tensor) product of matrices.  The superscript `ᵀ` means ordinary transpose.

6. Code:
```lean
  calc
```
This line begins a chained calculation. Each displayed step that follows must be justified by the indented proof after `:= by`.

7. Code:
```lean
    tensorWithIdentity (Fin d) (Fin d) (Lambda d) (phiState d)
```
This line is one local step in the declaration. It either refines the formula being defined or advances the proof by a small algebraic or logical move.

8. Code:
```lean
      =
```
This line is one local step in the declaration. It either refines the formula being defined or advances the proof by a small algebraic or logical move.

9. Code:
```lean
        tensorWithIdentity (Fin d) (Fin d) (transposeMap (Fin d)) (phiState d) -
```
This line is one local step in the declaration. It either refines the formula being defined or advances the proof by a small algebraic or logical move.

10. Code:
```lean
          tensorWithIdentity
```
This line is one local step in the declaration. It either refines the formula being defined or advances the proof by a small algebraic or logical move.

11. Code:
```lean
            (Fin d)
```
This line is one local step in the declaration. It either refines the formula being defined or advances the proof by a small algebraic or logical move.

12. Code:
```lean
            (Fin d)
```
This line is one local step in the declaration. It either refines the formula being defined or advances the proof by a small algebraic or logical move.

13. Code:
```lean
            ((transposeMap (Fin d)).comp (adMap (Fin d) (Ud d)))
```
This line is one local step in the declaration. It either refines the formula being defined or advances the proof by a small algebraic or logical move.  `comp` means composition of maps: one map is applied after another.

14. Code:
```lean
            (phiState d) := by
```
This line says that a proof script begins here. Everything indented underneath is a sequence of instructions that Lean will check step by step.

15. Code:
```lean
              ext i j
```
This line invokes extensionality. To prove two maps or matrices are equal, Lean reduces the problem to checking their values entry by entry.

16. Code:
```lean
              simp [Lambda, idMinus, tensorWithIdentity, transposeMap, adMap,
```
This line simplifies the goal using definitions and known equalities. `simpa` means that, after simplification, the desired statement matches a theorem Lean already has.

17. Code:
```lean
                LinearMap.comp_apply]
```
This line is one local step in the declaration. It either refines the formula being defined or advances the proof by a small algebraic or logical move.  `comp` means composition of maps: one map is applied after another.  `LinearMap.comp` is composition of linear maps.

18. Code:
```lean
    _ =
```
This line is one step inside a `calc` block. Lean is checking that the new expression really follows from the previous one.

19. Code:
```lean
        (d : ℂ)⁻¹ • swapMatrix d -
```
This line is one local step in the declaration. It either refines the formula being defined or advances the proof by a small algebraic or logical move.  `Matrix d d ℂ` means a square matrix with complex entries; the index type `d` tells Lean which rows and columns exist.

20. Code:
```lean
          (d : ℂ)⁻¹ • (swapMatrix d * ((Ud d)ᵀ ⊗ₖ star (Ud d))) := by
```
This line says that a proof script begins here. Everything indented underneath is a sequence of instructions that Lean will check step by step.  `Matrix d d ℂ` means a square matrix with complex entries; the index type `d` tells Lean which rows and columns exist.  The symbol `⊗ₖ` is the Kronecker (tensor) product of matrices.  The superscript `ᵀ` means ordinary transpose.

21. Code:
```lean
            rw [transpose_phiState_eq_swap, transpose_ad_phiState_eq_swap_mul_phase]
```
This line uses rewriting. Lean replaces one expression by an equal expression using the lemmas listed in brackets.

22. Code:
```lean
    _ =
```
This line is one step inside a `calc` block. Lean is checking that the new expression really follows from the previous one.

23. Code:
```lean
        (d : ℂ)⁻¹ •
```
This line is one local step in the declaration. It either refines the formula being defined or advances the proof by a small algebraic or logical move.

24. Code:
```lean
          (swapMatrix d - swapMatrix d * ((Ud d)ᵀ ⊗ₖ star (Ud d))) := by
```
This line says that a proof script begins here. Everything indented underneath is a sequence of instructions that Lean will check step by step.  `Matrix d d ℂ` means a square matrix with complex entries; the index type `d` tells Lean which rows and columns exist.  The symbol `⊗ₖ` is the Kronecker (tensor) product of matrices.  The superscript `ᵀ` means ordinary transpose.

25. Code:
```lean
            simp [smul_sub]
```
This line simplifies the goal using definitions and known equalities. `simpa` means that, after simplification, the desired statement matches a theorem Lean already has.

## Mathematical summary

Restated without Lean syntax, `lambda_phiState_eq` is the theorem or lemma written above.

- State the desired identity or inequality in Lean’s syntax.
- Introduce temporary names and intermediate claims that organize the argument.
- Use rewriting, simplification, and earlier lemmas to reduce the goal to standard matrix or norm manipulations.
- Close the remaining algebraic or order-theoretic steps with Lean’s proof tactics.

## Dependencies and downstream use

### Earlier declarations this depends on
- [`transposeMap`](../../Setups/transposeMap.md) from `Setups.lean`
- [`tensorWithIdentity`](../../Setups/tensorWithIdentity.md) from `Setups.lean`
- [`idMinus`](../../Setups/idMinus.md) from `Setups.lean`
- [`adMap`](../../Setups/adMap.md) from `Setups.lean`
- [`Ud`](../../Setups/Ud.md) from `Setups.lean`
- [`Lambda`](../../Setups/Lambda.md) from `Setups.lean`
- [`swapMatrix`](../../PositiveGap/Lemma6/swapMatrix.md) from `PositiveGap/Lemma6.lean`
- [`phiState`](phiState.md) from `EndMatter/Eq7.lean`
- [`transpose_phiState_eq_swap`](transpose_phiState_eq_swap.md) from `EndMatter/Eq7.lean`
- [`transpose_ad_phiState_eq_swap_mul_phase`](transpose_ad_phiState_eq_swap_mul_phase.md) from `EndMatter/Eq7.lean`

### Later declarations that use this one
- [`theorem_eq7_witness_bound_explicit`](theorem_eq7_witness_bound_explicit.md) in `EndMatter/Eq7.lean`

## Backlinks

- [Back to `INDEX.md`](../../INDEX.md)
- [Back to the `EndMatter/Eq7.lean` section in the index](../../INDEX.md#diamond-endmatter-eq7-lean)
- [Previous declaration in this file](transpose_ad_phiState_eq_swap_mul_phase.md)
- [Next declaration in this file](theorem_eq7_witness_bound.md)