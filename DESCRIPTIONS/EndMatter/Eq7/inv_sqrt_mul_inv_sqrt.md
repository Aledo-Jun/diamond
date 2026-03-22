# inv_sqrt_mul_inv_sqrt

## Source location

- Original Lean file: `Diamond/EndMatter/Eq7.lean`
- Declaration name: `inv_sqrt_mul_inv_sqrt`
- Declaration kind: `theorem`

## Why this declaration exists

This theorem records a reusable fact named `inv_sqrt_mul_inv_sqrt`. Its role is to make the later proof flow easier to state and reuse.

 In the file `EndMatter/Eq7.lean`, it contributes to the explicit witness construction used to prove the lower bound labelled Eq. (7). Later proofs call this result by name, so documenting it makes the larger argument readable as a mathematical chain rather than as opaque proof script.

## Original code

```lean
theorem inv_sqrt_mul_inv_sqrt (d : ℕ) [Fact (1 < d)] :
    ((Real.sqrt d : ℂ)⁻¹) * ((Real.sqrt d : ℂ)⁻¹) = (d : ℂ)⁻¹ := by
  have hd_pos_nat : 0 < d := lt_trans Nat.zero_lt_one ‹Fact (1 < d)›.out
  have hd_pos : (0 : ℝ) < d := by
    exact_mod_cast hd_pos_nat
  have hsqrt_neR : (Real.sqrt d : ℝ) ≠ 0 := by
    exact (Real.sqrt_ne_zero').2 hd_pos
  have hsqrt_ne : (Real.sqrt d : ℂ) ≠ 0 := by
    exact_mod_cast hsqrt_neR
  calc
    ((Real.sqrt d : ℂ)⁻¹) * ((Real.sqrt d : ℂ)⁻¹)
        = ((Real.sqrt d : ℂ) ^ 2)⁻¹ := by
          field_simp [hsqrt_ne]
    _ = (d : ℂ)⁻¹ := by
      congr 1
      exact_mod_cast Real.sq_sqrt (show 0 ≤ (d : ℝ) by positivity)
```

## Block-by-block explanation

The explanation below follows the declaration block by block. Each block groups a coherent piece of the definition or proof, so the mathematical structure is easier to see than in a strictly line-oriented reading.

1. Code:
```lean
theorem inv_sqrt_mul_inv_sqrt (d : ℕ) [Fact (1 < d)] :
```
This line starts the `inv_sqrt_mul_inv_sqrt` declaration. Because it begins with `theorem`, Lean now knows what kind of named object is being introduced.

2. Code:
```lean
    ((Real.sqrt d : ℂ)⁻¹) * ((Real.sqrt d : ℂ)⁻¹) = (d : ℂ)⁻¹ := by
```
This line says that a proof script begins here. Everything indented underneath is a sequence of instructions that Lean will check step by step.

3. Code:
```lean
  have hd_pos_nat : 0 < d := lt_trans Nat.zero_lt_one ‹Fact (1 < d)›.out
```
This line introduces an intermediate claim. The proof pauses to establish a fact that will be used shortly afterwards.

4. Code:
```lean
  have hd_pos : (0 : ℝ) < d := by
```
This line says that a proof script begins here. Everything indented underneath is a sequence of instructions that Lean will check step by step.

5. Code:
```lean
    exact_mod_cast hd_pos_nat
```
This line finishes the current goal by giving Lean the exact theorem, lemma, or term that proves it.

6. Code:
```lean
  have hsqrt_neR : (Real.sqrt d : ℝ) ≠ 0 := by
```
This line says that a proof script begins here. Everything indented underneath is a sequence of instructions that Lean will check step by step.

7. Code:
```lean
    exact (Real.sqrt_ne_zero').2 hd_pos
```
This line finishes the current goal by giving Lean the exact theorem, lemma, or term that proves it.

8. Code:
```lean
  have hsqrt_ne : (Real.sqrt d : ℂ) ≠ 0 := by
```
This line says that a proof script begins here. Everything indented underneath is a sequence of instructions that Lean will check step by step.

9. Code:
```lean
    exact_mod_cast hsqrt_neR
```
This line finishes the current goal by giving Lean the exact theorem, lemma, or term that proves it.

10. Code:
```lean
  calc
```
This line begins a chained calculation. Each displayed step that follows must be justified by the indented proof after `:= by`.

11. Code:
```lean
    ((Real.sqrt d : ℂ)⁻¹) * ((Real.sqrt d : ℂ)⁻¹)
```
This line is one local step in the declaration. It either refines the formula being defined or advances the proof by a small algebraic or logical move.

12. Code:
```lean
        = ((Real.sqrt d : ℂ) ^ 2)⁻¹ := by
```
This line says that a proof script begins here. Everything indented underneath is a sequence of instructions that Lean will check step by step.

13. Code:
```lean
          field_simp [hsqrt_ne]
```
This line is one local step in the declaration. It either refines the formula being defined or advances the proof by a small algebraic or logical move.

14. Code:
```lean
    _ = (d : ℂ)⁻¹ := by
```
This line says that a proof script begins here. Everything indented underneath is a sequence of instructions that Lean will check step by step.

15. Code:
```lean
      congr 1
```
This line is one local step in the declaration. It either refines the formula being defined or advances the proof by a small algebraic or logical move.

16. Code:
```lean
      exact_mod_cast Real.sq_sqrt (show 0 ≤ (d : ℝ) by positivity)
```
This line finishes the current goal by giving Lean the exact theorem, lemma, or term that proves it.

## Mathematical summary

Restated without Lean syntax, `inv_sqrt_mul_inv_sqrt` is the theorem or lemma written above.

- State the desired identity or inequality in Lean’s syntax.
- Introduce temporary names and intermediate claims that organize the argument.
- Use rewriting, simplification, and earlier lemmas to reduce the goal to standard matrix or norm manipulations.
- Close the remaining algebraic or order-theoretic steps with Lean’s proof tactics.

## Dependencies and downstream use

### Earlier declarations this depends on
- This declaration does not explicitly cite an earlier named declaration from the documented tree; it mostly uses Lean primitives or local algebraic steps.

### Later declarations that use this one
- [`phiState_trace`](phiState_trace.md) in `EndMatter/Eq7.lean`
- [`phiState_apply`](phiState_apply.md) in `EndMatter/Eq7.lean`

## Backlinks

- [Back to `INDEX.md`](../../INDEX.md)
- [Back to the `EndMatter/Eq7.lean` section in the index](../../INDEX.md#diamond-endmatter-eq7-lean)
- [Previous declaration in this file](phiState.md)
- [Next declaration in this file](phiState_trace.md)