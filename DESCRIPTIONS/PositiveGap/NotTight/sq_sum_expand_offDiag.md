# sq_sum_expand_offDiag

## Source location

- Original Lean file: `Diamond/PositiveGap/NotTight.lean`
- Declaration name: `sq_sum_expand_offDiag`
- Declaration kind: `lemma`

## Why this declaration exists

Expand a square of a finite sum into diagonal and off-diagonal parts.

 In the file `PositiveGap/NotTight.lean`, it contributes to the finite-dimensional non-tightness argument and the equality-case analysis behind it. Later proofs call this result by name, so documenting it makes the larger argument readable as a mathematical chain rather than as opaque proof script.

## Original code

```lean
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
```

## Block-by-block explanation

The explanation below follows the declaration block by block. Each block groups a coherent piece of the definition or proof, so the mathematical structure is easier to see than in a strictly line-oriented reading.

1. Code:
```lean
/-- Expand a square of a finite sum into diagonal and off-diagonal parts. -/
```
This is a Lean docstring. It is a human-written comment that tells readers what the declaration is meant to express before the formal code begins.

2. Code:
```lean
private lemma sq_sum_expand_offDiag
```
This line starts the `sq_sum_expand_offDiag` declaration. Because it begins with `lemma`, Lean now knows what kind of named object is being introduced.

3. Code:
```lean
    {ι : Type u} [Fintype ι] (p : ι → ℝ) :
```
This line is one local step in the declaration. It either refines the formula being defined or advances the proof by a small algebraic or logical move.  A bracket such as `[Fintype d]` tells Lean that the index set `d` is finite, so sums over all indices make sense.

4. Code:
```lean
    (∑ i, p i) ^ 2 =
```
This line is one local step in the declaration. It either refines the formula being defined or advances the proof by a small algebraic or logical move.

5. Code:
```lean
      (∑ i, (p i) ^ 2) + ∑ x ∈ (Finset.univ : Finset ι).offDiag, p x.1 * p x.2 := by
```
This line says that a proof script begins here. Everything indented underneath is a sequence of instructions that Lean will check step by step.

6. Code:
```lean
  classical
```
This line is one local step in the declaration. It either refines the formula being defined or advances the proof by a small algebraic or logical move.

7. Code:
```lean
  calc
```
This line begins a chained calculation. Each displayed step that follows must be justified by the indented proof after `:= by`.

8. Code:
```lean
    (∑ i, p i) ^ 2 = (∑ i, p i) * (∑ j, p j) := by
```
This line says that a proof script begins here. Everything indented underneath is a sequence of instructions that Lean will check step by step.

9. Code:
```lean
      ring
```
This line normalizes an algebraic identity in a commutative ring, just as one would expand and collect like terms by hand.

10. Code:
```lean
    _ = ∑ x ∈ ((Finset.univ : Finset ι) ×ˢ (Finset.univ : Finset ι)), p x.1 * p x.2 := by
```
This line says that a proof script begins here. Everything indented underneath is a sequence of instructions that Lean will check step by step.

11. Code:
```lean
      calc
```
This line begins a chained calculation. Each displayed step that follows must be justified by the indented proof after `:= by`.

12. Code:
```lean
        (∑ i, p i) * (∑ j, p j) = ∑ i, ∑ j, p i * p j := by
```
This line says that a proof script begins here. Everything indented underneath is a sequence of instructions that Lean will check step by step.

13. Code:
```lean
          simpa using (Fintype.sum_mul_sum p p)
```
This line simplifies the goal using definitions and known equalities. `simpa` means that, after simplification, the desired statement matches a theorem Lean already has.

14. Code:
```lean
        _ = ∑ x ∈ ((Finset.univ : Finset ι) ×ˢ (Finset.univ : Finset ι)), p x.1 * p x.2 := by
```
This line says that a proof script begins here. Everything indented underneath is a sequence of instructions that Lean will check step by step.

15. Code:
```lean
          rw [← Finset.sum_product']
```
This line uses rewriting. Lean replaces one expression by an equal expression using the lemmas listed in brackets.

16. Code:
```lean
    _ = ∑ x ∈ (Finset.univ : Finset ι).diag ∪ (Finset.univ : Finset ι).offDiag,
```
This line is one step inside a `calc` block. Lean is checking that the new expression really follows from the previous one.

17. Code:
```lean
          p x.1 * p x.2 := by
```
This line says that a proof script begins here. Everything indented underneath is a sequence of instructions that Lean will check step by step.

18. Code:
```lean
      rw [← Finset.diag_union_offDiag]
```
This line uses rewriting. Lean replaces one expression by an equal expression using the lemmas listed in brackets.

19. Code:
```lean
    _ = (∑ x ∈ (Finset.univ : Finset ι).diag, p x.1 * p x.2) +
```
This line is one step inside a `calc` block. Lean is checking that the new expression really follows from the previous one.

20. Code:
```lean
          ∑ x ∈ (Finset.univ : Finset ι).offDiag, p x.1 * p x.2 := by
```
This line says that a proof script begins here. Everything indented underneath is a sequence of instructions that Lean will check step by step.

21. Code:
```lean
      rw [Finset.sum_union (Finset.disjoint_diag_offDiag (s := (Finset.univ : Finset ι)))]
```
This line uses rewriting. Lean replaces one expression by an equal expression using the lemmas listed in brackets.

22. Code:
```lean
    _ = (∑ i, (p i) ^ 2) + ∑ x ∈ (Finset.univ : Finset ι).offDiag, p x.1 * p x.2 := by
```
This line says that a proof script begins here. Everything indented underneath is a sequence of instructions that Lean will check step by step.

23. Code:
```lean
      rw [Finset.sum_diag]
```
This line uses rewriting. Lean replaces one expression by an equal expression using the lemmas listed in brackets.

24. Code:
```lean
      simp [pow_two]
```
This line simplifies the goal using definitions and known equalities. `simpa` means that, after simplification, the desired statement matches a theorem Lean already has.

## Mathematical summary

Restated without Lean syntax, `sq_sum_expand_offDiag` is the theorem or lemma written above.

- State the desired identity or inequality in Lean’s syntax.
- Introduce temporary names and intermediate claims that organize the argument.
- Use rewriting, simplification, and earlier lemmas to reduce the goal to standard matrix or norm manipulations.
- Close the remaining algebraic or order-theoretic steps with Lean’s proof tactics.

## Dependencies and downstream use

### Earlier declarations this depends on
- This declaration does not explicitly cite an earlier named declaration from the documented tree; it mostly uses Lean primitives or local algebraic steps.

### Later declarations that use this one
- [`pairwise_zero_of_sum_sq_eq_sq_sum`](pairwise_zero_of_sum_sq_eq_sq_sum.md) in `PositiveGap/NotTight.lean`

## Backlinks

- [Back to `INDEX.md`](../../INDEX.md)
- [Back to the `PositiveGap/NotTight.lean` section in the index](../../INDEX.md#diamond-positivegap-nottight-lean)
- [Next declaration in this file](pairwise_zero_of_sum_sq_eq_sq_sum.md)