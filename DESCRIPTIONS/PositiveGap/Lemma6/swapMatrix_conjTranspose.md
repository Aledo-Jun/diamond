# swapMatrix_conjTranspose

## Source location

- Original Lean file: `Diamond/PositiveGap/Lemma6.lean`
- Declaration name: `swapMatrix_conjTranspose`
- Declaration kind: `theorem`

## Why this declaration exists

This theorem records a reusable fact named `swapMatrix_conjTranspose`. Its role is to make the later proof flow easier to state and reuse.

 In the file `PositiveGap/Lemma6.lean`, it contributes to the swap operator and its algebraic interaction with tensor products. Later proofs call this result by name, so documenting it makes the larger argument readable as a mathematical chain rather than as opaque proof script.

## Original code

```lean
theorem swapMatrix_conjTranspose (d : ℕ) :
    (swapMatrix d)ᴴ = swapMatrix d := by
  ext i j
  by_cases h : i.1 = j.2 ∧ i.2 = j.1
  · rcases h with ⟨h1, h2⟩
    have h' : j.1 = i.2 ∧ j.2 = i.1 := ⟨h2.symm, h1.symm⟩
    change
      star (if j.1 = i.2 ∧ j.2 = i.1 then (1 : ℂ) else 0) =
        if i.1 = j.2 ∧ i.2 = j.1 then (1 : ℂ) else 0
    simp only [if_pos h', if_pos (And.intro h1 h2), star_one]
  · have h' : ¬ (j.1 = i.2 ∧ j.2 = i.1) := by
      intro hji
      apply h
      exact ⟨hji.2.symm, hji.1.symm⟩
    change
      star (if j.1 = i.2 ∧ j.2 = i.1 then (1 : ℂ) else 0) =
        if i.1 = j.2 ∧ i.2 = j.1 then (1 : ℂ) else 0
    simp only [if_neg h', if_neg h, star_zero]
```

## Block-by-block explanation

The explanation below follows the declaration block by block. Each block groups a coherent piece of the definition or proof, so the mathematical structure is easier to see than in a strictly line-oriented reading.

1. Code:
```lean
theorem swapMatrix_conjTranspose (d : ℕ) :
```
This line starts the `swapMatrix_conjTranspose` declaration. Because it begins with `theorem`, Lean now knows what kind of named object is being introduced.

2. Code:
```lean
    (swapMatrix d)ᴴ = swapMatrix d := by
```
This line says that a proof script begins here. Everything indented underneath is a sequence of instructions that Lean will check step by step.  `Matrix d d ℂ` means a square matrix with complex entries; the index type `d` tells Lean which rows and columns exist.  The superscript `ᴴ` means conjugate transpose (also called the adjoint).

3. Code:
```lean
  ext i j
```
This line invokes extensionality. To prove two maps or matrices are equal, Lean reduces the problem to checking their values entry by entry.

4. Code:
```lean
  by_cases h : i.1 = j.2 ∧ i.2 = j.1
```
This line splits the proof into cases according to whether the named proposition is true or false.

5. Code:
```lean
  · rcases h with ⟨h1, h2⟩
```
This bullet starts a new subgoal produced by the previous tactic. Lean is now focusing on one branch of the argument.

6. Code:
```lean
    have h' : j.1 = i.2 ∧ j.2 = i.1 := ⟨h2.symm, h1.symm⟩
```
This line introduces an intermediate claim. The proof pauses to establish a fact that will be used shortly afterwards.

7. Code:
```lean
    change
```
This line replaces the current goal by a definitionally equal goal that is easier to manipulate.

8. Code:
```lean
      star (if j.1 = i.2 ∧ j.2 = i.1 then (1 : ℂ) else 0) =
```
This line is one local step in the declaration. It either refines the formula being defined or advances the proof by a small algebraic or logical move.

9. Code:
```lean
        if i.1 = j.2 ∧ i.2 = j.1 then (1 : ℂ) else 0
```
This line is one local step in the declaration. It either refines the formula being defined or advances the proof by a small algebraic or logical move.

10. Code:
```lean
    simp only [if_pos h', if_pos (And.intro h1 h2), star_one]
```
This line simplifies the goal using definitions and known equalities. `simpa` means that, after simplification, the desired statement matches a theorem Lean already has.

11. Code:
```lean
  · have h' : ¬ (j.1 = i.2 ∧ j.2 = i.1) := by
```
This line says that a proof script begins here. Everything indented underneath is a sequence of instructions that Lean will check step by step.

12. Code:
```lean
      intro hji
```
This line introduces the variable or hypothesis named here into the proof context. In ordinary mathematical prose, it is the same as saying “let” or “assume”.

13. Code:
```lean
      apply h
```
This line applies an existing theorem to the current goal. Lean then asks the author to prove the theorem’s hypotheses.

14. Code:
```lean
      exact ⟨hji.2.symm, hji.1.symm⟩
```
This line finishes the current goal by giving Lean the exact theorem, lemma, or term that proves it.

15. Code:
```lean
    change
```
This line replaces the current goal by a definitionally equal goal that is easier to manipulate.

16. Code:
```lean
      star (if j.1 = i.2 ∧ j.2 = i.1 then (1 : ℂ) else 0) =
```
This line is one local step in the declaration. It either refines the formula being defined or advances the proof by a small algebraic or logical move.

17. Code:
```lean
        if i.1 = j.2 ∧ i.2 = j.1 then (1 : ℂ) else 0
```
This line is one local step in the declaration. It either refines the formula being defined or advances the proof by a small algebraic or logical move.

18. Code:
```lean
    simp only [if_neg h', if_neg h, star_zero]
```
This line simplifies the goal using definitions and known equalities. `simpa` means that, after simplification, the desired statement matches a theorem Lean already has.

## Mathematical summary

Restated without Lean syntax, `swapMatrix_conjTranspose` is the theorem or lemma written above.

- State the desired identity or inequality in Lean’s syntax.
- Introduce temporary names and intermediate claims that organize the argument.
- Use rewriting, simplification, and earlier lemmas to reduce the goal to standard matrix or norm manipulations.
- Close the remaining algebraic or order-theoretic steps with Lean’s proof tactics.

## Dependencies and downstream use

### Earlier declarations this depends on
- [`swapMatrix`](swapMatrix.md) from `PositiveGap/Lemma6.lean`

### Later declarations that use this one
- [`swapMatrix_conjTranspose_mul_self`](swapMatrix_conjTranspose_mul_self.md) in `PositiveGap/Lemma6.lean`

## Backlinks

- [Back to `INDEX.md`](../../INDEX.md)
- [Back to the `PositiveGap/Lemma6.lean` section in the index](../../INDEX.md#diamond-positivegap-lemma6-lean)
- [Previous declaration in this file](swapMatrix_mul_self.md)
- [Next declaration in this file](swapMatrix_conjTranspose_mul_self.md)