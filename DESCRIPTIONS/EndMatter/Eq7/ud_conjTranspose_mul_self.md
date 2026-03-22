# ud_conjTranspose_mul_self

## Source location

- Original Lean file: `Diamond/EndMatter/Eq7.lean`
- Declaration name: `ud_conjTranspose_mul_self`
- Declaration kind: `theorem`

## Why this declaration exists

This theorem records a reusable fact named `ud_conjTranspose_mul_self`. Its role is to make the later proof flow easier to state and reuse.

 In the file `EndMatter/Eq7.lean`, it contributes to the explicit witness construction used to prove the lower bound labelled Eq. (7). Later proofs call this result by name, so documenting it makes the larger argument readable as a mathematical chain rather than as opaque proof script.

## Original code

```lean
theorem ud_conjTranspose_mul_self (d : ℕ) [Fact (1 < d)] :
    (Ud d)ᴴ * Ud d = 1 := by
  unfold Ud
  rw [Matrix.diagonal_conjTranspose, Matrix.diagonal_mul_diagonal]
  ext i j
  by_cases hij : i = j
  · subst hij
    simpa [Ud, Matrix.diagonal_apply_eq, mul_comm] using (ud_mul_star_self d i)
  · simp [hij]
```

## Block-by-block explanation

The explanation below follows the declaration block by block. Each block groups a coherent piece of the definition or proof, so the mathematical structure is easier to see than in a strictly line-oriented reading.

1. Code:
```lean
theorem ud_conjTranspose_mul_self (d : ℕ) [Fact (1 < d)] :
```
This line starts the `ud_conjTranspose_mul_self` declaration. Because it begins with `theorem`, Lean now knows what kind of named object is being introduced.

2. Code:
```lean
    (Ud d)ᴴ * Ud d = 1 := by
```
This line says that a proof script begins here. Everything indented underneath is a sequence of instructions that Lean will check step by step.  The superscript `ᴴ` means conjugate transpose (also called the adjoint).

3. Code:
```lean
  unfold Ud
```
This line is one local step in the declaration. It either refines the formula being defined or advances the proof by a small algebraic or logical move.

4. Code:
```lean
  rw [Matrix.diagonal_conjTranspose, Matrix.diagonal_mul_diagonal]
```
This line uses rewriting. Lean replaces one expression by an equal expression using the lemmas listed in brackets.

5. Code:
```lean
  ext i j
```
This line invokes extensionality. To prove two maps or matrices are equal, Lean reduces the problem to checking their values entry by entry.

6. Code:
```lean
  by_cases hij : i = j
```
This line splits the proof into cases according to whether the named proposition is true or false.

7. Code:
```lean
  · subst hij
```
This bullet starts a new subgoal produced by the previous tactic. Lean is now focusing on one branch of the argument.

8. Code:
```lean
    simpa [Ud, Matrix.diagonal_apply_eq, mul_comm] using (ud_mul_star_self d i)
```
This line simplifies the goal using definitions and known equalities. `simpa` means that, after simplification, the desired statement matches a theorem Lean already has.

9. Code:
```lean
  · simp [hij]
```
This bullet starts a new subgoal produced by the previous tactic. Lean is now focusing on one branch of the argument.

## Mathematical summary

Restated without Lean syntax, `ud_conjTranspose_mul_self` is the theorem or lemma written above.

- State the desired identity or inequality in Lean’s syntax.
- Introduce temporary names and intermediate claims that organize the argument.
- Use rewriting, simplification, and earlier lemmas to reduce the goal to standard matrix or norm manipulations.
- Close the remaining algebraic or order-theoretic steps with Lean’s proof tactics.

## Dependencies and downstream use

### Earlier declarations this depends on
- [`Ud`](../../Setups/Ud.md) from `Setups.lean`
- [`ud_mul_star_self`](ud_mul_star_self.md) from `EndMatter/Eq7.lean`

### Later declarations that use this one
- [`theorem_eq8`](../Eq8/theorem_eq8.md) in `EndMatter/Eq8.lean`
- [`alpha_lower_bound`](../Eq8/alpha_lower_bound.md) in `EndMatter/Eq8.lean`

## Backlinks

- [Back to `INDEX.md`](../../INDEX.md)
- [Back to the `EndMatter/Eq7.lean` section in the index](../../INDEX.md#diamond-endmatter-eq7-lean)
- [Previous declaration in this file](ud_mul_star_self.md)
- [Next declaration in this file](ud_add_mul_star_eq.md)