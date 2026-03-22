# adMap_isQuantumChannel

## Source location

- Original Lean file: `Diamond/StandardFacts.lean`
- Declaration name: `adMap_isQuantumChannel`
- Declaration kind: `theorem`

## Why this declaration exists

Unitary conjugation is a quantum channel.

 In the file `StandardFacts.lean`, it contributes to helper facts and background reductions that later proofs use directly. Later proofs call this result by name, so documenting it makes the larger argument readable as a mathematical chain rather than as opaque proof script.

## Original code

```lean
/-- Unitary conjugation is a quantum channel. -/
theorem adMap_isQuantumChannel
    {d : Type u} [Fintype d] [DecidableEq d]
    (U : Matrix d d ℂ) (hU : Uᴴ * U = 1) :
    IsQuantumChannel (adMap d U) := by
  refine ⟨?_, ?_⟩
  · intro X
    calc
      Matrix.trace (adMap d U X) = Matrix.trace (U * X * Uᴴ) := by rfl
      _ = Matrix.trace ((Uᴴ * U) * X) := by
            simpa [Matrix.mul_assoc] using Matrix.trace_mul_cycle U X Uᴴ
      _ = Matrix.trace X := by simp [hU]
  · intro X
    simp [adMap, Matrix.conjTranspose_mul, Matrix.mul_assoc]

/-- Abstract pointwise-to-diamond reduction.

    This lemma states the standard `k = d` reduction used throughout the file. -/
-- Background functional-analytic fact (finite-dimensional attainment/compactness input).
```

## Block-by-block explanation

The explanation below follows the declaration block by block. Each block groups a coherent piece of the definition or proof, so the mathematical structure is easier to see than in a strictly line-oriented reading.

1. Code:
```lean
/-- Unitary conjugation is a quantum channel. -/
```
This is a Lean docstring. It is a human-written comment that tells readers what the declaration is meant to express before the formal code begins.

2. Code:
```lean
theorem adMap_isQuantumChannel
```
This line starts the `adMap_isQuantumChannel` declaration. Because it begins with `theorem`, Lean now knows what kind of named object is being introduced.

3. Code:
```lean
    {d : Type u} [Fintype d] [DecidableEq d]
```
This line is one local step in the declaration. It either refines the formula being defined or advances the proof by a small algebraic or logical move.  A bracket such as `[Fintype d]` tells Lean that the index set `d` is finite, so sums over all indices make sense.  A bracket such as `[DecidableEq d]` tells Lean that it can decide whether two indices are equal.

4. Code:
```lean
    (U : Matrix d d ℂ) (hU : Uᴴ * U = 1) :
```
This line is one local step in the declaration. It either refines the formula being defined or advances the proof by a small algebraic or logical move.  `Matrix d d ℂ` means a square matrix with complex entries; the index type `d` tells Lean which rows and columns exist.  The superscript `ᴴ` means conjugate transpose (also called the adjoint).

5. Code:
```lean
    IsQuantumChannel (adMap d U) := by
```
This line says that a proof script begins here. Everything indented underneath is a sequence of instructions that Lean will check step by step.  `Channel d` is an abbreviation for a complex-linear map from operators on `d` to operators on `d`.

6. Code:
```lean
  refine ⟨?_, ?_⟩
```
This line is a more controlled version of `apply`. It sets up the proof with a partly specified argument and leaves smaller goals to solve next.

7. Code:
```lean
  · intro X
```
This bullet starts a new subgoal produced by the previous tactic. Lean is now focusing on one branch of the argument.

8. Code:
```lean
    calc
```
This line begins a chained calculation. Each displayed step that follows must be justified by the indented proof after `:= by`.

9. Code:
```lean
      Matrix.trace (adMap d U X) = Matrix.trace (U * X * Uᴴ) := by rfl
```
This line is one local step in the declaration. It either refines the formula being defined or advances the proof by a small algebraic or logical move.  The superscript `ᴴ` means conjugate transpose (also called the adjoint).

10. Code:
```lean
      _ = Matrix.trace ((Uᴴ * U) * X) := by
```
This line says that a proof script begins here. Everything indented underneath is a sequence of instructions that Lean will check step by step.  The superscript `ᴴ` means conjugate transpose (also called the adjoint).

11. Code:
```lean
            simpa [Matrix.mul_assoc] using Matrix.trace_mul_cycle U X Uᴴ
```
This line simplifies the goal using definitions and known equalities. `simpa` means that, after simplification, the desired statement matches a theorem Lean already has.  The superscript `ᴴ` means conjugate transpose (also called the adjoint).

12. Code:
```lean
      _ = Matrix.trace X := by simp [hU]
```
This line is one step inside a `calc` block. Lean is checking that the new expression really follows from the previous one.

13. Code:
```lean
  · intro X
```
This bullet starts a new subgoal produced by the previous tactic. Lean is now focusing on one branch of the argument.

14. Code:
```lean
    simp [adMap, Matrix.conjTranspose_mul, Matrix.mul_assoc]
```
This line simplifies the goal using definitions and known equalities. `simpa` means that, after simplification, the desired statement matches a theorem Lean already has.

15. Code:
```lean
/-- Abstract pointwise-to-diamond reduction.
```
This is a Lean docstring. It is a human-written comment that tells readers what the declaration is meant to express before the formal code begins.

16. Code:
```lean
    This lemma states the standard `k = d` reduction used throughout the file. -/
```
This line is one local step in the declaration. It either refines the formula being defined or advances the proof by a small algebraic or logical move.

17. Code:
```lean
-- Background functional-analytic fact (finite-dimensional attainment/compactness input).
```
This line is one local step in the declaration. It either refines the formula being defined or advances the proof by a small algebraic or logical move.

## Mathematical summary

Restated without Lean syntax, `adMap_isQuantumChannel` is the theorem or lemma written above.

- State the desired identity or inequality in Lean’s syntax.
- Introduce temporary names and intermediate claims that organize the argument.
- Use rewriting, simplification, and earlier lemmas to reduce the goal to standard matrix or norm manipulations.
- Close the remaining algebraic or order-theoretic steps with Lean’s proof tactics.

## Dependencies and downstream use

### Earlier declarations this depends on
- [`IsQuantumChannel`](../Setups/IsQuantumChannel.md) from `Setups.lean`
- [`adMap`](../Setups/adMap.md) from `Setups.lean`

### Later declarations that use this one
- [`alpha_lower_bound`](../EndMatter/Eq8/alpha_lower_bound.md) in `EndMatter/Eq8.lean`

## Backlinks

- [Back to `INDEX.md`](../INDEX.md)
- [Back to the `StandardFacts.lean` section in the index](../INDEX.md#diamond-standardfacts-lean)
- [Previous declaration in this file](idMinus_isTraceAnnihilating.md)
- [Next declaration in this file](diamond_le_of_pointwise.md)