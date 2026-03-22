# idMinus_isHermiticityPreserving

## Source location

- Original Lean file: `Diamond/StandardFacts.lean`
- Declaration name: `idMinus_isHermiticityPreserving`
- Declaration kind: `theorem`

## Why this declaration exists

`idMinus` preserves Hermiticity for CPTP channels.

 In the file `StandardFacts.lean`, it contributes to helper facts and background reductions that later proofs use directly. Later proofs call this result by name, so documenting it makes the larger argument readable as a mathematical chain rather than as opaque proof script.

## Original code

```lean
/-- `idMinus` preserves Hermiticity for CPTP channels. -/
theorem idMinus_isHermiticityPreserving
    {d : Type u} [Fintype d] [DecidableEq d] (T : Channel d) (hT : IsQuantumChannel T) :
    IsHermiticityPreserving (idMinus T) := by
  intro X
  calc
    idMinus T Xᴴ = Xᴴ - T Xᴴ := by simp [idMinus]
    _ = Xᴴ - (T X)ᴴ := by rw [hT.hermiticity_preserving X]
    _ = (X - T X)ᴴ := by simp [Matrix.conjTranspose_sub]
```

## Block-by-block explanation

The explanation below follows the declaration block by block. Each block groups a coherent piece of the definition or proof, so the mathematical structure is easier to see than in a strictly line-oriented reading.

1. Code:
```lean
/-- `idMinus` preserves Hermiticity for CPTP channels. -/
```
This is a Lean docstring. It is a human-written comment that tells readers what the declaration is meant to express before the formal code begins.

2. Code:
```lean
theorem idMinus_isHermiticityPreserving
```
This line starts the `idMinus_isHermiticityPreserving` declaration. Because it begins with `theorem`, Lean now knows what kind of named object is being introduced.

3. Code:
```lean
    {d : Type u} [Fintype d] [DecidableEq d] (T : Channel d) (hT : IsQuantumChannel T) :
```
This line is one local step in the declaration. It either refines the formula being defined or advances the proof by a small algebraic or logical move.  `Channel d` is an abbreviation for a complex-linear map from operators on `d` to operators on `d`.  A bracket such as `[Fintype d]` tells Lean that the index set `d` is finite, so sums over all indices make sense.  A bracket such as `[DecidableEq d]` tells Lean that it can decide whether two indices are equal.

4. Code:
```lean
    IsHermiticityPreserving (idMinus T) := by
```
This line says that a proof script begins here. Everything indented underneath is a sequence of instructions that Lean will check step by step.

5. Code:
```lean
  intro X
```
This line introduces the variable or hypothesis named here into the proof context. In ordinary mathematical prose, it is the same as saying “let” or “assume”.

6. Code:
```lean
  calc
```
This line begins a chained calculation. Each displayed step that follows must be justified by the indented proof after `:= by`.

7. Code:
```lean
    idMinus T Xᴴ = Xᴴ - T Xᴴ := by simp [idMinus]
```
This line is one local step in the declaration. It either refines the formula being defined or advances the proof by a small algebraic or logical move.  The superscript `ᴴ` means conjugate transpose (also called the adjoint).

8. Code:
```lean
    _ = Xᴴ - (T X)ᴴ := by rw [hT.hermiticity_preserving X]
```
This line is one step inside a `calc` block. Lean is checking that the new expression really follows from the previous one.  The superscript `ᴴ` means conjugate transpose (also called the adjoint).

9. Code:
```lean
    _ = (X - T X)ᴴ := by simp [Matrix.conjTranspose_sub]
```
This line is one step inside a `calc` block. Lean is checking that the new expression really follows from the previous one.  The superscript `ᴴ` means conjugate transpose (also called the adjoint).

## Mathematical summary

Restated without Lean syntax, `idMinus_isHermiticityPreserving` is the theorem or lemma written above.

- State the desired identity or inequality in Lean’s syntax.
- Introduce temporary names and intermediate claims that organize the argument.
- Use rewriting, simplification, and earlier lemmas to reduce the goal to standard matrix or norm manipulations.
- Close the remaining algebraic or order-theoretic steps with Lean’s proof tactics.

## Dependencies and downstream use

### Earlier declarations this depends on
- [`Channel`](../Setups/Channel.md) from `Setups.lean`
- [`IsHermiticityPreserving`](../Setups/IsHermiticityPreserving.md) from `Setups.lean`
- [`IsQuantumChannel`](../Setups/IsQuantumChannel.md) from `Setups.lean`
- [`idMinus`](../Setups/idMinus.md) from `Setups.lean`

### Later declarations that use this one
- [`theorem1`](../Theorem/Theorem1/theorem1.md) in `Theorem/Theorem1.lean`
- [`theorem_not_tight`](../PositiveGap/NotTight/theorem_not_tight.md) in `PositiveGap/NotTight.lean`
- [`corollary2_linear_bound`](../EndMatter/Corollary2/corollary2_linear_bound.md) in `EndMatter/Corollary2.lean`

## Backlinks

- [Back to `INDEX.md`](../INDEX.md)
- [Back to the `StandardFacts.lean` section in the index](../INDEX.md#diamond-standardfacts-lean)
- [Previous declaration in this file](tensorWithIdentity_comp_transpose.md)
- [Next declaration in this file](idMinus_isTraceAnnihilating.md)