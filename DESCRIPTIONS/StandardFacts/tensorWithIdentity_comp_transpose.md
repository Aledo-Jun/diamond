# tensorWithIdentity_comp_transpose

## Source location

- Original Lean file: `Diamond/StandardFacts.lean`
- Declaration name: `tensorWithIdentity_comp_transpose`
- Declaration kind: `theorem`

## Why this declaration exists

`tensorWithIdentity` commutes with transposition on the left tensor factor.

 In the file `StandardFacts.lean`, it contributes to helper facts and background axioms that the paper treats as standard or external input. Later proofs call this result by name, so documenting it makes the larger argument readable as a mathematical chain rather than as opaque proof script.

## Original code

```lean
/-- `tensorWithIdentity` commutes with transposition on the left tensor factor. -/
theorem tensorWithIdentity_comp_transpose
    {d k : Type u} [Fintype d] [DecidableEq d] [Fintype k] [DecidableEq k]
    (Φ : Channel d) :
    tensorWithIdentity d k ((transposeMap d).comp Φ)
      = (partialTransposeMap d k).comp (tensorWithIdentity d k Φ) := by
  ext X i j
  simp [tensorWithIdentity, partialTransposeMap, LinearMap.comp_apply, transposeMap]
```

## Line-by-line explanation

The explanation below follows the declaration one physical line at a time. For long proofs, some lines are tiny bookkeeping steps; those are still explained, but briefly.

1. Code:
```lean
/-- `tensorWithIdentity` commutes with transposition on the left tensor factor. -/
```
This is a Lean docstring. It is a human-written comment that tells readers what the declaration is meant to express before the formal code begins.

2. Code:
```lean
theorem tensorWithIdentity_comp_transpose
```
This line starts the `tensorWithIdentity_comp_transpose` declaration. Because it begins with `theorem`, Lean now knows what kind of named object is being introduced.

3. Code:
```lean
    {d k : Type u} [Fintype d] [DecidableEq d] [Fintype k] [DecidableEq k]
```
This line is one local step in the declaration. It either refines the formula being defined or advances the proof by a small algebraic or logical move.  A bracket such as `[Fintype d]` tells Lean that the index set `d` is finite, so sums over all indices make sense.  A bracket such as `[DecidableEq d]` tells Lean that it can decide whether two indices are equal.

4. Code:
```lean
    (Φ : Channel d) :
```
This line is one local step in the declaration. It either refines the formula being defined or advances the proof by a small algebraic or logical move.  `Channel d` is an abbreviation for a complex-linear map from operators on `d` to operators on `d`.

5. Code:
```lean
    tensorWithIdentity d k ((transposeMap d).comp Φ)
```
This line is one local step in the declaration. It either refines the formula being defined or advances the proof by a small algebraic or logical move.  `comp` means composition of maps: one map is applied after another.

6. Code:
```lean
      = (partialTransposeMap d k).comp (tensorWithIdentity d k Φ) := by
```
This line says that a proof script begins here. Everything indented underneath is a sequence of instructions that Lean will check step by step.  `comp` means composition of maps: one map is applied after another.

7. Code:
```lean
  ext X i j
```
This line invokes extensionality. To prove two maps or matrices are equal, Lean reduces the problem to checking their values entry by entry.

8. Code:
```lean
  simp [tensorWithIdentity, partialTransposeMap, LinearMap.comp_apply, transposeMap]
```
This line simplifies the goal using definitions and known equalities. `simpa` means that, after simplification, the desired statement matches a theorem Lean already has.  `comp` means composition of maps: one map is applied after another.  `LinearMap.comp` is composition of linear maps.

## Mathematical summary

Restated without Lean syntax, `tensorWithIdentity_comp_transpose` is the theorem or lemma written above.

- State the desired identity or inequality in Lean’s syntax.
- Introduce temporary names and intermediate claims that organize the argument.
- Use rewriting, simplification, and earlier lemmas to reduce the goal to standard matrix or norm manipulations.
- Close the remaining algebraic or order-theoretic steps with Lean’s proof tactics.

## Dependencies and downstream use

### Earlier declarations this depends on
- [`Channel`](../Setups/Channel.md) from `Setups.lean`
- [`transposeMap`](../Setups/transposeMap.md) from `Setups.lean`
- [`tensorWithIdentity`](../Setups/tensorWithIdentity.md) from `Setups.lean`
- [`partialTransposeMap`](../Setups/partialTransposeMap.md) from `Setups.lean`

### Later declarations that use this one
- [`theorem1`](../Theorem/Theorem1/theorem1.md) in `Theorem/Theorem1.lean`
- [`remark1`](../Theorem/Remark1/remark1.md) in `Theorem/Remark1.lean`
- [`theorem_not_tight`](../PositiveGap/NotTight/theorem_not_tight.md) in `PositiveGap/NotTight.lean`

## Backlinks

- [Back to `INDEX.md`](../INDEX.md)
- [Back to the `StandardFacts.lean` section in the index](../INDEX.md#diamond-standardfacts-lean)
- [Previous declaration in this file](quantumChannel_has_kraus.md)
- [Next declaration in this file](idMinus_isHermiticityPreserving.md)