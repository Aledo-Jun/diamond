# exists_maximizing_state

## Source location

- Original Lean file: `Diamond/StandardFacts.lean`
- Declaration name: `exists_maximizing_state`
- Declaration kind: `axiom`

## Why this declaration exists

This axiom packages the finite-dimensional attainment statement used in the non-tightness argument.

 In the file `StandardFacts.lean`, it contributes to helper facts and background axioms that the paper treats as standard or external input. Later proofs call this result by name, so documenting it makes the larger argument readable as a mathematical chain rather than as opaque proof script.

## Original code

```lean
/-- Finite-dimensional attainment of the left-hand diamond norm in the positive-gap argument.
    This compactness/maximizer step is background to the paper's main flow. -/
axiom exists_maximizing_state
    {d : Type u} [Fintype d] [DecidableEq d] [Nonempty d]
    (T : Channel d) (hT : IsQuantumChannel T) (hΦ : idMinus T ≠ 0) :
    ∃ ρ : DensityState (d × d),
      traceNormOp
          (tensorWithIdentity d d ((transposeMap d).comp (idMinus T)) ρ.1) =
        diamondOp ((transposeMap d).comp (idMinus T)) ∧
      tensorWithIdentity d d (idMinus T) ρ.1 ≠ 0
```

## Line-by-line explanation

The explanation below follows the declaration one physical line at a time. For long proofs, some lines are tiny bookkeeping steps; those are still explained, but briefly.

1. Code:
```lean
/-- Finite-dimensional attainment of the left-hand diamond norm in the positive-gap argument.
```
This is a Lean docstring. It is a human-written comment that tells readers what the declaration is meant to express before the formal code begins.

2. Code:
```lean
    This compactness/maximizer step is background to the paper's main flow. -/
```
This line is one local step in the declaration. It either refines the formula being defined or advances the proof by a small algebraic or logical move.

3. Code:
```lean
axiom exists_maximizing_state
```
This line starts the `exists_maximizing_state` declaration. Because it begins with `axiom`, Lean now knows what kind of named object is being introduced.

4. Code:
```lean
    {d : Type u} [Fintype d] [DecidableEq d] [Nonempty d]
```
This line is one local step in the declaration. It either refines the formula being defined or advances the proof by a small algebraic or logical move.  A bracket such as `[Fintype d]` tells Lean that the index set `d` is finite, so sums over all indices make sense.  A bracket such as `[DecidableEq d]` tells Lean that it can decide whether two indices are equal.

5. Code:
```lean
    (T : Channel d) (hT : IsQuantumChannel T) (hΦ : idMinus T ≠ 0) :
```
This line is one local step in the declaration. It either refines the formula being defined or advances the proof by a small algebraic or logical move.  `Channel d` is an abbreviation for a complex-linear map from operators on `d` to operators on `d`.

6. Code:
```lean
    ∃ ρ : DensityState (d × d),
```
This line is one local step in the declaration. It either refines the formula being defined or advances the proof by a small algebraic or logical move.

7. Code:
```lean
      traceNormOp
```
This line is one local step in the declaration. It either refines the formula being defined or advances the proof by a small algebraic or logical move.

8. Code:
```lean
          (tensorWithIdentity d d ((transposeMap d).comp (idMinus T)) ρ.1) =
```
This line is one local step in the declaration. It either refines the formula being defined or advances the proof by a small algebraic or logical move.  `comp` means composition of maps: one map is applied after another.

9. Code:
```lean
        diamondOp ((transposeMap d).comp (idMinus T)) ∧
```
This line is one local step in the declaration. It either refines the formula being defined or advances the proof by a small algebraic or logical move.  `comp` means composition of maps: one map is applied after another.

10. Code:
```lean
      tensorWithIdentity d d (idMinus T) ρ.1 ≠ 0
```
This line is one local step in the declaration. It either refines the formula being defined or advances the proof by a small algebraic or logical move.

## Mathematical summary

Restated without Lean syntax, `exists_maximizing_state` is the theorem or lemma written above.

- State the desired identity or inequality in Lean’s syntax.
- Introduce temporary names and intermediate claims that organize the argument.
- Use rewriting, simplification, and earlier lemmas to reduce the goal to standard matrix or norm manipulations.
- Close the remaining algebraic or order-theoretic steps with Lean’s proof tactics.

## Dependencies and downstream use

### Earlier declarations this depends on
- [`Channel`](../Setups/Channel.md) from `Setups.lean`
- [`traceNormOp`](../Setups/traceNormOp.md) from `Setups.lean`
- [`DensityState`](../Setups/DensityState.md) from `Setups.lean`
- [`IsQuantumChannel`](../Setups/IsQuantumChannel.md) from `Setups.lean`
- [`transposeMap`](../Setups/transposeMap.md) from `Setups.lean`
- [`tensorWithIdentity`](../Setups/tensorWithIdentity.md) from `Setups.lean`
- [`diamondOp`](../Setups/diamondOp.md) from `Setups.lean`
- [`idMinus`](../Setups/idMinus.md) from `Setups.lean`

### Later declarations that use this one
- [`theorem_not_tight`](../PositiveGap/NotTight/theorem_not_tight.md) in `PositiveGap/NotTight.lean`

## Backlinks

- [Back to `INDEX.md`](../INDEX.md)
- [Back to the `StandardFacts.lean` section in the index](../INDEX.md#diamond-standardfacts-lean)
- [Previous declaration in this file](trace_Ud_eq_zero.md)
- [Next declaration in this file](partialTranspose_rank_upper_bound.md)