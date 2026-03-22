# partialTraceLeft_tensor_zero

## Source location

- Original Lean file: `Diamond/StandardFacts.lean`
- Declaration name: `partialTraceLeft_tensor_zero`
- Declaration kind: `theorem`

## Why this declaration exists

Tensoring a trace-annihilating map with the identity has vanishing left partial trace.

 In the file `StandardFacts.lean`, it contributes to helper facts and background reductions that later proofs use directly. Later proofs call this result by name, so documenting it makes the larger argument readable as a mathematical chain rather than as opaque proof script.

## Original code

```lean
/-- Tensoring a trace-annihilating map with the identity has vanishing left partial trace. -/
theorem partialTraceLeft_tensor_zero
    {d k : Type u} [Fintype d] [DecidableEq d] [Fintype k] [DecidableEq k]
    (Ψ : Channel d) (hT : IsTraceAnnihilating Ψ)
    (Z : Matrix (d × k) (d × k) ℂ) :
    partialTraceLeft d k (tensorWithIdentity d k Ψ Z) = 0 := by
  ext i j
  have htrace :
      Matrix.trace (Ψ (fun a b : d => Z (a, i) (b, j))) = 0 :=
    hT _
  simpa [partialTraceLeft, tensorWithIdentity, Matrix.trace] using htrace
```

## Block-by-block explanation

The explanation below follows the declaration block by block. Each block groups a coherent piece of the definition or proof, so the mathematical structure is easier to see than in a strictly line-oriented reading.

1. Code:
```lean
/-- Tensoring a trace-annihilating map with the identity has vanishing left partial trace. -/
```
This is a Lean docstring. It is a human-written comment that tells readers what the declaration is meant to express before the formal code begins.

2. Code:
```lean
theorem partialTraceLeft_tensor_zero
```
This line starts the `partialTraceLeft_tensor_zero` declaration. Because it begins with `theorem`, Lean now knows what kind of named object is being introduced.

3. Code:
```lean
    {d k : Type u} [Fintype d] [DecidableEq d] [Fintype k] [DecidableEq k]
```
This line is one local step in the declaration. It either refines the formula being defined or advances the proof by a small algebraic or logical move.  A bracket such as `[Fintype d]` tells Lean that the index set `d` is finite, so sums over all indices make sense.  A bracket such as `[DecidableEq d]` tells Lean that it can decide whether two indices are equal.

4. Code:
```lean
    (Ψ : Channel d) (hT : IsTraceAnnihilating Ψ)
```
This line is one local step in the declaration. It either refines the formula being defined or advances the proof by a small algebraic or logical move.  `Channel d` is an abbreviation for a complex-linear map from operators on `d` to operators on `d`.

5. Code:
```lean
    (Z : Matrix (d × k) (d × k) ℂ) :
```
This line is one local step in the declaration. It either refines the formula being defined or advances the proof by a small algebraic or logical move.  `Matrix d d ℂ` means a square matrix with complex entries; the index type `d` tells Lean which rows and columns exist.

6. Code:
```lean
    partialTraceLeft d k (tensorWithIdentity d k Ψ Z) = 0 := by
```
This line says that a proof script begins here. Everything indented underneath is a sequence of instructions that Lean will check step by step.

7. Code:
```lean
  ext i j
```
This line invokes extensionality. To prove two maps or matrices are equal, Lean reduces the problem to checking their values entry by entry.

8. Code:
```lean
  have htrace :
```
This line introduces an intermediate claim. The proof pauses to establish a fact that will be used shortly afterwards.

9. Code:
```lean
      Matrix.trace (Ψ (fun a b : d => Z (a, i) (b, j))) = 0 :=
```
This line is one local step in the declaration. It either refines the formula being defined or advances the proof by a small algebraic or logical move.

10. Code:
```lean
    hT _
```
This line is one local step in the declaration. It either refines the formula being defined or advances the proof by a small algebraic or logical move.

11. Code:
```lean
  simpa [partialTraceLeft, tensorWithIdentity, Matrix.trace] using htrace
```
This line simplifies the goal using definitions and known equalities. `simpa` means that, after simplification, the desired statement matches a theorem Lean already has.

## Mathematical summary

Restated without Lean syntax, `partialTraceLeft_tensor_zero` is the theorem or lemma written above.

- State the desired identity or inequality in Lean’s syntax.
- Introduce temporary names and intermediate claims that organize the argument.
- Use rewriting, simplification, and earlier lemmas to reduce the goal to standard matrix or norm manipulations.
- Close the remaining algebraic or order-theoretic steps with Lean’s proof tactics.

## Dependencies and downstream use

### Earlier declarations this depends on
- [`Channel`](../Setups/Channel.md) from `Setups.lean`
- [`IsTraceAnnihilating`](../Setups/IsTraceAnnihilating.md) from `Setups.lean`
- [`tensorWithIdentity`](../Setups/tensorWithIdentity.md) from `Setups.lean`
- [`partialTraceLeft`](../Setups/partialTraceLeft.md) from `Setups.lean`

### Later declarations that use this one
- [`tensorWithIdentity_trace_zero`](tensorWithIdentity_trace_zero.md) in `StandardFacts.lean`

## Backlinks

- [Back to `INDEX.md`](../INDEX.md)
- [Back to the `StandardFacts.lean` section in the index](../INDEX.md#diamond-standardfacts-lean)
- [Previous declaration in this file](trace_eq_trace_partialTraceLeft.md)
- [Next declaration in this file](tensorWithIdentity_trace_zero.md)