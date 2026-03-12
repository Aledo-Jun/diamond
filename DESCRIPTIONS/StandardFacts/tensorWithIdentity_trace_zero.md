# tensorWithIdentity_trace_zero

## Source location

- Original Lean file: `Diamond/StandardFacts.lean`
- Declaration name: `tensorWithIdentity_trace_zero`
- Declaration kind: `theorem`

## Why this declaration exists

Tensoring a trace-annihilating map with the identity gives traceless output.

 In the file `StandardFacts.lean`, it contributes to helper facts and background axioms that the paper treats as standard or external input. Later proofs call this result by name, so documenting it makes the larger argument readable as a mathematical chain rather than as opaque proof script.

## Original code

```lean
/-- Tensoring a trace-annihilating map with the identity gives traceless output. -/
theorem tensorWithIdentity_trace_zero
    {d k : Type u} [Fintype d] [DecidableEq d] [Fintype k] [DecidableEq k]
    (Ψ : Channel d) (hT : IsTraceAnnihilating Ψ)
    (Z : Matrix (d × k) (d × k) ℂ) :
    Matrix.trace (tensorWithIdentity d k Ψ Z) = 0 := by
  rw [trace_eq_trace_partialTraceLeft]
  simpa using
    congrArg Matrix.trace (partialTraceLeft_tensor_zero (d := d) (k := k) Ψ hT Z)
```

## Line-by-line explanation

The explanation below follows the declaration one physical line at a time. For long proofs, some lines are tiny bookkeeping steps; those are still explained, but briefly.

1. Code:
```lean
/-- Tensoring a trace-annihilating map with the identity gives traceless output. -/
```
This is a Lean docstring. It is a human-written comment that tells readers what the declaration is meant to express before the formal code begins.

2. Code:
```lean
theorem tensorWithIdentity_trace_zero
```
This line starts the `tensorWithIdentity_trace_zero` declaration. Because it begins with `theorem`, Lean now knows what kind of named object is being introduced.

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
    Matrix.trace (tensorWithIdentity d k Ψ Z) = 0 := by
```
This line says that a proof script begins here. Everything indented underneath is a sequence of instructions that Lean will check step by step.

7. Code:
```lean
  rw [trace_eq_trace_partialTraceLeft]
```
This line uses rewriting. Lean replaces one expression by an equal expression using the lemmas listed in brackets.

8. Code:
```lean
  simpa using
```
This line simplifies the goal using definitions and known equalities. `simpa` means that, after simplification, the desired statement matches a theorem Lean already has.

9. Code:
```lean
    congrArg Matrix.trace (partialTraceLeft_tensor_zero (d := d) (k := k) Ψ hT Z)
```
This line applies the same function to both sides of a known equality, producing a new equality better suited to the current goal.

## Mathematical summary

Restated without Lean syntax, `tensorWithIdentity_trace_zero` is the theorem or lemma written above.

- State the desired identity or inequality in Lean’s syntax.
- Introduce temporary names and intermediate claims that organize the argument.
- Use rewriting, simplification, and earlier lemmas to reduce the goal to standard matrix or norm manipulations.
- Close the remaining algebraic or order-theoretic steps with Lean’s proof tactics.

## Dependencies and downstream use

### Earlier declarations this depends on
- [`Channel`](../Setups/Channel.md) from `Setups.lean`
- [`IsTraceAnnihilating`](../Setups/IsTraceAnnihilating.md) from `Setups.lean`
- [`tensorWithIdentity`](../Setups/tensorWithIdentity.md) from `Setups.lean`
- [`trace_eq_trace_partialTraceLeft`](trace_eq_trace_partialTraceLeft.md) from `StandardFacts.lean`
- [`partialTraceLeft_tensor_zero`](partialTraceLeft_tensor_zero.md) from `StandardFacts.lean`

### Later declarations that use this one
- [`theorem1`](../Theorem/Theorem1/theorem1.md) in `Theorem/Theorem1.lean`
- [`remark1`](../Theorem/Remark1/remark1.md) in `Theorem/Remark1.lean`
- [`theorem_not_tight`](../PositiveGap/NotTight/theorem_not_tight.md) in `PositiveGap/NotTight.lean`

## Backlinks

- [Back to `INDEX.md`](../INDEX.md)
- [Back to the `StandardFacts.lean` section in the index](../INDEX.md#diamond-standardfacts-lean)
- [Previous declaration in this file](partialTraceLeft_tensor_zero.md)
- [Next declaration in this file](tensorWithIdentity_hermitian.md)