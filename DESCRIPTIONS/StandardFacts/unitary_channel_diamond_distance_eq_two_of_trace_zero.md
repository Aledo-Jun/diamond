# unitary_channel_diamond_distance_eq_two_of_trace_zero

## Source location

- Original Lean file: `Diamond/StandardFacts.lean`
- Declaration name: `unitary_channel_diamond_distance_eq_two_of_trace_zero`
- Declaration kind: `axiom`

## Why this declaration exists

This axiom imports the standard unitary-channel distance formula used for Eq. (8).

 In the file `StandardFacts.lean`, it contributes to helper facts and background axioms that the paper treats as standard or external input. Later proofs call this result by name, so documenting it makes the larger argument readable as a mathematical chain rather than as opaque proof script.

## Original code

```lean
/-- Background unitary-channel diamond-distance formula used for Eq. (8). -/
axiom unitary_channel_diamond_distance_eq_two_of_trace_zero
    {d : Type u} [Fintype d] [DecidableEq d] (U : Matrix d d ℂ) (hU : Uᴴ * U = 1)
    (htrace : Matrix.trace U = 0) :
    diamondOp (idMinus (adMap d U)) = 2
```

## Line-by-line explanation

The explanation below follows the declaration one physical line at a time. For long proofs, some lines are tiny bookkeeping steps; those are still explained, but briefly.

1. Code:
```lean
/-- Background unitary-channel diamond-distance formula used for Eq. (8). -/
```
This is a Lean docstring. It is a human-written comment that tells readers what the declaration is meant to express before the formal code begins.

2. Code:
```lean
axiom unitary_channel_diamond_distance_eq_two_of_trace_zero
```
This line starts the `unitary_channel_diamond_distance_eq_two_of_trace_zero` declaration. Because it begins with `axiom`, Lean now knows what kind of named object is being introduced.

3. Code:
```lean
    {d : Type u} [Fintype d] [DecidableEq d] (U : Matrix d d ℂ) (hU : Uᴴ * U = 1)
```
This line is one local step in the declaration. It either refines the formula being defined or advances the proof by a small algebraic or logical move.  `Matrix d d ℂ` means a square matrix with complex entries; the index type `d` tells Lean which rows and columns exist.  A bracket such as `[Fintype d]` tells Lean that the index set `d` is finite, so sums over all indices make sense.  A bracket such as `[DecidableEq d]` tells Lean that it can decide whether two indices are equal.  The superscript `ᴴ` means conjugate transpose (also called the adjoint).

4. Code:
```lean
    (htrace : Matrix.trace U = 0) :
```
This line is one local step in the declaration. It either refines the formula being defined or advances the proof by a small algebraic or logical move.

5. Code:
```lean
    diamondOp (idMinus (adMap d U)) = 2
```
This line is one local step in the declaration. It either refines the formula being defined or advances the proof by a small algebraic or logical move.

## Mathematical summary

Restated without Lean syntax, `unitary_channel_diamond_distance_eq_two_of_trace_zero` is the theorem or lemma written above.

- State the desired identity or inequality in Lean’s syntax.
- Introduce temporary names and intermediate claims that organize the argument.
- Use rewriting, simplification, and earlier lemmas to reduce the goal to standard matrix or norm manipulations.
- Close the remaining algebraic or order-theoretic steps with Lean’s proof tactics.

## Dependencies and downstream use

### Earlier declarations this depends on
- [`diamondOp`](../Setups/diamondOp.md) from `Setups.lean`
- [`idMinus`](../Setups/idMinus.md) from `Setups.lean`
- [`adMap`](../Setups/adMap.md) from `Setups.lean`

### Later declarations that use this one
- [`theorem_eq8`](../EndMatter/Eq8/theorem_eq8.md) in `EndMatter/Eq8.lean`

## Backlinks

- [Back to `INDEX.md`](../INDEX.md)
- [Back to the `StandardFacts.lean` section in the index](../INDEX.md#diamond-standardfacts-lean)
- [Previous declaration in this file](lemma_transpose_diamond.md)
- [Next declaration in this file](trace_Ud_eq_zero.md)