# quantumChannel_has_kraus

## Source location

- Original Lean file: `Diamond/StandardFacts.lean`
- Declaration name: `quantumChannel_has_kraus`
- Declaration kind: `axiom`

## Why this declaration exists

This axiom imports the standard finite-dimensional Kraus representation theorem for quantum channels.

 In the file `StandardFacts.lean`, it contributes to helper facts and background axioms that the paper treats as standard or external input. Later proofs call this result by name, so documenting it makes the larger argument readable as a mathematical chain rather than as opaque proof script.

## Original code

```lean
/-- Background Kraus representation for finite-dimensional quantum channels. -/
axiom quantumChannel_has_kraus
    {d : Type u} [Fintype d] [DecidableEq d] {T : Channel d} :
    IsQuantumChannel T →
    ∃ (r : ℕ), ∃ (E : Fin r → Matrix d d ℂ),
      (∀ X, T X = ∑ i, E i * X * (E i)ᴴ) ∧
      (∑ i, (E i)ᴴ * E i = 1)
```

## Line-by-line explanation

The explanation below follows the declaration one physical line at a time. For long proofs, some lines are tiny bookkeeping steps; those are still explained, but briefly.

1. Code:
```lean
/-- Background Kraus representation for finite-dimensional quantum channels. -/
```
This is a Lean docstring. It is a human-written comment that tells readers what the declaration is meant to express before the formal code begins.

2. Code:
```lean
axiom quantumChannel_has_kraus
```
This line starts the `quantumChannel_has_kraus` declaration. Because it begins with `axiom`, Lean now knows what kind of named object is being introduced.

3. Code:
```lean
    {d : Type u} [Fintype d] [DecidableEq d] {T : Channel d} :
```
This line is one local step in the declaration. It either refines the formula being defined or advances the proof by a small algebraic or logical move.  `Channel d` is an abbreviation for a complex-linear map from operators on `d` to operators on `d`.  A bracket such as `[Fintype d]` tells Lean that the index set `d` is finite, so sums over all indices make sense.  A bracket such as `[DecidableEq d]` tells Lean that it can decide whether two indices are equal.

4. Code:
```lean
    IsQuantumChannel T →
```
This line is one local step in the declaration. It either refines the formula being defined or advances the proof by a small algebraic or logical move.  `Channel d` is an abbreviation for a complex-linear map from operators on `d` to operators on `d`.

5. Code:
```lean
    ∃ (r : ℕ), ∃ (E : Fin r → Matrix d d ℂ),
```
This line is one local step in the declaration. It either refines the formula being defined or advances the proof by a small algebraic or logical move.  `Matrix d d ℂ` means a square matrix with complex entries; the index type `d` tells Lean which rows and columns exist.

6. Code:
```lean
      (∀ X, T X = ∑ i, E i * X * (E i)ᴴ) ∧
```
This line is one local step in the declaration. It either refines the formula being defined or advances the proof by a small algebraic or logical move.  The superscript `ᴴ` means conjugate transpose (also called the adjoint).

7. Code:
```lean
      (∑ i, (E i)ᴴ * E i = 1)
```
This line is one local step in the declaration. It either refines the formula being defined or advances the proof by a small algebraic or logical move.  The superscript `ᴴ` means conjugate transpose (also called the adjoint).

## Mathematical summary

Restated without Lean syntax, `quantumChannel_has_kraus` is the theorem or lemma written above.

- State the desired identity or inequality in Lean’s syntax.
- Introduce temporary names and intermediate claims that organize the argument.
- Use rewriting, simplification, and earlier lemmas to reduce the goal to standard matrix or norm manipulations.
- Close the remaining algebraic or order-theoretic steps with Lean’s proof tactics.

## Dependencies and downstream use

### Earlier declarations this depends on
- [`Channel`](../Setups/Channel.md) from `Setups.lean`
- [`IsQuantumChannel`](../Setups/IsQuantumChannel.md) from `Setups.lean`

### Later declarations that use this one
- [`lemma4`](../PositiveGap/Lemma4/lemma4.md) in `PositiveGap/Lemma4.lean`

## Backlinks

- [Back to `INDEX.md`](../INDEX.md)
- [Back to the `StandardFacts.lean` section in the index](../INDEX.md#diamond-standardfacts-lean)
- [Previous declaration in this file](hsNormOp_eq_zero_iff.md)
- [Next declaration in this file](tensorWithIdentity_comp_transpose.md)