# trace_Ud_eq_zero

## Source location

- Original Lean file: `Diamond/StandardFacts.lean`
- Declaration name: `trace_Ud_eq_zero`
- Declaration kind: `axiom`

## Why this declaration exists

Background roots-of-unity trace identity for the phase unitary `U_d`.

 In the file `StandardFacts.lean`, it contributes to helper facts and background axioms that the paper treats as standard or external input. Later proofs call this result by name, so documenting it makes the larger argument readable as a mathematical chain rather than as opaque proof script.

## Original code

```lean
/-- Background roots-of-unity trace identity for the phase unitary `U_d`. -/
axiom trace_Ud_eq_zero (d : ℕ) [Fact (1 < d)] :
    Matrix.trace (Ud d) = 0
```

## Line-by-line explanation

The explanation below follows the declaration one physical line at a time. For long proofs, some lines are tiny bookkeeping steps; those are still explained, but briefly.

1. Code:
```lean
/-- Background roots-of-unity trace identity for the phase unitary `U_d`. -/
```
This is a Lean docstring. It is a human-written comment that tells readers what the declaration is meant to express before the formal code begins.

2. Code:
```lean
axiom trace_Ud_eq_zero (d : ℕ) [Fact (1 < d)] :
```
This line starts the `trace_Ud_eq_zero` declaration. Because it begins with `axiom`, Lean now knows what kind of named object is being introduced.

3. Code:
```lean
    Matrix.trace (Ud d) = 0
```
This line is one local step in the declaration. It either refines the formula being defined or advances the proof by a small algebraic or logical move.

## Mathematical summary

Restated without Lean syntax, `trace_Ud_eq_zero` is the theorem or lemma written above.

- State the desired identity or inequality in Lean’s syntax.
- Introduce temporary names and intermediate claims that organize the argument.
- Use rewriting, simplification, and earlier lemmas to reduce the goal to standard matrix or norm manipulations.
- Close the remaining algebraic or order-theoretic steps with Lean’s proof tactics.

## Dependencies and downstream use

### Earlier declarations this depends on
- [`Ud`](../Setups/Ud.md) from `Setups.lean`

### Later declarations that use this one
- [`theorem_eq8`](../EndMatter/Eq8/theorem_eq8.md) in `EndMatter/Eq8.lean`

## Backlinks

- [Back to `INDEX.md`](../INDEX.md)
- [Back to the `StandardFacts.lean` section in the index](../INDEX.md#diamond-standardfacts-lean)
- [Previous declaration in this file](unitary_channel_diamond_distance_eq_two_of_trace_zero.md)
- [Next declaration in this file](exists_maximizing_state.md)