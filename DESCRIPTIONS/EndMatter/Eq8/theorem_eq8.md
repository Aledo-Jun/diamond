# theorem_eq8

## Source location

- Original Lean file: `Diamond/EndMatter/Eq8.lean`
- Declaration name: `theorem_eq8`
- Declaration kind: `theorem`

## Why this declaration exists

This theorem proves the paper's Eq. (8), namely that the diamond distance between the identity and the special unitary channel is exactly $2$.

 In the file `EndMatter/Eq8.lean`, it contributes to the proof of Eq. (8) and the lower bound on the universal constant. Later proofs call this result by name, so documenting it makes the larger argument readable as a mathematical chain rather than as opaque proof script.

## Original code

```lean
/-- Paper Eq. (8): the unitary channel `Ad_{U_d}` sits at diamond distance `2`
    from the identity. -/
theorem theorem_eq8 (d : ℕ) [Fact (1 < d)] :
    diamondOp (idMinus (adMap (Fin d) (Ud d))) = 2 := by
  exact unitary_channel_diamond_distance_eq_two_of_trace_zero
    (U := Ud d) (hU := ud_conjTranspose_mul_self d) (htrace := trace_Ud_eq_zero d)
```

## Line-by-line explanation

The explanation below follows the declaration one physical line at a time. For long proofs, some lines are tiny bookkeeping steps; those are still explained, but briefly.

1. Code:
```lean
/-- Paper Eq. (8): the unitary channel `Ad_{U_d}` sits at diamond distance `2`
```
This is a Lean docstring. It is a human-written comment that tells readers what the declaration is meant to express before the formal code begins.

2. Code:
```lean
    from the identity. -/
```
This line is one local step in the declaration. It either refines the formula being defined or advances the proof by a small algebraic or logical move.

3. Code:
```lean
theorem theorem_eq8 (d : ℕ) [Fact (1 < d)] :
```
This line starts the `theorem_eq8` declaration. Because it begins with `theorem`, Lean now knows what kind of named object is being introduced.

4. Code:
```lean
    diamondOp (idMinus (adMap (Fin d) (Ud d))) = 2 := by
```
This line says that a proof script begins here. Everything indented underneath is a sequence of instructions that Lean will check step by step.

5. Code:
```lean
  exact unitary_channel_diamond_distance_eq_two_of_trace_zero
```
This line finishes the current goal by giving Lean the exact theorem, lemma, or term that proves it.

6. Code:
```lean
    (U := Ud d) (hU := ud_conjTranspose_mul_self d) (htrace := trace_Ud_eq_zero d)
```
This line is one local step in the declaration. It either refines the formula being defined or advances the proof by a small algebraic or logical move.

## Mathematical summary

Restated without Lean syntax, `theorem_eq8` is the theorem or lemma written above.

- State the desired identity or inequality in Lean’s syntax.
- Introduce temporary names and intermediate claims that organize the argument.
- Use rewriting, simplification, and earlier lemmas to reduce the goal to standard matrix or norm manipulations.
- Close the remaining algebraic or order-theoretic steps with Lean’s proof tactics.

## Dependencies and downstream use

### Earlier declarations this depends on
- [`diamondOp`](../../Setups/diamondOp.md) from `Setups.lean`
- [`idMinus`](../../Setups/idMinus.md) from `Setups.lean`
- [`adMap`](../../Setups/adMap.md) from `Setups.lean`
- [`Ud`](../../Setups/Ud.md) from `Setups.lean`
- [`unitary_channel_diamond_distance_eq_two_of_trace_zero`](../../StandardFacts/unitary_channel_diamond_distance_eq_two_of_trace_zero.md) from `StandardFacts.lean`
- [`trace_Ud_eq_zero`](../../StandardFacts/trace_Ud_eq_zero.md) from `StandardFacts.lean`
- [`ud_conjTranspose_mul_self`](../Eq7/ud_conjTranspose_mul_self.md) from `EndMatter/Eq7.lean`

### Later declarations that use this one
- [`alpha_lower_bound`](alpha_lower_bound.md) in `EndMatter/Eq8.lean`

## Backlinks

- [Back to `INDEX.md`](../../INDEX.md)
- [Back to the `EndMatter/Eq8.lean` section in the index](../../INDEX.md#diamond-endmatter-eq8-lean)
- [Next declaration in this file](alpha_lower_bound.md)