# traceNormOp_density_eq_one

## Source location

- Original Lean file: `Diamond/Theorem/Lemma1.lean`
- Declaration name: `traceNormOp_density_eq_one`
- Declaration kind: `theorem`

## Why this declaration exists

Density states have concrete trace norm `1`.

 In the file `Theorem/Lemma1.lean`, it contributes to the proof infrastructure for the first norm inequality and the public theorem `lemma1`. Later proofs call this result by name, so documenting it makes the larger argument readable as a mathematical chain rather than as opaque proof script.

## Original code

```lean
/-- Density states have concrete trace norm `1`. -/
private theorem traceNormOp_density_eq_one
    {d : Type u} [Fintype d] [DecidableEq d]
    {ρ : Matrix d d ℂ} (hρ : IsDensityState ρ) :
    traceNormOp ρ = 1 := by
  rw [traceNormOp_posSemidef_eq_trace hρ.1, hρ.2]
  simp
```

## Line-by-line explanation

The explanation below follows the declaration one physical line at a time. For long proofs, some lines are tiny bookkeeping steps; those are still explained, but briefly.

1. Code:
```lean
/-- Density states have concrete trace norm `1`. -/
```
This is a Lean docstring. It is a human-written comment that tells readers what the declaration is meant to express before the formal code begins.

2. Code:
```lean
private theorem traceNormOp_density_eq_one
```
This line starts the `traceNormOp_density_eq_one` declaration. Because it begins with `theorem`, Lean now knows what kind of named object is being introduced.

3. Code:
```lean
    {d : Type u} [Fintype d] [DecidableEq d]
```
This line is one local step in the declaration. It either refines the formula being defined or advances the proof by a small algebraic or logical move.  A bracket such as `[Fintype d]` tells Lean that the index set `d` is finite, so sums over all indices make sense.  A bracket such as `[DecidableEq d]` tells Lean that it can decide whether two indices are equal.

4. Code:
```lean
    {ρ : Matrix d d ℂ} (hρ : IsDensityState ρ) :
```
This line is one local step in the declaration. It either refines the formula being defined or advances the proof by a small algebraic or logical move.  `Matrix d d ℂ` means a square matrix with complex entries; the index type `d` tells Lean which rows and columns exist.

5. Code:
```lean
    traceNormOp ρ = 1 := by
```
This line says that a proof script begins here. Everything indented underneath is a sequence of instructions that Lean will check step by step.

6. Code:
```lean
  rw [traceNormOp_posSemidef_eq_trace hρ.1, hρ.2]
```
This line uses rewriting. Lean replaces one expression by an equal expression using the lemmas listed in brackets.

7. Code:
```lean
  simp
```
This line simplifies the goal using definitions and known equalities. `simpa` means that, after simplification, the desired statement matches a theorem Lean already has.

## Mathematical summary

Restated without Lean syntax, `traceNormOp_density_eq_one` is the theorem or lemma written above.

- State the desired identity or inequality in Lean’s syntax.
- Introduce temporary names and intermediate claims that organize the argument.
- Use rewriting, simplification, and earlier lemmas to reduce the goal to standard matrix or norm manipulations.
- Close the remaining algebraic or order-theoretic steps with Lean’s proof tactics.

## Dependencies and downstream use

### Earlier declarations this depends on
- [`traceNormOp`](../../Setups/traceNormOp.md) from `Setups.lean`
- [`IsDensityState`](../../Setups/IsDensityState.md) from `Setups.lean`
- [`traceNormOp_posSemidef_eq_trace`](traceNormOp_posSemidef_eq_trace.md) from `Theorem/Lemma1.lean`

### Later declarations that use this one
- No later documented declaration mentions this name explicitly.

## Backlinks

- [Back to `INDEX.md`](../../INDEX.md)
- [Back to the `Theorem/Lemma1.lean` section in the index](../../INDEX.md#diamond-theorem-lemma1-lean)
- [Previous declaration in this file](traceNormOp_posSemidef_eq_trace.md)
- [Next declaration in this file](traceNormOp_sub_density_le_two.md)