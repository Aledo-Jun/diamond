# idMinus_isTraceAnnihilating

## Source location

- Original Lean file: `Diamond/StandardFacts.lean`
- Declaration name: `idMinus_isTraceAnnihilating`
- Declaration kind: `theorem`

## Why this declaration exists

`idMinus` is trace-annihilating for CPTP channels.

 In the file `StandardFacts.lean`, it contributes to helper facts and background axioms that the paper treats as standard or external input. Later proofs call this result by name, so documenting it makes the larger argument readable as a mathematical chain rather than as opaque proof script.

## Original code

```lean
/-- `idMinus` is trace-annihilating for CPTP channels. -/
theorem idMinus_isTraceAnnihilating
    {d : Type u} [Fintype d] [DecidableEq d] (T : Channel d) (hT : IsQuantumChannel T) :
    IsTraceAnnihilating (idMinus T) := by
  intro X
  simp [idMinus, hT.trace_preserving]
```

## Line-by-line explanation

The explanation below follows the declaration one physical line at a time. For long proofs, some lines are tiny bookkeeping steps; those are still explained, but briefly.

1. Code:
```lean
/-- `idMinus` is trace-annihilating for CPTP channels. -/
```
This is a Lean docstring. It is a human-written comment that tells readers what the declaration is meant to express before the formal code begins.

2. Code:
```lean
theorem idMinus_isTraceAnnihilating
```
This line starts the `idMinus_isTraceAnnihilating` declaration. Because it begins with `theorem`, Lean now knows what kind of named object is being introduced.

3. Code:
```lean
    {d : Type u} [Fintype d] [DecidableEq d] (T : Channel d) (hT : IsQuantumChannel T) :
```
This line is one local step in the declaration. It either refines the formula being defined or advances the proof by a small algebraic or logical move.  `Channel d` is an abbreviation for a complex-linear map from operators on `d` to operators on `d`.  A bracket such as `[Fintype d]` tells Lean that the index set `d` is finite, so sums over all indices make sense.  A bracket such as `[DecidableEq d]` tells Lean that it can decide whether two indices are equal.

4. Code:
```lean
    IsTraceAnnihilating (idMinus T) := by
```
This line says that a proof script begins here. Everything indented underneath is a sequence of instructions that Lean will check step by step.

5. Code:
```lean
  intro X
```
This line introduces the variable or hypothesis named here into the proof context. In ordinary mathematical prose, it is the same as saying “let” or “assume”.

6. Code:
```lean
  simp [idMinus, hT.trace_preserving]
```
This line simplifies the goal using definitions and known equalities. `simpa` means that, after simplification, the desired statement matches a theorem Lean already has.

## Mathematical summary

Restated without Lean syntax, `idMinus_isTraceAnnihilating` is the theorem or lemma written above.

- State the desired identity or inequality in Lean’s syntax.
- Introduce temporary names and intermediate claims that organize the argument.
- Use rewriting, simplification, and earlier lemmas to reduce the goal to standard matrix or norm manipulations.
- Close the remaining algebraic or order-theoretic steps with Lean’s proof tactics.

## Dependencies and downstream use

### Earlier declarations this depends on
- [`Channel`](../Setups/Channel.md) from `Setups.lean`
- [`IsQuantumChannel`](../Setups/IsQuantumChannel.md) from `Setups.lean`
- [`IsTraceAnnihilating`](../Setups/IsTraceAnnihilating.md) from `Setups.lean`
- [`idMinus`](../Setups/idMinus.md) from `Setups.lean`

### Later declarations that use this one
- [`theorem1`](../Theorem/Theorem1/theorem1.md) in `Theorem/Theorem1.lean`
- [`theorem_not_tight`](../PositiveGap/NotTight/theorem_not_tight.md) in `PositiveGap/NotTight.lean`
- [`corollary2_linear_bound`](../EndMatter/Corollary2/corollary2_linear_bound.md) in `EndMatter/Corollary2.lean`

## Backlinks

- [Back to `INDEX.md`](../INDEX.md)
- [Back to the `StandardFacts.lean` section in the index](../INDEX.md#diamond-standardfacts-lean)
- [Previous declaration in this file](idMinus_isHermiticityPreserving.md)
- [Next declaration in this file](adMap_isQuantumChannel.md)