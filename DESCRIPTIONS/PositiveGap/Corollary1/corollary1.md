# corollary1

## Source location

- Original Lean file: `Diamond/PositiveGap/Corollary1.lean`
- Declaration name: `corollary1`
- Declaration kind: `theorem`

## Why this declaration exists

This corollary applies Lemma 4 to the difference map `idMinus T` and gets a vanishing partial trace.

 In the file `PositiveGap/Corollary1.lean`, it contributes to the immediate zero-partial-trace consequence for `idMinus T`. Later proofs call this result by name, so documenting it makes the larger argument readable as a mathematical chain rather than as opaque proof script.

## Original code

```lean
/-- Paper Corollary 1. -/
theorem corollary1
    {d : Type u} [Fintype d] [DecidableEq d]
    (T : Channel d) (hT : IsQuantumChannel T)
    (ρ : Matrix (d × d) (d × d) ℂ) :
    partialTraceLeft d d (tensorWithIdentity d d (idMinus T) ρ) = 0 := by
  ext i j
  calc
    partialTraceLeft d d (tensorWithIdentity d d (idMinus T) ρ) i j
      = partialTraceLeft d d ρ i j -
          partialTraceLeft d d (tensorWithIdentity d d T ρ) i j := by
            simp [partialTraceLeft, tensorWithIdentity, idMinus, Finset.sum_sub_distrib]
    _ = 0 := by
          rw [lemma4 T hT ρ]
          ring
```

## Line-by-line explanation

The explanation below follows the declaration one physical line at a time. For long proofs, some lines are tiny bookkeeping steps; those are still explained, but briefly.

1. Code:
```lean
/-- Paper Corollary 1. -/
```
This is a Lean docstring. It is a human-written comment that tells readers what the declaration is meant to express before the formal code begins.

2. Code:
```lean
theorem corollary1
```
This line starts the `corollary1` declaration. Because it begins with `theorem`, Lean now knows what kind of named object is being introduced.

3. Code:
```lean
    {d : Type u} [Fintype d] [DecidableEq d]
```
This line is one local step in the declaration. It either refines the formula being defined or advances the proof by a small algebraic or logical move.  A bracket such as `[Fintype d]` tells Lean that the index set `d` is finite, so sums over all indices make sense.  A bracket such as `[DecidableEq d]` tells Lean that it can decide whether two indices are equal.

4. Code:
```lean
    (T : Channel d) (hT : IsQuantumChannel T)
```
This line is one local step in the declaration. It either refines the formula being defined or advances the proof by a small algebraic or logical move.  `Channel d` is an abbreviation for a complex-linear map from operators on `d` to operators on `d`.

5. Code:
```lean
    (ρ : Matrix (d × d) (d × d) ℂ) :
```
This line is one local step in the declaration. It either refines the formula being defined or advances the proof by a small algebraic or logical move.  `Matrix d d ℂ` means a square matrix with complex entries; the index type `d` tells Lean which rows and columns exist.

6. Code:
```lean
    partialTraceLeft d d (tensorWithIdentity d d (idMinus T) ρ) = 0 := by
```
This line says that a proof script begins here. Everything indented underneath is a sequence of instructions that Lean will check step by step.

7. Code:
```lean
  ext i j
```
This line invokes extensionality. To prove two maps or matrices are equal, Lean reduces the problem to checking their values entry by entry.

8. Code:
```lean
  calc
```
This line begins a chained calculation. Each displayed step that follows must be justified by the indented proof after `:= by`.

9. Code:
```lean
    partialTraceLeft d d (tensorWithIdentity d d (idMinus T) ρ) i j
```
This line is one local step in the declaration. It either refines the formula being defined or advances the proof by a small algebraic or logical move.

10. Code:
```lean
      = partialTraceLeft d d ρ i j -
```
This line is one local step in the declaration. It either refines the formula being defined or advances the proof by a small algebraic or logical move.

11. Code:
```lean
          partialTraceLeft d d (tensorWithIdentity d d T ρ) i j := by
```
This line says that a proof script begins here. Everything indented underneath is a sequence of instructions that Lean will check step by step.

12. Code:
```lean
            simp [partialTraceLeft, tensorWithIdentity, idMinus, Finset.sum_sub_distrib]
```
This line simplifies the goal using definitions and known equalities. `simpa` means that, after simplification, the desired statement matches a theorem Lean already has.

13. Code:
```lean
    _ = 0 := by
```
This line says that a proof script begins here. Everything indented underneath is a sequence of instructions that Lean will check step by step.

14. Code:
```lean
          rw [lemma4 T hT ρ]
```
This line uses rewriting. Lean replaces one expression by an equal expression using the lemmas listed in brackets.

15. Code:
```lean
          ring
```
This line normalizes an algebraic identity in a commutative ring, just as one would expand and collect like terms by hand.

## Mathematical summary

Restated without Lean syntax, `corollary1` is the theorem or lemma written above.

- State the desired identity or inequality in Lean’s syntax.
- Introduce temporary names and intermediate claims that organize the argument.
- Use rewriting, simplification, and earlier lemmas to reduce the goal to standard matrix or norm manipulations.
- Close the remaining algebraic or order-theoretic steps with Lean’s proof tactics.

## Dependencies and downstream use

### Earlier declarations this depends on
- [`Channel`](../../Setups/Channel.md) from `Setups.lean`
- [`IsQuantumChannel`](../../Setups/IsQuantumChannel.md) from `Setups.lean`
- [`tensorWithIdentity`](../../Setups/tensorWithIdentity.md) from `Setups.lean`
- [`partialTraceLeft`](../../Setups/partialTraceLeft.md) from `Setups.lean`
- [`idMinus`](../../Setups/idMinus.md) from `Setups.lean`
- [`lemma4`](../Lemma4/lemma4.md) from `PositiveGap/Lemma4.lean`

### Later declarations that use this one
- [`theorem_not_tight`](../NotTight/theorem_not_tight.md) in `PositiveGap/NotTight.lean`

## Backlinks

- [Back to `INDEX.md`](../../INDEX.md)
- [Back to the `PositiveGap/Corollary1.lean` section in the index](../../INDEX.md#diamond-positivegap-corollary1-lean)