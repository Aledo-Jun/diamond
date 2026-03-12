# trace_eq_trace_partialTraceLeft

## Source location

- Original Lean file: `Diamond/StandardFacts.lean`
- Declaration name: `trace_eq_trace_partialTraceLeft`
- Declaration kind: `theorem`

## Why this declaration exists

Trace equals the trace of the left partial trace.

 In the file `StandardFacts.lean`, it contributes to helper facts and background axioms that the paper treats as standard or external input. Later proofs call this result by name, so documenting it makes the larger argument readable as a mathematical chain rather than as opaque proof script.

## Original code

```lean
/-- Trace equals the trace of the left partial trace. -/
theorem trace_eq_trace_partialTraceLeft
    {d k : Type u} [Fintype d] [DecidableEq d] [Fintype k] [DecidableEq k]
    (X : Matrix (d × k) (d × k) ℂ) :
    Matrix.trace X = Matrix.trace (partialTraceLeft d k X) := by
  calc
    Matrix.trace X = ∑ a : d, ∑ i : k, X (a, i) (a, i) := by
      simp [Matrix.trace, Fintype.sum_prod_type]
    _ = ∑ i : k, ∑ a : d, X (a, i) (a, i) := by
      simpa using
        (Finset.sum_comm
          (s := (Finset.univ : Finset d))
          (t := (Finset.univ : Finset k))
          (f := fun a i => X (a, i) (a, i)))
    _ = Matrix.trace (partialTraceLeft d k X) := by
      simp [partialTraceLeft, Matrix.trace]
```

## Line-by-line explanation

The explanation below follows the declaration one physical line at a time. For long proofs, some lines are tiny bookkeeping steps; those are still explained, but briefly.

1. Code:
```lean
/-- Trace equals the trace of the left partial trace. -/
```
This is a Lean docstring. It is a human-written comment that tells readers what the declaration is meant to express before the formal code begins.

2. Code:
```lean
theorem trace_eq_trace_partialTraceLeft
```
This line starts the `trace_eq_trace_partialTraceLeft` declaration. Because it begins with `theorem`, Lean now knows what kind of named object is being introduced.

3. Code:
```lean
    {d k : Type u} [Fintype d] [DecidableEq d] [Fintype k] [DecidableEq k]
```
This line is one local step in the declaration. It either refines the formula being defined or advances the proof by a small algebraic or logical move.  A bracket such as `[Fintype d]` tells Lean that the index set `d` is finite, so sums over all indices make sense.  A bracket such as `[DecidableEq d]` tells Lean that it can decide whether two indices are equal.

4. Code:
```lean
    (X : Matrix (d × k) (d × k) ℂ) :
```
This line is one local step in the declaration. It either refines the formula being defined or advances the proof by a small algebraic or logical move.  `Matrix d d ℂ` means a square matrix with complex entries; the index type `d` tells Lean which rows and columns exist.

5. Code:
```lean
    Matrix.trace X = Matrix.trace (partialTraceLeft d k X) := by
```
This line says that a proof script begins here. Everything indented underneath is a sequence of instructions that Lean will check step by step.

6. Code:
```lean
  calc
```
This line begins a chained calculation. Each displayed step that follows must be justified by the indented proof after `:= by`.

7. Code:
```lean
    Matrix.trace X = ∑ a : d, ∑ i : k, X (a, i) (a, i) := by
```
This line says that a proof script begins here. Everything indented underneath is a sequence of instructions that Lean will check step by step.

8. Code:
```lean
      simp [Matrix.trace, Fintype.sum_prod_type]
```
This line simplifies the goal using definitions and known equalities. `simpa` means that, after simplification, the desired statement matches a theorem Lean already has.

9. Code:
```lean
    _ = ∑ i : k, ∑ a : d, X (a, i) (a, i) := by
```
This line says that a proof script begins here. Everything indented underneath is a sequence of instructions that Lean will check step by step.

10. Code:
```lean
      simpa using
```
This line simplifies the goal using definitions and known equalities. `simpa` means that, after simplification, the desired statement matches a theorem Lean already has.

11. Code:
```lean
        (Finset.sum_comm
```
This line is one local step in the declaration. It either refines the formula being defined or advances the proof by a small algebraic or logical move.

12. Code:
```lean
          (s := (Finset.univ : Finset d))
```
This line is one local step in the declaration. It either refines the formula being defined or advances the proof by a small algebraic or logical move.

13. Code:
```lean
          (t := (Finset.univ : Finset k))
```
This line is one local step in the declaration. It either refines the formula being defined or advances the proof by a small algebraic or logical move.

14. Code:
```lean
          (f := fun a i => X (a, i) (a, i)))
```
This line is one local step in the declaration. It either refines the formula being defined or advances the proof by a small algebraic or logical move.

15. Code:
```lean
    _ = Matrix.trace (partialTraceLeft d k X) := by
```
This line says that a proof script begins here. Everything indented underneath is a sequence of instructions that Lean will check step by step.

16. Code:
```lean
      simp [partialTraceLeft, Matrix.trace]
```
This line simplifies the goal using definitions and known equalities. `simpa` means that, after simplification, the desired statement matches a theorem Lean already has.

## Mathematical summary

Restated without Lean syntax, `trace_eq_trace_partialTraceLeft` is the theorem or lemma written above.

- State the desired identity or inequality in Lean’s syntax.
- Introduce temporary names and intermediate claims that organize the argument.
- Use rewriting, simplification, and earlier lemmas to reduce the goal to standard matrix or norm manipulations.
- Close the remaining algebraic or order-theoretic steps with Lean’s proof tactics.

## Dependencies and downstream use

### Earlier declarations this depends on
- [`partialTraceLeft`](../Setups/partialTraceLeft.md) from `Setups.lean`

### Later declarations that use this one
- [`tensorWithIdentity_trace_zero`](tensorWithIdentity_trace_zero.md) in `StandardFacts.lean`

## Backlinks

- [Back to `INDEX.md`](../INDEX.md)
- [Back to the `StandardFacts.lean` section in the index](../INDEX.md#diamond-standardfacts-lean)
- [Previous declaration in this file](asymptotic_cotangent_lower_bound.md)
- [Next declaration in this file](partialTraceLeft_tensor_zero.md)