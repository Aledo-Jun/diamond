# theorem1

## Source location

- Original Lean file: `Diamond/Theorem/Theorem1.lean`
- Declaration name: `theorem1`
- Declaration kind: `theorem`

## Why this declaration exists

This is the main theorem of the project: it proves a universal $1/\sqrt{2}$ loss factor when transpose is composed with a channel difference.

 In the file `Theorem/Theorem1.lean`, it contributes to the main strict submultiplicativity theorem for transpose composed with a channel difference. Later proofs call this result by name, so documenting it makes the larger argument readable as a mathematical chain rather than as opaque proof script.

## Original code

```lean
theorem theorem1
    {d : Type u} [Fintype d] [DecidableEq d] [Nonempty d]
    (T : Channel d) (hT : IsQuantumChannel T) :
    diamondOp ((transposeMap d).comp (idMinus T)) ≤
      (1 / Real.sqrt 2) * diamondOp (transposeMap d) * diamondOp (idMinus T) := by
  change diamondNormAt (d := d) (k := d) ((transposeMap d).comp (idMinus T)) ≤
      (1 / Real.sqrt 2) * diamondOp (transposeMap d) * diamondOp (idMinus T)
  refine diamond_le_of_pointwise (d := d) (Φ := (transposeMap d).comp (idMinus T))
    ((1 / Real.sqrt 2) * diamondOp (transposeMap d) * diamondOp (idMinus T)) ?_
  intro ρ
  let Mρ : Matrix (d × d) (d × d) ℂ := tensorWithIdentity d d (idMinus T) ρ.1
  have hrewrite :
      tensorWithIdentity d d ((transposeMap d).comp (idMinus T)) ρ.1 =
        partialTransposeMap d d Mρ := by
    simpa [Mρ, LinearMap.comp_apply] using
      congrArg (fun Ψ : Channel (d × d) => Ψ ρ.1)
        (tensorWithIdentity_comp_transpose (d := d) (k := d) (Φ := idMinus T))
  have hTrace : Matrix.trace Mρ = 0 := by
    simpa [Mρ] using
      tensorWithIdentity_trace_zero (d := d) (k := d)
        (idMinus T) (idMinus_isTraceAnnihilating T hT) ρ.1
  have hHerm : Matrix.IsHermitian Mρ := by
    simpa [Mρ] using
      tensorWithIdentity_hermitian (d := d) (k := d)
        (Ψ := idMinus T) (idMinus_isHermiticityPreserving T hT) ρ.1 ρ.2
  have hlemma3 : hsNormOp (partialTransposeMap d d Mρ) = hsNormOp Mρ := by
    simpa [Mρ] using lemma3 (d := d) (k := d) Mρ
  have hlemma2 :
      traceNormOp (tensorWithIdentity d d ((transposeMap d).comp (idMinus T)) ρ.1) ≤
        Real.sqrt (Fintype.card (d × d) : ℝ) * hsNormOp Mρ := by
    have htmp :
        traceNormOp (partialTransposeMap d d Mρ) ≤
          Real.sqrt (Fintype.card (d × d) : ℝ) * hsNormOp (partialTransposeMap d d Mρ) := by
      simpa using lemma2 (Y := partialTransposeMap d d Mρ)
    rw [hrewrite]
    simpa [hlemma3] using htmp
  have hlemma1 : hsNormOp Mρ ≤ (1 / Real.sqrt 2) * traceNormOp Mρ := by
    simpa [Mρ] using lemma1 (X := Mρ) hHerm hTrace
  have htraceBound : traceNormOp Mρ ≤ diamondOp (idMinus T) := by
    simpa [Mρ, diamondOp] using
      traceNorm_apply_le_diamond
        (d := d) (k := d) (Φ := idMinus T) (ρ := ρ)
  have hhs : hsNormOp Mρ ≤ (1 / Real.sqrt 2) * diamondOp (idMinus T) := by
    calc
      hsNormOp Mρ ≤ (1 / Real.sqrt 2) * traceNormOp Mρ := hlemma1
      _ ≤ (1 / Real.sqrt 2) * diamondOp (idMinus T) := by
        exact mul_le_mul_of_nonneg_left htraceBound (by positivity)
  have hfinal1 :
      traceNormOp (tensorWithIdentity d d ((transposeMap d).comp (idMinus T)) ρ.1) ≤
        Real.sqrt (Fintype.card (d × d) : ℝ) * ((1 / Real.sqrt 2) * diamondOp (idMinus T)) := by
    exact le_trans hlemma2 (mul_le_mul_of_nonneg_left hhs (Real.sqrt_nonneg _))
  have hsqrt : Real.sqrt (Fintype.card (d × d) : ℝ) = diamondOp (transposeMap d) := by
    symm
    exact lemma_transpose_diamond (d := d)
  calc
    traceNormOp (tensorWithIdentity d d ((transposeMap d).comp (idMinus T)) ρ.1) ≤
        Real.sqrt (Fintype.card (d × d) : ℝ) *
          ((1 / Real.sqrt 2) * diamondOp (idMinus T)) := hfinal1
    _ = (1 / Real.sqrt 2) * diamondOp (transposeMap d) * diamondOp (idMinus T) := by
      rw [hsqrt]
      ring
```

## Line-by-line explanation

The explanation below follows the declaration one physical line at a time. For long proofs, some lines are tiny bookkeeping steps; those are still explained, but briefly.

1. Code:
```lean
theorem theorem1
```
This line starts the `theorem1` declaration. Because it begins with `theorem`, Lean now knows what kind of named object is being introduced.

2. Code:
```lean
    {d : Type u} [Fintype d] [DecidableEq d] [Nonempty d]
```
This line is one local step in the declaration. It either refines the formula being defined or advances the proof by a small algebraic or logical move.  A bracket such as `[Fintype d]` tells Lean that the index set `d` is finite, so sums over all indices make sense.  A bracket such as `[DecidableEq d]` tells Lean that it can decide whether two indices are equal.

3. Code:
```lean
    (T : Channel d) (hT : IsQuantumChannel T) :
```
This line is one local step in the declaration. It either refines the formula being defined or advances the proof by a small algebraic or logical move.  `Channel d` is an abbreviation for a complex-linear map from operators on `d` to operators on `d`.

4. Code:
```lean
    diamondOp ((transposeMap d).comp (idMinus T)) ≤
```
This line is one local step in the declaration. It either refines the formula being defined or advances the proof by a small algebraic or logical move.  `comp` means composition of maps: one map is applied after another.

5. Code:
```lean
      (1 / Real.sqrt 2) * diamondOp (transposeMap d) * diamondOp (idMinus T) := by
```
This line says that a proof script begins here. Everything indented underneath is a sequence of instructions that Lean will check step by step.

6. Code:
```lean
  change diamondNormAt (d := d) (k := d) ((transposeMap d).comp (idMinus T)) ≤
```
This line replaces the current goal by a definitionally equal goal that is easier to manipulate.  `comp` means composition of maps: one map is applied after another.

7. Code:
```lean
      (1 / Real.sqrt 2) * diamondOp (transposeMap d) * diamondOp (idMinus T)
```
This line is one local step in the declaration. It either refines the formula being defined or advances the proof by a small algebraic or logical move.

8. Code:
```lean
  refine diamond_le_of_pointwise (d := d) (Φ := (transposeMap d).comp (idMinus T))
```
This line is a more controlled version of `apply`. It sets up the proof with a partly specified argument and leaves smaller goals to solve next.  `comp` means composition of maps: one map is applied after another.

9. Code:
```lean
    ((1 / Real.sqrt 2) * diamondOp (transposeMap d) * diamondOp (idMinus T)) ?_
```
This line is one local step in the declaration. It either refines the formula being defined or advances the proof by a small algebraic or logical move.

10. Code:
```lean
  intro ρ
```
This line introduces the variable or hypothesis named here into the proof context. In ordinary mathematical prose, it is the same as saying “let” or “assume”.

11. Code:
```lean
  let Mρ : Matrix (d × d) (d × d) ℂ := tensorWithIdentity d d (idMinus T) ρ.1
```
This line gives a temporary name to an expression. Doing that makes later lines shorter and easier to read.  `Matrix d d ℂ` means a square matrix with complex entries; the index type `d` tells Lean which rows and columns exist.

12. Code:
```lean
  have hrewrite :
```
This line introduces an intermediate claim. The proof pauses to establish a fact that will be used shortly afterwards.

13. Code:
```lean
      tensorWithIdentity d d ((transposeMap d).comp (idMinus T)) ρ.1 =
```
This line is one local step in the declaration. It either refines the formula being defined or advances the proof by a small algebraic or logical move.  `comp` means composition of maps: one map is applied after another.

14. Code:
```lean
        partialTransposeMap d d Mρ := by
```
This line says that a proof script begins here. Everything indented underneath is a sequence of instructions that Lean will check step by step.

15. Code:
```lean
    simpa [Mρ, LinearMap.comp_apply] using
```
This line simplifies the goal using definitions and known equalities. `simpa` means that, after simplification, the desired statement matches a theorem Lean already has.  `comp` means composition of maps: one map is applied after another.  `LinearMap.comp` is composition of linear maps.

16. Code:
```lean
      congrArg (fun Ψ : Channel (d × d) => Ψ ρ.1)
```
This line applies the same function to both sides of a known equality, producing a new equality better suited to the current goal.

17. Code:
```lean
        (tensorWithIdentity_comp_transpose (d := d) (k := d) (Φ := idMinus T))
```
This line is one local step in the declaration. It either refines the formula being defined or advances the proof by a small algebraic or logical move.

18. Code:
```lean
  have hTrace : Matrix.trace Mρ = 0 := by
```
This line says that a proof script begins here. Everything indented underneath is a sequence of instructions that Lean will check step by step.

19. Code:
```lean
    simpa [Mρ] using
```
This line simplifies the goal using definitions and known equalities. `simpa` means that, after simplification, the desired statement matches a theorem Lean already has.

20. Code:
```lean
      tensorWithIdentity_trace_zero (d := d) (k := d)
```
This line is one local step in the declaration. It either refines the formula being defined or advances the proof by a small algebraic or logical move.

21. Code:
```lean
        (idMinus T) (idMinus_isTraceAnnihilating T hT) ρ.1
```
This line is one local step in the declaration. It either refines the formula being defined or advances the proof by a small algebraic or logical move.

22. Code:
```lean
  have hHerm : Matrix.IsHermitian Mρ := by
```
This line says that a proof script begins here. Everything indented underneath is a sequence of instructions that Lean will check step by step.

23. Code:
```lean
    simpa [Mρ] using
```
This line simplifies the goal using definitions and known equalities. `simpa` means that, after simplification, the desired statement matches a theorem Lean already has.

24. Code:
```lean
      tensorWithIdentity_hermitian (d := d) (k := d)
```
This line is one local step in the declaration. It either refines the formula being defined or advances the proof by a small algebraic or logical move.

25. Code:
```lean
        (Ψ := idMinus T) (idMinus_isHermiticityPreserving T hT) ρ.1 ρ.2
```
This line is one local step in the declaration. It either refines the formula being defined or advances the proof by a small algebraic or logical move.

26. Code:
```lean
  have hlemma3 : hsNormOp (partialTransposeMap d d Mρ) = hsNormOp Mρ := by
```
This line says that a proof script begins here. Everything indented underneath is a sequence of instructions that Lean will check step by step.

27. Code:
```lean
    simpa [Mρ] using lemma3 (d := d) (k := d) Mρ
```
This line simplifies the goal using definitions and known equalities. `simpa` means that, after simplification, the desired statement matches a theorem Lean already has.

28. Code:
```lean
  have hlemma2 :
```
This line introduces an intermediate claim. The proof pauses to establish a fact that will be used shortly afterwards.

29. Code:
```lean
      traceNormOp (tensorWithIdentity d d ((transposeMap d).comp (idMinus T)) ρ.1) ≤
```
This line is one local step in the declaration. It either refines the formula being defined or advances the proof by a small algebraic or logical move.  `comp` means composition of maps: one map is applied after another.

30. Code:
```lean
        Real.sqrt (Fintype.card (d × d) : ℝ) * hsNormOp Mρ := by
```
This line says that a proof script begins here. Everything indented underneath is a sequence of instructions that Lean will check step by step.  `Fintype.card` is the size of a finite index set.

31. Code:
```lean
    have htmp :
```
This line introduces an intermediate claim. The proof pauses to establish a fact that will be used shortly afterwards.

32. Code:
```lean
        traceNormOp (partialTransposeMap d d Mρ) ≤
```
This line is one local step in the declaration. It either refines the formula being defined or advances the proof by a small algebraic or logical move.

33. Code:
```lean
          Real.sqrt (Fintype.card (d × d) : ℝ) * hsNormOp (partialTransposeMap d d Mρ) := by
```
This line says that a proof script begins here. Everything indented underneath is a sequence of instructions that Lean will check step by step.  `Fintype.card` is the size of a finite index set.

34. Code:
```lean
      simpa using lemma2 (Y := partialTransposeMap d d Mρ)
```
This line simplifies the goal using definitions and known equalities. `simpa` means that, after simplification, the desired statement matches a theorem Lean already has.

35. Code:
```lean
    rw [hrewrite]
```
This line uses rewriting. Lean replaces one expression by an equal expression using the lemmas listed in brackets.

36. Code:
```lean
    simpa [hlemma3] using htmp
```
This line simplifies the goal using definitions and known equalities. `simpa` means that, after simplification, the desired statement matches a theorem Lean already has.

37. Code:
```lean
  have hlemma1 : hsNormOp Mρ ≤ (1 / Real.sqrt 2) * traceNormOp Mρ := by
```
This line says that a proof script begins here. Everything indented underneath is a sequence of instructions that Lean will check step by step.

38. Code:
```lean
    simpa [Mρ] using lemma1 (X := Mρ) hHerm hTrace
```
This line simplifies the goal using definitions and known equalities. `simpa` means that, after simplification, the desired statement matches a theorem Lean already has.

39. Code:
```lean
  have htraceBound : traceNormOp Mρ ≤ diamondOp (idMinus T) := by
```
This line says that a proof script begins here. Everything indented underneath is a sequence of instructions that Lean will check step by step.

40. Code:
```lean
    simpa [Mρ, diamondOp] using
```
This line simplifies the goal using definitions and known equalities. `simpa` means that, after simplification, the desired statement matches a theorem Lean already has.

41. Code:
```lean
      traceNorm_apply_le_diamond
```
This line is one local step in the declaration. It either refines the formula being defined or advances the proof by a small algebraic or logical move.

42. Code:
```lean
        (d := d) (k := d) (Φ := idMinus T) (ρ := ρ)
```
This line is one local step in the declaration. It either refines the formula being defined or advances the proof by a small algebraic or logical move.

43. Code:
```lean
  have hhs : hsNormOp Mρ ≤ (1 / Real.sqrt 2) * diamondOp (idMinus T) := by
```
This line says that a proof script begins here. Everything indented underneath is a sequence of instructions that Lean will check step by step.

44. Code:
```lean
    calc
```
This line begins a chained calculation. Each displayed step that follows must be justified by the indented proof after `:= by`.

45. Code:
```lean
      hsNormOp Mρ ≤ (1 / Real.sqrt 2) * traceNormOp Mρ := hlemma1
```
This line is one local step in the declaration. It either refines the formula being defined or advances the proof by a small algebraic or logical move.

46. Code:
```lean
      _ ≤ (1 / Real.sqrt 2) * diamondOp (idMinus T) := by
```
This line says that a proof script begins here. Everything indented underneath is a sequence of instructions that Lean will check step by step.

47. Code:
```lean
        exact mul_le_mul_of_nonneg_left htraceBound (by positivity)
```
This line finishes the current goal by giving Lean the exact theorem, lemma, or term that proves it.

48. Code:
```lean
  have hfinal1 :
```
This line introduces an intermediate claim. The proof pauses to establish a fact that will be used shortly afterwards.

49. Code:
```lean
      traceNormOp (tensorWithIdentity d d ((transposeMap d).comp (idMinus T)) ρ.1) ≤
```
This line is one local step in the declaration. It either refines the formula being defined or advances the proof by a small algebraic or logical move.  `comp` means composition of maps: one map is applied after another.

50. Code:
```lean
        Real.sqrt (Fintype.card (d × d) : ℝ) * ((1 / Real.sqrt 2) * diamondOp (idMinus T)) := by
```
This line says that a proof script begins here. Everything indented underneath is a sequence of instructions that Lean will check step by step.  `Fintype.card` is the size of a finite index set.

51. Code:
```lean
    exact le_trans hlemma2 (mul_le_mul_of_nonneg_left hhs (Real.sqrt_nonneg _))
```
This line finishes the current goal by giving Lean the exact theorem, lemma, or term that proves it.

52. Code:
```lean
  have hsqrt : Real.sqrt (Fintype.card (d × d) : ℝ) = diamondOp (transposeMap d) := by
```
This line says that a proof script begins here. Everything indented underneath is a sequence of instructions that Lean will check step by step.  `Fintype.card` is the size of a finite index set.

53. Code:
```lean
    symm
```
This line is one local step in the declaration. It either refines the formula being defined or advances the proof by a small algebraic or logical move.

54. Code:
```lean
    exact lemma_transpose_diamond (d := d)
```
This line finishes the current goal by giving Lean the exact theorem, lemma, or term that proves it.

55. Code:
```lean
  calc
```
This line begins a chained calculation. Each displayed step that follows must be justified by the indented proof after `:= by`.

56. Code:
```lean
    traceNormOp (tensorWithIdentity d d ((transposeMap d).comp (idMinus T)) ρ.1) ≤
```
This line is one local step in the declaration. It either refines the formula being defined or advances the proof by a small algebraic or logical move.  `comp` means composition of maps: one map is applied after another.

57. Code:
```lean
        Real.sqrt (Fintype.card (d × d) : ℝ) *
```
This line is one local step in the declaration. It either refines the formula being defined or advances the proof by a small algebraic or logical move.  `Fintype.card` is the size of a finite index set.

58. Code:
```lean
          ((1 / Real.sqrt 2) * diamondOp (idMinus T)) := hfinal1
```
This line is one local step in the declaration. It either refines the formula being defined or advances the proof by a small algebraic or logical move.

59. Code:
```lean
    _ = (1 / Real.sqrt 2) * diamondOp (transposeMap d) * diamondOp (idMinus T) := by
```
This line says that a proof script begins here. Everything indented underneath is a sequence of instructions that Lean will check step by step.

60. Code:
```lean
      rw [hsqrt]
```
This line uses rewriting. Lean replaces one expression by an equal expression using the lemmas listed in brackets.

61. Code:
```lean
      ring
```
This line normalizes an algebraic identity in a commutative ring, just as one would expand and collect like terms by hand.

## Mathematical summary

Restated without Lean syntax, `theorem1` is the theorem or lemma written above.

- Rewrite the stabilized transpose channel as a partial transpose using `tensorWithIdentity_comp_transpose`.
- Set $X = ((\mathrm{id}-T) \otimes \mathrm{id})(\rho)$ and show that $X$ is traceless and Hermitian.
- Apply Lemma 2 to the partial transpose of $X$, then Lemma 3 to remove the partial transpose from the Hilbert--Schmidt norm.
- Apply Lemma 1 to $X` to convert the Hilbert--Schmidt norm into a trace norm.
- Bound the remaining trace norm by the diamond norm of `idMinus T` and replace the dimension factor by `diamondOp (transposeMap d)`.

## Dependencies and downstream use

### Earlier declarations this depends on
- [`Channel`](../../Setups/Channel.md) from `Setups.lean`
- [`traceNormOp`](../../Setups/traceNormOp.md) from `Setups.lean`
- [`hsNormOp`](../../Setups/hsNormOp.md) from `Setups.lean`
- [`IsQuantumChannel`](../../Setups/IsQuantumChannel.md) from `Setups.lean`
- [`transposeMap`](../../Setups/transposeMap.md) from `Setups.lean`
- [`tensorWithIdentity`](../../Setups/tensorWithIdentity.md) from `Setups.lean`
- [`partialTransposeMap`](../../Setups/partialTransposeMap.md) from `Setups.lean`
- [`diamondNormAt`](../../Setups/diamondNormAt.md) from `Setups.lean`
- [`diamondOp`](../../Setups/diamondOp.md) from `Setups.lean`
- [`idMinus`](../../Setups/idMinus.md) from `Setups.lean`
- [`tensorWithIdentity_comp_transpose`](../../StandardFacts/tensorWithIdentity_comp_transpose.md) from `StandardFacts.lean`
- [`idMinus_isHermiticityPreserving`](../../StandardFacts/idMinus_isHermiticityPreserving.md) from `StandardFacts.lean`
- [`idMinus_isTraceAnnihilating`](../../StandardFacts/idMinus_isTraceAnnihilating.md) from `StandardFacts.lean`
- [`diamond_le_of_pointwise`](../../StandardFacts/diamond_le_of_pointwise.md) from `StandardFacts.lean`
- [`traceNorm_apply_le_diamond`](../../StandardFacts/traceNorm_apply_le_diamond.md) from `StandardFacts.lean`
- [`lemma_transpose_diamond`](../../StandardFacts/lemma_transpose_diamond.md) from `StandardFacts.lean`
- [`tensorWithIdentity_trace_zero`](../../StandardFacts/tensorWithIdentity_trace_zero.md) from `StandardFacts.lean`
- [`tensorWithIdentity_hermitian`](../../StandardFacts/tensorWithIdentity_hermitian.md) from `StandardFacts.lean`
- [`lemma1`](../Lemma1/lemma1.md) from `Theorem/Lemma1.lean`
- [`lemma2`](../Lemma2/lemma2.md) from `Theorem/Lemma2.lean`
- [`lemma3`](../Lemma3/lemma3.md) from `Theorem/Lemma3.lean`

### Later declarations that use this one
- [`theorem_not_tight`](../../PositiveGap/NotTight/theorem_not_tight.md) in `PositiveGap/NotTight.lean`
- [`alpha_lower_bound`](../../EndMatter/Eq8/alpha_lower_bound.md) in `EndMatter/Eq8.lean`

## Backlinks

- [Back to `INDEX.md`](../../INDEX.md)
- [Back to the `Theorem/Theorem1.lean` section in the index](../../INDEX.md#diamond-theorem-theorem1-lean)