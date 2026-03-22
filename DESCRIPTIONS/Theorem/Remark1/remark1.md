# remark1

## Source location

- Original Lean file: `Diamond/Theorem/Remark1.lean`
- Declaration name: `remark1`
- Declaration kind: `theorem`

## Why this declaration exists

This remark shows that the same bound as Theorem 1 holds for any Hermiticity-preserving, trace-annihilating map, not just `idMinus T`.

 In the file `Theorem/Remark1.lean`, it contributes to the extension of Theorem 1 from channel differences to arbitrary Hermiticity-preserving, trace-annihilating maps. Later proofs call this result by name, so documenting it makes the larger argument readable as a mathematical chain rather than as opaque proof script.

## Original code

```lean
/-- Paper Remark 1: the general Hermiticity-preserving, trace-annihilating bound. -/
theorem remark1
    {d : Type u} [Fintype d] [DecidableEq d] [Nonempty d]
    (Ψ : Channel d) (hH : IsHermiticityPreserving Ψ) (hT : IsTraceAnnihilating Ψ) :
    diamondOp ((transposeMap d).comp Ψ) ≤
      (1 / Real.sqrt 2) * diamondOp (transposeMap d) * diamondOp Ψ := by
  change diamondNormAt (d := d) (k := d) ((transposeMap d).comp Ψ) ≤
      (1 / Real.sqrt 2) * diamondOp (transposeMap d) * diamondOp Ψ
  refine diamond_le_of_pointwise_nonempty (d := d) (Φ := (transposeMap d).comp Ψ)
    ((1 / Real.sqrt 2) * diamondOp (transposeMap d) * diamondOp Ψ) ?_
  intro ρ
  let Mρ : Matrix (d × d) (d × d) ℂ := tensorWithIdentity d d Ψ ρ.1
  have hrewrite :
      tensorWithIdentity d d ((transposeMap d).comp Ψ) ρ.1 =
        partialTransposeMap d d Mρ := by
    simpa [Mρ, LinearMap.comp_apply] using
      congrArg (fun Φ : Channel (d × d) => Φ ρ.1)
        (tensorWithIdentity_comp_transpose (d := d) (k := d) (Φ := Ψ))
  have hTrace : Matrix.trace Mρ = 0 := by
    simpa [Mρ] using tensorWithIdentity_trace_zero (d := d) (k := d) Ψ hT ρ.1
  have hHerm : Matrix.IsHermitian Mρ := by
    simpa [Mρ] using tensorWithIdentity_hermitian (d := d) (k := d) Ψ hH ρ.1 ρ.2
  have hbound2 : hsNormOp (partialTransposeMap d d Mρ) = hsNormOp Mρ := by
    simpa [Mρ] using lemma3 (d := d) (k := d) Mρ
  have hbound1 :
      traceNormOp (tensorWithIdentity d d ((transposeMap d).comp Ψ) ρ.1) ≤
        Real.sqrt (Fintype.card (d × d) : ℝ) * hsNormOp Mρ := by
    have htmp :
        traceNormOp (partialTransposeMap d d Mρ) ≤
          Real.sqrt (Fintype.card (d × d) : ℝ) * hsNormOp (partialTransposeMap d d Mρ) := by
      simpa using lemma2 (Y := partialTransposeMap d d Mρ)
    rw [hrewrite]
    simpa [hbound2] using htmp
  have hlemma1 : hsNormOp Mρ ≤ (1 / Real.sqrt 2) * traceNormOp Mρ := by
    simpa [Mρ] using lemma1 (X := Mρ) hHerm hTrace
  have htraceBound : traceNormOp Mρ ≤ diamondOp Ψ := by
    simpa [Mρ, diamondOp] using
      traceNorm_apply_le_diamond
        (d := d) (k := d) (Φ := Ψ) (ρ := ρ)
  have hhs : hsNormOp Mρ ≤ (1 / Real.sqrt 2) * diamondOp Ψ := by
    calc
      hsNormOp Mρ ≤ (1 / Real.sqrt 2) * traceNormOp Mρ := hlemma1
      _ ≤ (1 / Real.sqrt 2) * diamondOp Ψ := by
        exact mul_le_mul_of_nonneg_left htraceBound (by positivity)
  have hfinal1 :
      traceNormOp (tensorWithIdentity d d ((transposeMap d).comp Ψ) ρ.1) ≤
        Real.sqrt (Fintype.card (d × d) : ℝ) * ((1 / Real.sqrt 2) * diamondOp Ψ) := by
    exact le_trans hbound1 (mul_le_mul_of_nonneg_left hhs (Real.sqrt_nonneg _))
  have hsqrt : Real.sqrt (Fintype.card (d × d) : ℝ) = diamondOp (transposeMap d) := by
    symm
    exact lemma_transpose_diamond (d := d)
  calc
    traceNormOp (tensorWithIdentity d d ((transposeMap d).comp Ψ) ρ.1) ≤
        Real.sqrt (Fintype.card (d × d) : ℝ) * ((1 / Real.sqrt 2) * diamondOp Ψ) := hfinal1
    _ = (1 / Real.sqrt 2) * diamondOp (transposeMap d) * diamondOp Ψ := by
      rw [hsqrt]
      ring
```

## Block-by-block explanation

The explanation below follows the declaration block by block. Each block groups a coherent piece of the definition or proof, so the mathematical structure is easier to see than in a strictly line-oriented reading.

1. Code:
```lean
/-- Paper Remark 1: the general Hermiticity-preserving, trace-annihilating bound. -/
```
This is a Lean docstring. It is a human-written comment that tells readers what the declaration is meant to express before the formal code begins.

2. Code:
```lean
theorem remark1
```
This line starts the `remark1` declaration. Because it begins with `theorem`, Lean now knows what kind of named object is being introduced.

3. Code:
```lean
    {d : Type u} [Fintype d] [DecidableEq d] [Nonempty d]
```
This line is one local step in the declaration. It either refines the formula being defined or advances the proof by a small algebraic or logical move.  A bracket such as `[Fintype d]` tells Lean that the index set `d` is finite, so sums over all indices make sense.  A bracket such as `[DecidableEq d]` tells Lean that it can decide whether two indices are equal.

4. Code:
```lean
    (Ψ : Channel d) (hH : IsHermiticityPreserving Ψ) (hT : IsTraceAnnihilating Ψ) :
```
This line is one local step in the declaration. It either refines the formula being defined or advances the proof by a small algebraic or logical move.  `Channel d` is an abbreviation for a complex-linear map from operators on `d` to operators on `d`.

5. Code:
```lean
    diamondOp ((transposeMap d).comp Ψ) ≤
```
This line is one local step in the declaration. It either refines the formula being defined or advances the proof by a small algebraic or logical move.  `comp` means composition of maps: one map is applied after another.

6. Code:
```lean
      (1 / Real.sqrt 2) * diamondOp (transposeMap d) * diamondOp Ψ := by
```
This line says that a proof script begins here. Everything indented underneath is a sequence of instructions that Lean will check step by step.

7. Code:
```lean
  change diamondNormAt (d := d) (k := d) ((transposeMap d).comp Ψ) ≤
```
This line replaces the current goal by a definitionally equal goal that is easier to manipulate.  `comp` means composition of maps: one map is applied after another.

8. Code:
```lean
      (1 / Real.sqrt 2) * diamondOp (transposeMap d) * diamondOp Ψ
```
This line is one local step in the declaration. It either refines the formula being defined or advances the proof by a small algebraic or logical move.

9. Code:
```lean
  refine diamond_le_of_pointwise_nonempty (d := d) (Φ := (transposeMap d).comp Ψ)
```
This line is a more controlled version of `apply`. It sets up the proof with a partly specified argument and leaves smaller goals to solve next.  `comp` means composition of maps: one map is applied after another.

10. Code:
```lean
    ((1 / Real.sqrt 2) * diamondOp (transposeMap d) * diamondOp Ψ) ?_
```
This line is one local step in the declaration. It either refines the formula being defined or advances the proof by a small algebraic or logical move.

11. Code:
```lean
  intro ρ
```
This line introduces the variable or hypothesis named here into the proof context. In ordinary mathematical prose, it is the same as saying “let” or “assume”.

12. Code:
```lean
  let Mρ : Matrix (d × d) (d × d) ℂ := tensorWithIdentity d d Ψ ρ.1
```
This line gives a temporary name to an expression. Doing that makes later lines shorter and easier to read.  `Matrix d d ℂ` means a square matrix with complex entries; the index type `d` tells Lean which rows and columns exist.

13. Code:
```lean
  have hrewrite :
```
This line introduces an intermediate claim. The proof pauses to establish a fact that will be used shortly afterwards.

14. Code:
```lean
      tensorWithIdentity d d ((transposeMap d).comp Ψ) ρ.1 =
```
This line is one local step in the declaration. It either refines the formula being defined or advances the proof by a small algebraic or logical move.  `comp` means composition of maps: one map is applied after another.

15. Code:
```lean
        partialTransposeMap d d Mρ := by
```
This line says that a proof script begins here. Everything indented underneath is a sequence of instructions that Lean will check step by step.

16. Code:
```lean
    simpa [Mρ, LinearMap.comp_apply] using
```
This line simplifies the goal using definitions and known equalities. `simpa` means that, after simplification, the desired statement matches a theorem Lean already has.  `comp` means composition of maps: one map is applied after another.  `LinearMap.comp` is composition of linear maps.

17. Code:
```lean
      congrArg (fun Φ : Channel (d × d) => Φ ρ.1)
```
This line applies the same function to both sides of a known equality, producing a new equality better suited to the current goal.

18. Code:
```lean
        (tensorWithIdentity_comp_transpose (d := d) (k := d) (Φ := Ψ))
```
This line is one local step in the declaration. It either refines the formula being defined or advances the proof by a small algebraic or logical move.

19. Code:
```lean
  have hTrace : Matrix.trace Mρ = 0 := by
```
This line says that a proof script begins here. Everything indented underneath is a sequence of instructions that Lean will check step by step.

20. Code:
```lean
    simpa [Mρ] using tensorWithIdentity_trace_zero (d := d) (k := d) Ψ hT ρ.1
```
This line simplifies the goal using definitions and known equalities. `simpa` means that, after simplification, the desired statement matches a theorem Lean already has.

21. Code:
```lean
  have hHerm : Matrix.IsHermitian Mρ := by
```
This line says that a proof script begins here. Everything indented underneath is a sequence of instructions that Lean will check step by step.

22. Code:
```lean
    simpa [Mρ] using tensorWithIdentity_hermitian (d := d) (k := d) Ψ hH ρ.1 ρ.2
```
This line simplifies the goal using definitions and known equalities. `simpa` means that, after simplification, the desired statement matches a theorem Lean already has.

23. Code:
```lean
  have hbound2 : hsNormOp (partialTransposeMap d d Mρ) = hsNormOp Mρ := by
```
This line says that a proof script begins here. Everything indented underneath is a sequence of instructions that Lean will check step by step.

24. Code:
```lean
    simpa [Mρ] using lemma3 (d := d) (k := d) Mρ
```
This line simplifies the goal using definitions and known equalities. `simpa` means that, after simplification, the desired statement matches a theorem Lean already has.

25. Code:
```lean
  have hbound1 :
```
This line introduces an intermediate claim. The proof pauses to establish a fact that will be used shortly afterwards.

26. Code:
```lean
      traceNormOp (tensorWithIdentity d d ((transposeMap d).comp Ψ) ρ.1) ≤
```
This line is one local step in the declaration. It either refines the formula being defined or advances the proof by a small algebraic or logical move.  `comp` means composition of maps: one map is applied after another.

27. Code:
```lean
        Real.sqrt (Fintype.card (d × d) : ℝ) * hsNormOp Mρ := by
```
This line says that a proof script begins here. Everything indented underneath is a sequence of instructions that Lean will check step by step.  `Fintype.card` is the size of a finite index set.

28. Code:
```lean
    have htmp :
```
This line introduces an intermediate claim. The proof pauses to establish a fact that will be used shortly afterwards.

29. Code:
```lean
        traceNormOp (partialTransposeMap d d Mρ) ≤
```
This line is one local step in the declaration. It either refines the formula being defined or advances the proof by a small algebraic or logical move.

30. Code:
```lean
          Real.sqrt (Fintype.card (d × d) : ℝ) * hsNormOp (partialTransposeMap d d Mρ) := by
```
This line says that a proof script begins here. Everything indented underneath is a sequence of instructions that Lean will check step by step.  `Fintype.card` is the size of a finite index set.

31. Code:
```lean
      simpa using lemma2 (Y := partialTransposeMap d d Mρ)
```
This line simplifies the goal using definitions and known equalities. `simpa` means that, after simplification, the desired statement matches a theorem Lean already has.

32. Code:
```lean
    rw [hrewrite]
```
This line uses rewriting. Lean replaces one expression by an equal expression using the lemmas listed in brackets.

33. Code:
```lean
    simpa [hbound2] using htmp
```
This line simplifies the goal using definitions and known equalities. `simpa` means that, after simplification, the desired statement matches a theorem Lean already has.

34. Code:
```lean
  have hlemma1 : hsNormOp Mρ ≤ (1 / Real.sqrt 2) * traceNormOp Mρ := by
```
This line says that a proof script begins here. Everything indented underneath is a sequence of instructions that Lean will check step by step.

35. Code:
```lean
    simpa [Mρ] using lemma1 (X := Mρ) hHerm hTrace
```
This line simplifies the goal using definitions and known equalities. `simpa` means that, after simplification, the desired statement matches a theorem Lean already has.

36. Code:
```lean
  have htraceBound : traceNormOp Mρ ≤ diamondOp Ψ := by
```
This line says that a proof script begins here. Everything indented underneath is a sequence of instructions that Lean will check step by step.

37. Code:
```lean
    simpa [Mρ, diamondOp] using
```
This line simplifies the goal using definitions and known equalities. `simpa` means that, after simplification, the desired statement matches a theorem Lean already has.

38. Code:
```lean
      traceNorm_apply_le_diamond
```
This line is one local step in the declaration. It either refines the formula being defined or advances the proof by a small algebraic or logical move.

39. Code:
```lean
        (d := d) (k := d) (Φ := Ψ) (ρ := ρ)
```
This line is one local step in the declaration. It either refines the formula being defined or advances the proof by a small algebraic or logical move.

40. Code:
```lean
  have hhs : hsNormOp Mρ ≤ (1 / Real.sqrt 2) * diamondOp Ψ := by
```
This line says that a proof script begins here. Everything indented underneath is a sequence of instructions that Lean will check step by step.

41. Code:
```lean
    calc
```
This line begins a chained calculation. Each displayed step that follows must be justified by the indented proof after `:= by`.

42. Code:
```lean
      hsNormOp Mρ ≤ (1 / Real.sqrt 2) * traceNormOp Mρ := hlemma1
```
This line is one local step in the declaration. It either refines the formula being defined or advances the proof by a small algebraic or logical move.

43. Code:
```lean
      _ ≤ (1 / Real.sqrt 2) * diamondOp Ψ := by
```
This line says that a proof script begins here. Everything indented underneath is a sequence of instructions that Lean will check step by step.

44. Code:
```lean
        exact mul_le_mul_of_nonneg_left htraceBound (by positivity)
```
This line finishes the current goal by giving Lean the exact theorem, lemma, or term that proves it.

45. Code:
```lean
  have hfinal1 :
```
This line introduces an intermediate claim. The proof pauses to establish a fact that will be used shortly afterwards.

46. Code:
```lean
      traceNormOp (tensorWithIdentity d d ((transposeMap d).comp Ψ) ρ.1) ≤
```
This line is one local step in the declaration. It either refines the formula being defined or advances the proof by a small algebraic or logical move.  `comp` means composition of maps: one map is applied after another.

47. Code:
```lean
        Real.sqrt (Fintype.card (d × d) : ℝ) * ((1 / Real.sqrt 2) * diamondOp Ψ) := by
```
This line says that a proof script begins here. Everything indented underneath is a sequence of instructions that Lean will check step by step.  `Fintype.card` is the size of a finite index set.

48. Code:
```lean
    exact le_trans hbound1 (mul_le_mul_of_nonneg_left hhs (Real.sqrt_nonneg _))
```
This line finishes the current goal by giving Lean the exact theorem, lemma, or term that proves it.

49. Code:
```lean
  have hsqrt : Real.sqrt (Fintype.card (d × d) : ℝ) = diamondOp (transposeMap d) := by
```
This line says that a proof script begins here. Everything indented underneath is a sequence of instructions that Lean will check step by step.  `Fintype.card` is the size of a finite index set.

50. Code:
```lean
    symm
```
This line is one local step in the declaration. It either refines the formula being defined or advances the proof by a small algebraic or logical move.

51. Code:
```lean
    exact lemma_transpose_diamond (d := d)
```
This line finishes the current goal by giving Lean the exact theorem, lemma, or term that proves it.

52. Code:
```lean
  calc
```
This line begins a chained calculation. Each displayed step that follows must be justified by the indented proof after `:= by`.

53. Code:
```lean
    traceNormOp (tensorWithIdentity d d ((transposeMap d).comp Ψ) ρ.1) ≤
```
This line is one local step in the declaration. It either refines the formula being defined or advances the proof by a small algebraic or logical move.  `comp` means composition of maps: one map is applied after another.

54. Code:
```lean
        Real.sqrt (Fintype.card (d × d) : ℝ) * ((1 / Real.sqrt 2) * diamondOp Ψ) := hfinal1
```
This line is one local step in the declaration. It either refines the formula being defined or advances the proof by a small algebraic or logical move.  `Fintype.card` is the size of a finite index set.

55. Code:
```lean
    _ = (1 / Real.sqrt 2) * diamondOp (transposeMap d) * diamondOp Ψ := by
```
This line says that a proof script begins here. Everything indented underneath is a sequence of instructions that Lean will check step by step.

56. Code:
```lean
      rw [hsqrt]
```
This line uses rewriting. Lean replaces one expression by an equal expression using the lemmas listed in brackets.

57. Code:
```lean
      ring
```
This line normalizes an algebraic identity in a commutative ring, just as one would expand and collect like terms by hand.

## Mathematical summary

Restated without Lean syntax, `remark1` is the theorem or lemma written above.

- Repeat the proof of Theorem 1 with a general map $\Psi$ in place of $\mathrm{id}-T$.
- Use the assumptions that $\Psi$ is Hermiticity preserving and trace annihilating to get the needed structural facts about $X = (\Psi \otimes \mathrm{id})(\rho)$.
- Apply the same Lemma 2 -> Lemma 3 -> Lemma 1 chain as in Theorem 1.
- Finish with the witness bound for the diamond norm and the known value of the transpose diamond norm.

## Dependencies and downstream use

### Earlier declarations this depends on
- [`Channel`](../../Setups/Channel.md) from `Setups.lean`
- [`traceNormOp`](../../Setups/traceNormOp.md) from `Setups.lean`
- [`hsNormOp`](../../Setups/hsNormOp.md) from `Setups.lean`
- [`IsHermiticityPreserving`](../../Setups/IsHermiticityPreserving.md) from `Setups.lean`
- [`IsTraceAnnihilating`](../../Setups/IsTraceAnnihilating.md) from `Setups.lean`
- [`transposeMap`](../../Setups/transposeMap.md) from `Setups.lean`
- [`tensorWithIdentity`](../../Setups/tensorWithIdentity.md) from `Setups.lean`
- [`partialTransposeMap`](../../Setups/partialTransposeMap.md) from `Setups.lean`
- [`diamondNormAt`](../../Setups/diamondNormAt.md) from `Setups.lean`
- [`diamondOp`](../../Setups/diamondOp.md) from `Setups.lean`
- [`tensorWithIdentity_comp_transpose`](../../StandardFacts/tensorWithIdentity_comp_transpose.md) from `StandardFacts.lean`
- [`diamond_le_of_pointwise_nonempty`](../../StandardFacts/diamond_le_of_pointwise_nonempty.md) from `StandardFacts.lean`
- [`traceNorm_apply_le_diamond`](../../StandardFacts/traceNorm_apply_le_diamond.md) from `StandardFacts.lean`
- [`lemma_transpose_diamond`](../../StandardFacts/lemma_transpose_diamond.md) from `StandardFacts.lean`
- [`tensorWithIdentity_trace_zero`](../../StandardFacts/tensorWithIdentity_trace_zero.md) from `StandardFacts.lean`
- [`tensorWithIdentity_hermitian`](../../StandardFacts/tensorWithIdentity_hermitian.md) from `StandardFacts.lean`
- [`lemma1`](../Lemma1/lemma1.md) from `Theorem/Lemma1.lean`
- [`lemma2`](../Lemma2/lemma2.md) from `Theorem/Lemma2.lean`
- [`lemma3`](../Lemma3/lemma3.md) from `Theorem/Lemma3.lean`

### Later declarations that use this one
- [`corollary2_linear_bound`](../../EndMatter/Corollary2/corollary2_linear_bound.md) in `EndMatter/Corollary2.lean`

## Backlinks

- [Back to `INDEX.md`](../../INDEX.md)
- [Back to the `Theorem/Remark1.lean` section in the index](../../INDEX.md#diamond-theorem-remark1-lean)
