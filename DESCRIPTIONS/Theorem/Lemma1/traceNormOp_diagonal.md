# traceNormOp_diagonal

## Source location

- Original Lean file: `Diamond/Theorem/Lemma1.lean`
- Declaration name: `traceNormOp_diagonal`
- Declaration kind: `theorem`

## Why this declaration exists

Trace norm of a diagonal matrix is the sum of the absolute values of its diagonal entries.

 In the file `Theorem/Lemma1.lean`, it contributes to the proof infrastructure for the first norm inequality and the public theorem `lemma1`. Later proofs call this result by name, so documenting it makes the larger argument readable as a mathematical chain rather than as opaque proof script.

## Original code

```lean
/-- Trace norm of a diagonal matrix is the sum of the absolute values of its diagonal entries. -/
theorem traceNormOp_diagonal
    {d : Type u} [Fintype d] [DecidableEq d] (z : d → ℂ) :
    traceNormOp (Matrix.diagonal z) = ∑ i, ‖z i‖ := by
  let hDiag :
      Matrix.IsHermitian
        (Matrix.diagonal fun i => ((Complex.normSq (z i) : ℂ))) :=
    Matrix.isHermitian_diagonal_of_self_adjoint
      (fun i => ((Complex.normSq (z i) : ℂ))) (by
        ext i
        simp)
  have hmat :
      (Matrix.diagonal z)ᴴ * Matrix.diagonal z =
        Matrix.diagonal fun i => ((Complex.normSq (z i) : ℂ)) := by
    ext i j
    by_cases hij : i = j
    · subst hij
      simp [Complex.normSq_eq_conj_mul_self]
    · simp [hij]
  have hEig :
      (Matrix.isHermitian_conjTranspose_mul_self (Matrix.diagonal z)).eigenvalues =
        hDiag.eigenvalues := by
    apply
      (Matrix.IsHermitian.eigenvalues_eq_eigenvalues_iff
        (Matrix.isHermitian_conjTranspose_mul_self (Matrix.diagonal z))
        hDiag).2
    exact congrArg Matrix.charpoly hmat
  dsimp [traceNormOp, traceNorm]
  rw [hEig]
  have hmultiset :
      Multiset.map hDiag.eigenvalues Finset.univ.val =
        Multiset.map (fun i => Complex.normSq (z i)) Finset.univ.val := by
    have hroots :
        Multiset.map Complex.re
            ((Matrix.diagonal fun i => ((Complex.normSq (z i) : ℂ))).charpoly.roots) =
          Multiset.map (fun i => Complex.normSq (z i)) Finset.univ.val := by
      rw [show
            (Matrix.diagonal fun i => ((Complex.normSq (z i) : ℂ))).charpoly.roots =
              Multiset.map (fun i => ((Complex.normSq (z i) : ℂ))) Finset.univ.val by
            simpa [Matrix.charpoly_diagonal] using
              (Polynomial.roots_multiset_prod_X_sub_C
                (s := Multiset.map
                  (fun i => ((Complex.normSq (z i) : ℂ))) Finset.univ.val))]
      simp
    rw [Matrix.IsHermitian.roots_charpoly_eq_eigenvalues hDiag] at hroots
    simpa [Multiset.map_map, Function.comp_def] using hroots
  have hsqrt := congrArg (Multiset.map Real.sqrt) hmultiset
  have hsum :
      ∑ i, Real.sqrt (hDiag.eigenvalues i) =
        ∑ i, Real.sqrt (Complex.normSq (z i)) := by
    simpa [Multiset.map_map] using congrArg Multiset.sum hsqrt
  simpa [RCLike.sqrt_normSq_eq_norm] using hsum
```

## Block-by-block explanation

The explanation below follows the declaration block by block. Each block groups a coherent piece of the definition or proof, so the mathematical structure is easier to see than in a strictly line-oriented reading.

1. Code:
```lean
/-- Trace norm of a diagonal matrix is the sum of the absolute values of its diagonal entries. -/
```
This is a Lean docstring. It is a human-written comment that tells readers what the declaration is meant to express before the formal code begins.

2. Code:
```lean
theorem traceNormOp_diagonal
```
This line starts the `traceNormOp_diagonal` declaration. Because it begins with `theorem`, Lean now knows what kind of named object is being introduced.

3. Code:
```lean
    {d : Type u} [Fintype d] [DecidableEq d] (z : d → ℂ) :
```
This line is one local step in the declaration. It either refines the formula being defined or advances the proof by a small algebraic or logical move.  A bracket such as `[Fintype d]` tells Lean that the index set `d` is finite, so sums over all indices make sense.  A bracket such as `[DecidableEq d]` tells Lean that it can decide whether two indices are equal.

4. Code:
```lean
    traceNormOp (Matrix.diagonal z) = ∑ i, ‖z i‖ := by
```
This line says that a proof script begins here. Everything indented underneath is a sequence of instructions that Lean will check step by step.

5. Code:
```lean
  let hDiag :
```
This line gives a temporary name to an expression. Doing that makes later lines shorter and easier to read.

6. Code:
```lean
      Matrix.IsHermitian
```
This line is one local step in the declaration. It either refines the formula being defined or advances the proof by a small algebraic or logical move.

7. Code:
```lean
        (Matrix.diagonal fun i => ((Complex.normSq (z i) : ℂ))) :=
```
This line is one local step in the declaration. It either refines the formula being defined or advances the proof by a small algebraic or logical move.

8. Code:
```lean
    Matrix.isHermitian_diagonal_of_self_adjoint
```
This line is one local step in the declaration. It either refines the formula being defined or advances the proof by a small algebraic or logical move.

9. Code:
```lean
      (fun i => ((Complex.normSq (z i) : ℂ))) (by
```
This line is one local step in the declaration. It either refines the formula being defined or advances the proof by a small algebraic or logical move.

10. Code:
```lean
        ext i
```
This line invokes extensionality. To prove two maps or matrices are equal, Lean reduces the problem to checking their values entry by entry.

11. Code:
```lean
        simp)
```
This line simplifies the goal using definitions and known equalities. `simpa` means that, after simplification, the desired statement matches a theorem Lean already has.

12. Code:
```lean
  have hmat :
```
This line introduces an intermediate claim. The proof pauses to establish a fact that will be used shortly afterwards.

13. Code:
```lean
      (Matrix.diagonal z)ᴴ * Matrix.diagonal z =
```
This line is one local step in the declaration. It either refines the formula being defined or advances the proof by a small algebraic or logical move.  The superscript `ᴴ` means conjugate transpose (also called the adjoint).

14. Code:
```lean
        Matrix.diagonal fun i => ((Complex.normSq (z i) : ℂ)) := by
```
This line says that a proof script begins here. Everything indented underneath is a sequence of instructions that Lean will check step by step.

15. Code:
```lean
    ext i j
```
This line invokes extensionality. To prove two maps or matrices are equal, Lean reduces the problem to checking their values entry by entry.

16. Code:
```lean
    by_cases hij : i = j
```
This line splits the proof into cases according to whether the named proposition is true or false.

17. Code:
```lean
    · subst hij
```
This bullet starts a new subgoal produced by the previous tactic. Lean is now focusing on one branch of the argument.

18. Code:
```lean
      simp [Complex.normSq_eq_conj_mul_self]
```
This line simplifies the goal using definitions and known equalities. `simpa` means that, after simplification, the desired statement matches a theorem Lean already has.

19. Code:
```lean
    · simp [hij]
```
This bullet starts a new subgoal produced by the previous tactic. Lean is now focusing on one branch of the argument.

20. Code:
```lean
  have hEig :
```
This line introduces an intermediate claim. The proof pauses to establish a fact that will be used shortly afterwards.

21. Code:
```lean
      (Matrix.isHermitian_conjTranspose_mul_self (Matrix.diagonal z)).eigenvalues =
```
This line is one local step in the declaration. It either refines the formula being defined or advances the proof by a small algebraic or logical move.

22. Code:
```lean
        hDiag.eigenvalues := by
```
This line says that a proof script begins here. Everything indented underneath is a sequence of instructions that Lean will check step by step.

23. Code:
```lean
    apply
```
This line applies an existing theorem to the current goal. Lean then asks the author to prove the theorem’s hypotheses.

24. Code:
```lean
      (Matrix.IsHermitian.eigenvalues_eq_eigenvalues_iff
```
This line is one local step in the declaration. It either refines the formula being defined or advances the proof by a small algebraic or logical move.

25. Code:
```lean
        (Matrix.isHermitian_conjTranspose_mul_self (Matrix.diagonal z))
```
This line is one local step in the declaration. It either refines the formula being defined or advances the proof by a small algebraic or logical move.

26. Code:
```lean
        hDiag).2
```
This line is one local step in the declaration. It either refines the formula being defined or advances the proof by a small algebraic or logical move.

27. Code:
```lean
    exact congrArg Matrix.charpoly hmat
```
This line finishes the current goal by giving Lean the exact theorem, lemma, or term that proves it.

28. Code:
```lean
  dsimp [traceNormOp, traceNorm]
```
This line is one local step in the declaration. It either refines the formula being defined or advances the proof by a small algebraic or logical move.

29. Code:
```lean
  rw [hEig]
```
This line uses rewriting. Lean replaces one expression by an equal expression using the lemmas listed in brackets.

30. Code:
```lean
  have hmultiset :
```
This line introduces an intermediate claim. The proof pauses to establish a fact that will be used shortly afterwards.

31. Code:
```lean
      Multiset.map hDiag.eigenvalues Finset.univ.val =
```
This line is one local step in the declaration. It either refines the formula being defined or advances the proof by a small algebraic or logical move.

32. Code:
```lean
        Multiset.map (fun i => Complex.normSq (z i)) Finset.univ.val := by
```
This line says that a proof script begins here. Everything indented underneath is a sequence of instructions that Lean will check step by step.

33. Code:
```lean
    have hroots :
```
This line introduces an intermediate claim. The proof pauses to establish a fact that will be used shortly afterwards.

34. Code:
```lean
        Multiset.map Complex.re
```
This line is one local step in the declaration. It either refines the formula being defined or advances the proof by a small algebraic or logical move.

35. Code:
```lean
            ((Matrix.diagonal fun i => ((Complex.normSq (z i) : ℂ))).charpoly.roots) =
```
This line is one local step in the declaration. It either refines the formula being defined or advances the proof by a small algebraic or logical move.

36. Code:
```lean
          Multiset.map (fun i => Complex.normSq (z i)) Finset.univ.val := by
```
This line says that a proof script begins here. Everything indented underneath is a sequence of instructions that Lean will check step by step.

37. Code:
```lean
      rw [show
```
This line uses rewriting. Lean replaces one expression by an equal expression using the lemmas listed in brackets.

38. Code:
```lean
            (Matrix.diagonal fun i => ((Complex.normSq (z i) : ℂ))).charpoly.roots =
```
This line is one local step in the declaration. It either refines the formula being defined or advances the proof by a small algebraic or logical move.

39. Code:
```lean
              Multiset.map (fun i => ((Complex.normSq (z i) : ℂ))) Finset.univ.val by
```
This line is one local step in the declaration. It either refines the formula being defined or advances the proof by a small algebraic or logical move.

40. Code:
```lean
            simpa [Matrix.charpoly_diagonal] using
```
This line simplifies the goal using definitions and known equalities. `simpa` means that, after simplification, the desired statement matches a theorem Lean already has.

41. Code:
```lean
              (Polynomial.roots_multiset_prod_X_sub_C
```
This line is one local step in the declaration. It either refines the formula being defined or advances the proof by a small algebraic or logical move.

42. Code:
```lean
                (s := Multiset.map
```
This line is one local step in the declaration. It either refines the formula being defined or advances the proof by a small algebraic or logical move.

43. Code:
```lean
                  (fun i => ((Complex.normSq (z i) : ℂ))) Finset.univ.val))]
```
This line is one local step in the declaration. It either refines the formula being defined or advances the proof by a small algebraic or logical move.

44. Code:
```lean
      simp
```
This line simplifies the goal using definitions and known equalities. `simpa` means that, after simplification, the desired statement matches a theorem Lean already has.

45. Code:
```lean
    rw [Matrix.IsHermitian.roots_charpoly_eq_eigenvalues hDiag] at hroots
```
This line uses rewriting. Lean replaces one expression by an equal expression using the lemmas listed in brackets.

46. Code:
```lean
    simpa [Multiset.map_map, Function.comp_def] using hroots
```
This line simplifies the goal using definitions and known equalities. `simpa` means that, after simplification, the desired statement matches a theorem Lean already has.  `comp` means composition of maps: one map is applied after another.

47. Code:
```lean
  have hsqrt := congrArg (Multiset.map Real.sqrt) hmultiset
```
This line introduces an intermediate claim. The proof pauses to establish a fact that will be used shortly afterwards.

48. Code:
```lean
  have hsum :
```
This line introduces an intermediate claim. The proof pauses to establish a fact that will be used shortly afterwards.

49. Code:
```lean
      ∑ i, Real.sqrt (hDiag.eigenvalues i) =
```
This line is one local step in the declaration. It either refines the formula being defined or advances the proof by a small algebraic or logical move.

50. Code:
```lean
        ∑ i, Real.sqrt (Complex.normSq (z i)) := by
```
This line says that a proof script begins here. Everything indented underneath is a sequence of instructions that Lean will check step by step.

51. Code:
```lean
    simpa [Multiset.map_map] using congrArg Multiset.sum hsqrt
```
This line simplifies the goal using definitions and known equalities. `simpa` means that, after simplification, the desired statement matches a theorem Lean already has.

52. Code:
```lean
  simpa [RCLike.sqrt_normSq_eq_norm] using hsum
```
This line simplifies the goal using definitions and known equalities. `simpa` means that, after simplification, the desired statement matches a theorem Lean already has.

## Mathematical summary

Restated without Lean syntax, `traceNormOp_diagonal` is the theorem or lemma written above.

- State the desired identity or inequality in Lean’s syntax.
- Introduce temporary names and intermediate claims that organize the argument.
- Use rewriting, simplification, and earlier lemmas to reduce the goal to standard matrix or norm manipulations.
- Close the remaining algebraic or order-theoretic steps with Lean’s proof tactics.

## Dependencies and downstream use

### Earlier declarations this depends on
- [`traceNorm`](../../Setups/traceNorm.md) from `Setups.lean`
- [`traceNormOp`](../../Setups/traceNormOp.md) from `Setups.lean`

### Later declarations that use this one
- [`traceNormOp_hermitian_eq_sum_abs_eigenvalues`](traceNormOp_hermitian_eq_sum_abs_eigenvalues.md) in `Theorem/Lemma1.lean`
- [`explicit_witness_traceNorm_eq_sum`](../../EndMatter/Eq7/explicit_witness_traceNorm_eq_sum.md) in `EndMatter/Eq7.lean`

## Backlinks

- [Back to `INDEX.md`](../../INDEX.md)
- [Back to the `Theorem/Lemma1.lean` section in the index](../../INDEX.md#diamond-theorem-lemma1-lean)
- [Previous declaration in this file](traceNormOp_mul_left_isometry.md)
- [Next declaration in this file](traceNormOp_conjTranspose.md)