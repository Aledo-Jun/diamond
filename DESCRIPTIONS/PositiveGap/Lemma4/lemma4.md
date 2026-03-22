# lemma4

## Source location

- Original Lean file: `Diamond/PositiveGap/Lemma4.lean`
- Declaration name: `lemma4`
- Declaration kind: `theorem`

## Why this declaration exists

This lemma proves that tensoring a quantum channel with the identity does not change the partial trace over the channel side.

 In the file `PositiveGap/Lemma4.lean`, it contributes to the partial-trace identity for tensoring a quantum channel with the identity. Later proofs call this result by name, so documenting it makes the larger argument readable as a mathematical chain rather than as opaque proof script.

## Original code

```lean
/-- Paper Lemma 4: partial trace on the left is unchanged by tensoring with a quantum channel. -/
theorem lemma4
    {d : Type u} [Fintype d] [DecidableEq d]
    (T : Channel d) (hT : IsQuantumChannel T)
    {k : Type u} [Fintype k] [DecidableEq k]
    (Z : Matrix (d × k) (d × k) ℂ) :
    partialTraceLeft d k (tensorWithIdentity d k T Z) = partialTraceLeft d k Z := by
  obtain ⟨r, E, hmap, hcomplete⟩ := quantumChannel_has_kraus (T := T) hT
  ext i j
  let A : Matrix d d ℂ := fun a b => Z (a, i) (b, j)
  calc
    partialTraceLeft d k (tensorWithIdentity d k T Z) i j = Matrix.trace (T A) := by
      simp [partialTraceLeft, tensorWithIdentity, A, Matrix.trace]
    _ = Matrix.trace (∑ n : Fin r, E n * A * (E n)ᴴ) := by
      simp [hmap]
    _ = ∑ n : Fin r, Matrix.trace (E n * A * (E n)ᴴ) := by
      simpa using (Matrix.trace_sum (s := (Finset.univ : Finset (Fin r)))
        (f := fun n => E n * A * (E n)ᴴ))
    _ = ∑ n : Fin r, Matrix.trace (A * ((E n)ᴴ * E n)) := by
      refine Finset.sum_congr rfl ?_
      intro n hn
      calc
        Matrix.trace (E n * A * (E n)ᴴ)
            = Matrix.trace (((E n)ᴴ * E n) * A) := by
              simpa [Matrix.mul_assoc] using (Matrix.trace_mul_cycle (E n) A (E n)ᴴ)
        _ = Matrix.trace (A * ((E n)ᴴ * E n)) := by
              simpa [Matrix.mul_assoc] using (Matrix.trace_mul_comm ((E n)ᴴ * E n) A)
    _ = Matrix.trace (∑ n : Fin r, A * ((E n)ᴴ * E n)) := by
      simpa using
        (Matrix.trace_sum (s := (Finset.univ : Finset (Fin r))
          )
          (f := fun n => A * ((E n)ᴴ * E n))).symm
    _ = Matrix.trace (A * (∑ n : Fin r, (E n)ᴴ * E n)) := by
      simp [Matrix.mul_sum]
    _ = Matrix.trace (A * 1) := by
      rw [hcomplete]
    _ = partialTraceLeft d k Z i j := by
      simp [A, partialTraceLeft, Matrix.trace]
```

## Block-by-block explanation

The explanation below follows the declaration block by block. Each block groups a coherent piece of the definition or proof, so the mathematical structure is easier to see than in a strictly line-oriented reading.

1. Code:
```lean
/-- Paper Lemma 4: partial trace on the left is unchanged by tensoring with a quantum channel. -/
```
This is a Lean docstring. It is a human-written comment that tells readers what the declaration is meant to express before the formal code begins.

2. Code:
```lean
theorem lemma4
```
This line starts the `lemma4` declaration. Because it begins with `theorem`, Lean now knows what kind of named object is being introduced.

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
    {k : Type u} [Fintype k] [DecidableEq k]
```
This line is one local step in the declaration. It either refines the formula being defined or advances the proof by a small algebraic or logical move.  A bracket such as `[Fintype d]` tells Lean that the index set `d` is finite, so sums over all indices make sense.  A bracket such as `[DecidableEq d]` tells Lean that it can decide whether two indices are equal.

6. Code:
```lean
    (Z : Matrix (d × k) (d × k) ℂ) :
```
This line is one local step in the declaration. It either refines the formula being defined or advances the proof by a small algebraic or logical move.  `Matrix d d ℂ` means a square matrix with complex entries; the index type `d` tells Lean which rows and columns exist.

7. Code:
```lean
    partialTraceLeft d k (tensorWithIdentity d k T Z) = partialTraceLeft d k Z := by
```
This line says that a proof script begins here. Everything indented underneath is a sequence of instructions that Lean will check step by step.

8. Code:
```lean
  obtain ⟨r, E, hmap, hcomplete⟩ := quantumChannel_has_kraus (T := T) hT
```
This line unpacks an existential statement or tuple into named pieces.

9. Code:
```lean
  ext i j
```
This line invokes extensionality. To prove two maps or matrices are equal, Lean reduces the problem to checking their values entry by entry.

10. Code:
```lean
  let A : Matrix d d ℂ := fun a b => Z (a, i) (b, j)
```
This line gives a temporary name to an expression. Doing that makes later lines shorter and easier to read.  `Matrix d d ℂ` means a square matrix with complex entries; the index type `d` tells Lean which rows and columns exist.

11. Code:
```lean
  calc
```
This line begins a chained calculation. Each displayed step that follows must be justified by the indented proof after `:= by`.

12. Code:
```lean
    partialTraceLeft d k (tensorWithIdentity d k T Z) i j = Matrix.trace (T A) := by
```
This line says that a proof script begins here. Everything indented underneath is a sequence of instructions that Lean will check step by step.

13. Code:
```lean
      simp [partialTraceLeft, tensorWithIdentity, A, Matrix.trace]
```
This line simplifies the goal using definitions and known equalities. `simpa` means that, after simplification, the desired statement matches a theorem Lean already has.

14. Code:
```lean
    _ = Matrix.trace (∑ n : Fin r, E n * A * (E n)ᴴ) := by
```
This line says that a proof script begins here. Everything indented underneath is a sequence of instructions that Lean will check step by step.  The superscript `ᴴ` means conjugate transpose (also called the adjoint).

15. Code:
```lean
      simp [hmap]
```
This line simplifies the goal using definitions and known equalities. `simpa` means that, after simplification, the desired statement matches a theorem Lean already has.

16. Code:
```lean
    _ = ∑ n : Fin r, Matrix.trace (E n * A * (E n)ᴴ) := by
```
This line says that a proof script begins here. Everything indented underneath is a sequence of instructions that Lean will check step by step.  The superscript `ᴴ` means conjugate transpose (also called the adjoint).

17. Code:
```lean
      simpa using (Matrix.trace_sum (s := (Finset.univ : Finset (Fin r)))
```
This line simplifies the goal using definitions and known equalities. `simpa` means that, after simplification, the desired statement matches a theorem Lean already has.

18. Code:
```lean
        (f := fun n => E n * A * (E n)ᴴ))
```
This line is one local step in the declaration. It either refines the formula being defined or advances the proof by a small algebraic or logical move.  The superscript `ᴴ` means conjugate transpose (also called the adjoint).

19. Code:
```lean
    _ = ∑ n : Fin r, Matrix.trace (A * ((E n)ᴴ * E n)) := by
```
This line says that a proof script begins here. Everything indented underneath is a sequence of instructions that Lean will check step by step.  The superscript `ᴴ` means conjugate transpose (also called the adjoint).

20. Code:
```lean
      refine Finset.sum_congr rfl ?_
```
This line is a more controlled version of `apply`. It sets up the proof with a partly specified argument and leaves smaller goals to solve next.

21. Code:
```lean
      intro n hn
```
This line introduces the variable or hypothesis named here into the proof context. In ordinary mathematical prose, it is the same as saying “let” or “assume”.

22. Code:
```lean
      calc
```
This line begins a chained calculation. Each displayed step that follows must be justified by the indented proof after `:= by`.

23. Code:
```lean
        Matrix.trace (E n * A * (E n)ᴴ)
```
This line is one local step in the declaration. It either refines the formula being defined or advances the proof by a small algebraic or logical move.  The superscript `ᴴ` means conjugate transpose (also called the adjoint).

24. Code:
```lean
            = Matrix.trace (((E n)ᴴ * E n) * A) := by
```
This line says that a proof script begins here. Everything indented underneath is a sequence of instructions that Lean will check step by step.  The superscript `ᴴ` means conjugate transpose (also called the adjoint).

25. Code:
```lean
              simpa [Matrix.mul_assoc] using (Matrix.trace_mul_cycle (E n) A (E n)ᴴ)
```
This line simplifies the goal using definitions and known equalities. `simpa` means that, after simplification, the desired statement matches a theorem Lean already has.  The superscript `ᴴ` means conjugate transpose (also called the adjoint).

26. Code:
```lean
        _ = Matrix.trace (A * ((E n)ᴴ * E n)) := by
```
This line says that a proof script begins here. Everything indented underneath is a sequence of instructions that Lean will check step by step.  The superscript `ᴴ` means conjugate transpose (also called the adjoint).

27. Code:
```lean
              simpa [Matrix.mul_assoc] using (Matrix.trace_mul_comm ((E n)ᴴ * E n) A)
```
This line simplifies the goal using definitions and known equalities. `simpa` means that, after simplification, the desired statement matches a theorem Lean already has.  The superscript `ᴴ` means conjugate transpose (also called the adjoint).

28. Code:
```lean
    _ = Matrix.trace (∑ n : Fin r, A * ((E n)ᴴ * E n)) := by
```
This line says that a proof script begins here. Everything indented underneath is a sequence of instructions that Lean will check step by step.  The superscript `ᴴ` means conjugate transpose (also called the adjoint).

29. Code:
```lean
      simpa using
```
This line simplifies the goal using definitions and known equalities. `simpa` means that, after simplification, the desired statement matches a theorem Lean already has.

30. Code:
```lean
        (Matrix.trace_sum (s := (Finset.univ : Finset (Fin r))
```
This line is one local step in the declaration. It either refines the formula being defined or advances the proof by a small algebraic or logical move.

31. Code:
```lean
          )
```
This line is one local step in the declaration. It either refines the formula being defined or advances the proof by a small algebraic or logical move.

32. Code:
```lean
          (f := fun n => A * ((E n)ᴴ * E n))).symm
```
This line is one local step in the declaration. It either refines the formula being defined or advances the proof by a small algebraic or logical move.  The superscript `ᴴ` means conjugate transpose (also called the adjoint).

33. Code:
```lean
    _ = Matrix.trace (A * (∑ n : Fin r, (E n)ᴴ * E n)) := by
```
This line says that a proof script begins here. Everything indented underneath is a sequence of instructions that Lean will check step by step.  The superscript `ᴴ` means conjugate transpose (also called the adjoint).

34. Code:
```lean
      simp [Matrix.mul_sum]
```
This line simplifies the goal using definitions and known equalities. `simpa` means that, after simplification, the desired statement matches a theorem Lean already has.

35. Code:
```lean
    _ = Matrix.trace (A * 1) := by
```
This line says that a proof script begins here. Everything indented underneath is a sequence of instructions that Lean will check step by step.

36. Code:
```lean
      rw [hcomplete]
```
This line uses rewriting. Lean replaces one expression by an equal expression using the lemmas listed in brackets.

37. Code:
```lean
    _ = partialTraceLeft d k Z i j := by
```
This line says that a proof script begins here. Everything indented underneath is a sequence of instructions that Lean will check step by step.

38. Code:
```lean
      simp [A, partialTraceLeft, Matrix.trace]
```
This line simplifies the goal using definitions and known equalities. `simpa` means that, after simplification, the desired statement matches a theorem Lean already has.

## Mathematical summary

Restated without Lean syntax, `lemma4` is the theorem or lemma written above.

- Choose a Kraus decomposition for the quantum channel.
- Expand the channel action on a simple tensor decomposition of the bipartite operator.
- Apply the partial trace entrywise and use cyclicity of trace.
- Use the Kraus completeness relation $\sum_k E_k^\dagger E_k = I$ to recover the original partial trace.

## Dependencies and downstream use

### Earlier declarations this depends on
- [`Channel`](../../Setups/Channel.md) from `Setups.lean`
- [`IsQuantumChannel`](../../Setups/IsQuantumChannel.md) from `Setups.lean`
- [`tensorWithIdentity`](../../Setups/tensorWithIdentity.md) from `Setups.lean`
- [`partialTraceLeft`](../../Setups/partialTraceLeft.md) from `Setups.lean`
- [`quantumChannel_has_kraus`](../../StandardFacts/quantumChannel_has_kraus.md) from `StandardFacts.lean`

### Later declarations that use this one
- [`corollary1`](../Corollary1/corollary1.md) in `PositiveGap/Corollary1.lean`

## Backlinks

- [Back to `INDEX.md`](../../INDEX.md)
- [Back to the `PositiveGap/Lemma4.lean` section in the index](../../INDEX.md#diamond-positivegap-lemma4-lean)