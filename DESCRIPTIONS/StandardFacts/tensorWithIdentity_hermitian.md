# tensorWithIdentity_hermitian

## Source location

- Original Lean file: `Diamond/StandardFacts.lean`
- Declaration name: `tensorWithIdentity_hermitian`
- Declaration kind: `theorem`

## Why this declaration exists

Tensoring a Hermiticity-preserving map with the identity preserves Hermiticity.

 In the file `StandardFacts.lean`, it contributes to helper facts and background reductions that later proofs use directly. Later proofs call this result by name, so documenting it makes the larger argument readable as a mathematical chain rather than as opaque proof script.

## Original code

```lean
/-- Tensoring a Hermiticity-preserving map with the identity preserves Hermiticity. -/
theorem tensorWithIdentity_hermitian
    {d k : Type u} [Fintype d] [DecidableEq d] [Fintype k] [DecidableEq k]
    (Ψ : Channel d) (hH : IsHermiticityPreserving Ψ)
    (ρ : Matrix (d × k) (d × k) ℂ) (hρ : IsDensityState ρ) :
    Matrix.IsHermitian (tensorWithIdentity d k Ψ ρ) := by
  change (tensorWithIdentity d k Ψ ρ)ᴴ = tensorWithIdentity d k Ψ ρ
  ext p q
  let A : Matrix d d ℂ := fun i j => ρ (i, p.2) (j, q.2)
  have hρh : Matrix.IsHermitian ρ := hρ.1.isHermitian
  have hA : Aᴴ = fun i j : d => ρ (i, q.2) (j, p.2) := by
    ext i j
    simpa [A, Matrix.conjTranspose_apply] using
      congrArg (fun M => M (i, q.2) (j, p.2)) hρh.eq
  have hcomm := hH A
  have hpoint : Ψ Aᴴ q.1 p.1 = star (Ψ A p.1 q.1) := by
    simpa [Matrix.conjTranspose_apply] using congrArg (fun M => M q.1 p.1) hcomm
  have hpoint' : star (Ψ Aᴴ q.1 p.1) = Ψ A p.1 q.1 := by
    simpa using congrArg star hpoint
  simpa [A, hA, tensorWithIdentity, Matrix.conjTranspose_apply] using hpoint'
```

## Block-by-block explanation

The explanation below follows the declaration block by block. Each block groups a coherent piece of the definition or proof, so the mathematical structure is easier to see than in a strictly line-oriented reading.

1. Code:
```lean
/-- Tensoring a Hermiticity-preserving map with the identity preserves Hermiticity. -/
```
This is a Lean docstring. It is a human-written comment that tells readers what the declaration is meant to express before the formal code begins.

2. Code:
```lean
theorem tensorWithIdentity_hermitian
```
This line starts the `tensorWithIdentity_hermitian` declaration. Because it begins with `theorem`, Lean now knows what kind of named object is being introduced.

3. Code:
```lean
    {d k : Type u} [Fintype d] [DecidableEq d] [Fintype k] [DecidableEq k]
```
This line is one local step in the declaration. It either refines the formula being defined or advances the proof by a small algebraic or logical move.  A bracket such as `[Fintype d]` tells Lean that the index set `d` is finite, so sums over all indices make sense.  A bracket such as `[DecidableEq d]` tells Lean that it can decide whether two indices are equal.

4. Code:
```lean
    (Ψ : Channel d) (hH : IsHermiticityPreserving Ψ)
```
This line is one local step in the declaration. It either refines the formula being defined or advances the proof by a small algebraic or logical move.  `Channel d` is an abbreviation for a complex-linear map from operators on `d` to operators on `d`.

5. Code:
```lean
    (ρ : Matrix (d × k) (d × k) ℂ) (hρ : IsDensityState ρ) :
```
This line is one local step in the declaration. It either refines the formula being defined or advances the proof by a small algebraic or logical move.  `Matrix d d ℂ` means a square matrix with complex entries; the index type `d` tells Lean which rows and columns exist.

6. Code:
```lean
    Matrix.IsHermitian (tensorWithIdentity d k Ψ ρ) := by
```
This line says that a proof script begins here. Everything indented underneath is a sequence of instructions that Lean will check step by step.

7. Code:
```lean
  change (tensorWithIdentity d k Ψ ρ)ᴴ = tensorWithIdentity d k Ψ ρ
```
This line replaces the current goal by a definitionally equal goal that is easier to manipulate.  The superscript `ᴴ` means conjugate transpose (also called the adjoint).

8. Code:
```lean
  ext p q
```
This line invokes extensionality. To prove two maps or matrices are equal, Lean reduces the problem to checking their values entry by entry.

9. Code:
```lean
  let A : Matrix d d ℂ := fun i j => ρ (i, p.2) (j, q.2)
```
This line gives a temporary name to an expression. Doing that makes later lines shorter and easier to read.  `Matrix d d ℂ` means a square matrix with complex entries; the index type `d` tells Lean which rows and columns exist.

10. Code:
```lean
  have hρh : Matrix.IsHermitian ρ := hρ.1.isHermitian
```
This line introduces an intermediate claim. The proof pauses to establish a fact that will be used shortly afterwards.

11. Code:
```lean
  have hA : Aᴴ = fun i j : d => ρ (i, q.2) (j, p.2) := by
```
This line says that a proof script begins here. Everything indented underneath is a sequence of instructions that Lean will check step by step.  The superscript `ᴴ` means conjugate transpose (also called the adjoint).

12. Code:
```lean
    ext i j
```
This line invokes extensionality. To prove two maps or matrices are equal, Lean reduces the problem to checking their values entry by entry.

13. Code:
```lean
    simpa [A, Matrix.conjTranspose_apply] using
```
This line simplifies the goal using definitions and known equalities. `simpa` means that, after simplification, the desired statement matches a theorem Lean already has.

14. Code:
```lean
      congrArg (fun M => M (i, q.2) (j, p.2)) hρh.eq
```
This line applies the same function to both sides of a known equality, producing a new equality better suited to the current goal.

15. Code:
```lean
  have hcomm := hH A
```
This line introduces an intermediate claim. The proof pauses to establish a fact that will be used shortly afterwards.

16. Code:
```lean
  have hpoint : Ψ Aᴴ q.1 p.1 = star (Ψ A p.1 q.1) := by
```
This line says that a proof script begins here. Everything indented underneath is a sequence of instructions that Lean will check step by step.  The superscript `ᴴ` means conjugate transpose (also called the adjoint).

17. Code:
```lean
    simpa [Matrix.conjTranspose_apply] using congrArg (fun M => M q.1 p.1) hcomm
```
This line simplifies the goal using definitions and known equalities. `simpa` means that, after simplification, the desired statement matches a theorem Lean already has.

18. Code:
```lean
  have hpoint' : star (Ψ Aᴴ q.1 p.1) = Ψ A p.1 q.1 := by
```
This line says that a proof script begins here. Everything indented underneath is a sequence of instructions that Lean will check step by step.  The superscript `ᴴ` means conjugate transpose (also called the adjoint).

19. Code:
```lean
    simpa using congrArg star hpoint
```
This line simplifies the goal using definitions and known equalities. `simpa` means that, after simplification, the desired statement matches a theorem Lean already has.

20. Code:
```lean
  simpa [A, hA, tensorWithIdentity, Matrix.conjTranspose_apply] using hpoint'
```
This line simplifies the goal using definitions and known equalities. `simpa` means that, after simplification, the desired statement matches a theorem Lean already has.

## Mathematical summary

Restated without Lean syntax, `tensorWithIdentity_hermitian` is the theorem or lemma written above.

- State the desired identity or inequality in Lean’s syntax.
- Introduce temporary names and intermediate claims that organize the argument.
- Use rewriting, simplification, and earlier lemmas to reduce the goal to standard matrix or norm manipulations.
- Close the remaining algebraic or order-theoretic steps with Lean’s proof tactics.

## Dependencies and downstream use

### Earlier declarations this depends on
- [`Channel`](../Setups/Channel.md) from `Setups.lean`
- [`IsDensityState`](../Setups/IsDensityState.md) from `Setups.lean`
- [`IsHermiticityPreserving`](../Setups/IsHermiticityPreserving.md) from `Setups.lean`
- [`tensorWithIdentity`](../Setups/tensorWithIdentity.md) from `Setups.lean`

### Later declarations that use this one
- [`theorem1`](../Theorem/Theorem1/theorem1.md) in `Theorem/Theorem1.lean`
- [`remark1`](../Theorem/Remark1/remark1.md) in `Theorem/Remark1.lean`
- [`theorem_not_tight`](../PositiveGap/NotTight/theorem_not_tight.md) in `PositiveGap/NotTight.lean`

## Backlinks

- [Back to `INDEX.md`](../INDEX.md)
- [Back to the `StandardFacts.lean` section in the index](../INDEX.md#diamond-standardfacts-lean)
- [Previous declaration in this file](tensorWithIdentity_trace_zero.md)
- [Next declaration in this file](sqrt_card_prod_self.md)