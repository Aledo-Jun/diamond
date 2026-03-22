# idMinus

## Source location

- Original Lean file: `Diamond/Setups.lean`
- Declaration name: `idMinus`
- Declaration kind: `def`

## Why this declaration exists

This is the basic perturbation map $X \mapsto X - \Phi(X)$, which becomes $\mathrm{id}-T$ when $\Phi=T$.

 In the file `Setups.lean`, it contributes to foundational objects and notational definitions for operators, channels, norms, and the maps studied in the paper. Later declarations use this name instead of repeatedly expanding the underlying matrix formula.

## Original code

```lean
/-- The map `X ↦ X - Φ X`. -/
def idMinus
    {d : Type u} [Fintype d] [DecidableEq d] (Φ : Channel d) : Channel d where
  toFun := fun X => X - Φ X
  map_add' := by
    intro X Y
    ext i j
    simp [map_add, sub_eq_add_neg, add_assoc, add_left_comm, add_comm]
  map_smul' := by
    intro c X
    ext i j
    simp [map_smul, sub_eq_add_neg, mul_add]
```

## Block-by-block explanation

The explanation below follows the declaration block by block. Each block groups a coherent piece of the definition or proof, so the mathematical structure is easier to see than in a strictly line-oriented reading.

1. Code:
```lean
/-- The map `X ↦ X - Φ X`. -/
```
This is a Lean docstring. It is a human-written comment that tells readers what the declaration is meant to express before the formal code begins.

2. Code:
```lean
def idMinus
```
This line starts the `idMinus` declaration. Because it begins with `def`, Lean now knows what kind of named object is being introduced.

3. Code:
```lean
    {d : Type u} [Fintype d] [DecidableEq d] (Φ : Channel d) : Channel d where
```
This line starts a `where` block. In Lean, a `where` block lists the fields of a structure or bundled map.

4. Code:
```lean
  toFun := fun X => X - Φ X
```
This line is one local step in the declaration. It either refines the formula being defined or advances the proof by a small algebraic or logical move.

5. Code:
```lean
  map_add' := by
```
This line says that a proof script begins here. Everything indented underneath is a sequence of instructions that Lean will check step by step.

6. Code:
```lean
    intro X Y
```
This line introduces the variable or hypothesis named here into the proof context. In ordinary mathematical prose, it is the same as saying “let” or “assume”.

7. Code:
```lean
    ext i j
```
This line invokes extensionality. To prove two maps or matrices are equal, Lean reduces the problem to checking their values entry by entry.

8. Code:
```lean
    simp [map_add, sub_eq_add_neg, add_assoc, add_left_comm, add_comm]
```
This line simplifies the goal using definitions and known equalities. `simpa` means that, after simplification, the desired statement matches a theorem Lean already has.

9. Code:
```lean
  map_smul' := by
```
This line says that a proof script begins here. Everything indented underneath is a sequence of instructions that Lean will check step by step.

10. Code:
```lean
    intro c X
```
This line introduces the variable or hypothesis named here into the proof context. In ordinary mathematical prose, it is the same as saying “let” or “assume”.

11. Code:
```lean
    ext i j
```
This line invokes extensionality. To prove two maps or matrices are equal, Lean reduces the problem to checking their values entry by entry.

12. Code:
```lean
    simp [map_smul, sub_eq_add_neg, mul_add]
```
This line simplifies the goal using definitions and known equalities. `simpa` means that, after simplification, the desired statement matches a theorem Lean already has.

## Mathematical summary

In ordinary mathematical language, `idMinus` is the project's formal Lean name for the object introduced in this declaration.

## Dependencies and downstream use

### Earlier declarations this depends on
- [`Channel`](Channel.md) from `Setups.lean`

### Later declarations that use this one
- [`Lambda`](Lambda.md) in `Setups.lean`
- [`idMinus_isHermiticityPreserving`](../StandardFacts/idMinus_isHermiticityPreserving.md) in `StandardFacts.lean`
- [`idMinus_isTraceAnnihilating`](../StandardFacts/idMinus_isTraceAnnihilating.md) in `StandardFacts.lean`
- [`unitary_channel_diamond_distance_eq_two_of_trace_zero`](../StandardFacts/unitary_channel_diamond_distance_eq_two_of_trace_zero.md) in `StandardFacts.lean`
- [`exists_maximizing_state`](../StandardFacts/exists_maximizing_state.md) in `StandardFacts.lean`
- [`theorem1`](../Theorem/Theorem1/theorem1.md) in `Theorem/Theorem1.lean`
- [`corollary1`](../PositiveGap/Corollary1/corollary1.md) in `PositiveGap/Corollary1.lean`
- [`theorem_not_tight`](../PositiveGap/NotTight/theorem_not_tight.md) in `PositiveGap/NotTight.lean`
- [`lambda_phiState_eq`](../EndMatter/Eq7/lambda_phiState_eq.md) in `EndMatter/Eq7.lean`
- [`theorem_eq8`](../EndMatter/Eq8/theorem_eq8.md) in `EndMatter/Eq8.lean`
- [`alpha_lower_bound`](../EndMatter/Eq8/alpha_lower_bound.md) in `EndMatter/Eq8.lean`
- [`corollary2_linear_bound`](../EndMatter/Corollary2/corollary2_linear_bound.md) in `EndMatter/Corollary2.lean`
- [`corollary2`](../EndMatter/Corollary2/corollary2.md) in `EndMatter/Corollary2.lean`

## Backlinks

- [Back to `INDEX.md`](../INDEX.md)
- [Back to the `Setups.lean` section in the index](../INDEX.md#diamond-setups-lean)
- [Previous declaration in this file](partialTraceLeft.md)
- [Next declaration in this file](adMap.md)