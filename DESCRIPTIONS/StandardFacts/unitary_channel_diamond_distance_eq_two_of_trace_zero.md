# unitary_channel_diamond_distance_eq_two_of_trace_zero

## Source location

- Original Lean file: `Diamond/StandardFacts.lean`
- Declaration name: `unitary_channel_diamond_distance_eq_two_of_trace_zero`
- Declaration kind: `theorem`

## Why this declaration exists

This theorem supplies the Eq. (8) input that the identity channel and a traceless unitary channel are
at diamond distance `2`. The Lean proof now constructs the maximally entangled witness directly and
uses the elementary upper bound `‖ρ - σ‖₁ ≤ 2` for density operators.

The statement is intentionally restricted to `[Nonempty d]`. Without that hypothesis the formula is
false in the empty-index case, while every intended paper use works over nonempty finite dimensions.

## Current code

```lean
/-- Background unitary-channel diamond-distance formula used for Eq. (8). -/
theorem unitary_channel_diamond_distance_eq_two_of_trace_zero
    {d : Type u} [Fintype d] [DecidableEq d] [Nonempty d] (U : Matrix d d ℂ) (hU : Uᴴ * U = 1)
    (htrace : Matrix.trace U = 0) :
    diamondOp (idMinus (adMap d U)) = 2 := by
  ...
```

## Mathematical summary

The proof has two parts.

- Upper bound: for every density state `ρ`, both `ρ` and `((Ad_U) ⊗ id)(ρ)` are density states, so
  their trace-distance is at most `2`.
- Lower bound: use the maximally entangled pure state `|Ω⟩⟨Ω|` as a witness. Its image under
  `((Ad_U) ⊗ id)` is another pure state. The overlap of the two witness vectors is
  `tr(U) / card(d)`, so the tracelessness assumption forces orthogonality, and the trace norm of the
  difference is exactly `2`.

## Dependencies and downstream use

### Earlier declarations this depends on
- [`diamond_le_of_pointwise_nonempty`](diamond_le_of_pointwise_nonempty.md) from `StandardFacts.lean`
- [`traceNorm_apply_le_diamond`](traceNorm_apply_le_diamond.md) from `StandardFacts.lean`
- [`traceNormOp_sub_density_le_two`](../Theorem/Lemma1/traceNormOp_sub_density_le_two.md) from `Theorem/Lemma1.lean`

### Later declarations that use this one
- [`theorem_eq8`](../EndMatter/Eq8/theorem_eq8.md) in `EndMatter/Eq8.lean`

## Backlinks

- [Back to `INDEX.md`](../INDEX.md)
- [Back to the `StandardFacts.lean` section in the index](../INDEX.md#diamond-standardfacts-lean)
- [Previous declaration in this file](lemma_transpose_diamond.md)
- [Next declaration in this file](trace_Ud_eq_zero.md)
