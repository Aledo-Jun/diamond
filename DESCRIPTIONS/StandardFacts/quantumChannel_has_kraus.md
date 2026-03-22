# quantumChannel_has_kraus

## Source location

- Original Lean file: `Diamond/StandardFacts.lean`
- Declaration name: `quantumChannel_has_kraus`
- Declaration kind: `theorem`

## Why this declaration exists

This theorem exposes the Kraus data stored inside the project’s current definition of
`IsQuantumChannel`.

After the channel structure was strengthened, Lean no longer needs an external Kraus-representation
axiom here. The theorem is now just the accessor that unwraps the witness already bundled with
`hT : IsQuantumChannel T`.

## Current code

```lean
/-- Background Kraus representation for finite-dimensional quantum channels. -/
theorem quantumChannel_has_kraus
    {d : Type u} [Fintype d] [DecidableEq d] {T : Channel d} :
    IsQuantumChannel T →
    ∃ (r : ℕ), ∃ (E : Fin r → Matrix d d ℂ),
      (∀ X, T X = ∑ i, E i * X * (E i)ᴴ) ∧
      (∑ i, (E i)ᴴ * E i = 1) := by
  intro hT
  exact hT.kraus
```

## Block-by-block explanation

1. The theorem states exactly the usual finite-dimensional Kraus conclusion.
2. The proof introduces `hT : IsQuantumChannel T`.
3. The final line returns `hT.kraus`, which is the Kraus witness field already stored in the
   structure.

## Mathematical summary

Mathematically, nothing deep is reproved at this point. The content is:

- if `T` is a quantum channel in the project’s sense,
- then `T` comes equipped with Kraus operators `E_i`,
- and this theorem simply projects that data back out.

## Dependencies and downstream use

### Earlier declarations this depends on
- [`Channel`](../Setups/Channel.md) from `Setups.lean`
- [`IsQuantumChannel`](../Setups/IsQuantumChannel.md) from `Setups.lean`

### Later declarations that use this one
- [`lemma4`](../PositiveGap/Lemma4/lemma4.md) in `PositiveGap/Lemma4.lean`

## Backlinks

- [Back to `INDEX.md`](../INDEX.md)
- [Back to the `StandardFacts.lean` section in the index](../INDEX.md#diamond-standardfacts-lean)
