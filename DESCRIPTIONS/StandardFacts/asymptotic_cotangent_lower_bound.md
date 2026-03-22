# asymptotic_cotangent_lower_bound

## Source location

- Original Lean file: `Diamond/StandardFacts.lean`
- Declaration name: `asymptotic_cotangent_lower_bound`
- Declaration kind: `theorem`

## Why this declaration exists

This theorem passes from finite-dimensional cotangent bounds to the universal lower bound
\[
2 / \pi \le \alpha.
\]

It is no longer assumed. The proof is now internal and works by constructing an explicit sequence
whose limit is `2 / π`, then applying the uniform finite-dimensional hypothesis along that
sequence.

## Current code

```lean
theorem asymptotic_cotangent_lower_bound
    {α : ℝ} :
    (∀ d : ℕ, 2 ≤ d → Real.cot (Real.pi / (2 * (d : ℝ))) / (d : ℝ) ≤ α) →
      (2 : ℝ) / Real.pi ≤ α := by
  ...
```

## Block-by-block explanation

1. Define the auxiliary sequences `xSeq` and `cotSeq`.
2. Show `xSeq → 0`.
3. Rewrite `cotSeq` as `(2 / π) * (cos xSeq / sinc xSeq)`.
4. Use continuity of `cos` and `sinc` at `0` to prove `cotSeq → 2 / π`.
5. Apply the hypothesis at dimensions `d = n + 2` to get `cotSeq n ≤ α`.
6. Pass to the limit to conclude `2 / π ≤ α`.

## Mathematical summary

This theorem is the asymptotic bridge from the explicit finite-dimensional lower bounds in Eq. (7)
to the universal constant obstruction used in Eq. (8) and the final coding consequence.

## Dependencies and downstream use

### Earlier declarations this depends on
- This theorem mainly depends on local real-analysis lemmas and the auxiliary sequences defined just
  above it in `StandardFacts.lean`.

### Later declarations that use this one
- [`alpha_lower_bound`](../EndMatter/Eq8/alpha_lower_bound.md) in `EndMatter/Eq8.lean`

## Backlinks

- [Back to `INDEX.md`](../INDEX.md)
- [Back to the `StandardFacts.lean` section in the index](../INDEX.md#diamond-standardfacts-lean)
