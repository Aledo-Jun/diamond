# ud_add_mul_star_eq

## Source location

- Original Lean file: `Diamond/EndMatter/Eq7.lean`
- Declaration name: `ud_add_mul_star_eq`
- Declaration kind: `theorem`

## Why this declaration exists

Translating indices by `b` removes the compensating phase `star (Ud_d(b,b))`.

 In the file `EndMatter/Eq7.lean`, it contributes to the explicit witness construction used to prove the lower bound labelled Eq. (7). Later proofs call this result by name, so documenting it makes the larger argument readable as a mathematical chain rather than as opaque proof script.

## Original code

```lean
/-- Translating indices by `b` removes the compensating phase `star (Ud_d(b,b))`. -/
theorem ud_add_mul_star_eq (d : ℕ) [Fact (1 < d)] (a b : Fin d) :
    Ud d (a + b) (a + b) * star (Ud d b b) = Ud d a a := by
  rw [ud_add_eq_mul, mul_assoc, ud_mul_star_self, mul_one]
```

## Block-by-block explanation

The explanation below follows the declaration block by block. Each block groups a coherent piece of the definition or proof, so the mathematical structure is easier to see than in a strictly line-oriented reading.

1. Code:
```lean
/-- Translating indices by `b` removes the compensating phase `star (Ud_d(b,b))`. -/
```
This is a Lean docstring. It is a human-written comment that tells readers what the declaration is meant to express before the formal code begins.

2. Code:
```lean
theorem ud_add_mul_star_eq (d : ℕ) [Fact (1 < d)] (a b : Fin d) :
```
This line starts the `ud_add_mul_star_eq` declaration. Because it begins with `theorem`, Lean now knows what kind of named object is being introduced.

3. Code:
```lean
    Ud d (a + b) (a + b) * star (Ud d b b) = Ud d a a := by
```
This line says that a proof script begins here. Everything indented underneath is a sequence of instructions that Lean will check step by step.

4. Code:
```lean
  rw [ud_add_eq_mul, mul_assoc, ud_mul_star_self, mul_one]
```
This line uses rewriting. Lean replaces one expression by an equal expression using the lemmas listed in brackets.

## Mathematical summary

Restated without Lean syntax, `ud_add_mul_star_eq` is the theorem or lemma written above.

- State the desired identity or inequality in Lean’s syntax.
- Introduce temporary names and intermediate claims that organize the argument.
- Use rewriting, simplification, and earlier lemmas to reduce the goal to standard matrix or norm manipulations.
- Close the remaining algebraic or order-theoretic steps with Lean’s proof tactics.

## Dependencies and downstream use

### Earlier declarations this depends on
- [`Ud`](../../Setups/Ud.md) from `Setups.lean`
- [`ud_add_eq_mul`](ud_add_eq_mul.md) from `EndMatter/Eq7.lean`
- [`ud_mul_star_self`](ud_mul_star_self.md) from `EndMatter/Eq7.lean`

### Later declarations that use this one
- [`explicit_witness_traceNorm_eq_sum`](explicit_witness_traceNorm_eq_sum.md) in `EndMatter/Eq7.lean`

## Backlinks

- [Back to `INDEX.md`](../../INDEX.md)
- [Back to the `EndMatter/Eq7.lean` section in the index](../../INDEX.md#diamond-endmatter-eq7-lean)
- [Previous declaration in this file](ud_conjTranspose_mul_self.md)
- [Next declaration in this file](swapMatrix_mul_diagonal_apply.md)