---
layout: default
---

# PositiveGap Overview

## Purpose

The `PositiveGap/` folder proves that the constant \(1/\sqrt{2}\) from Theorem 1 is not merely
an upper bound that happens to be attained everywhere. In finite dimension, the inequality is
strict as soon as the channel difference is nonzero.

## Main Statement

For a quantum channel \(T\) with \(\mathrm{id}-T \neq 0\),

$$
\|\Theta \circ (\mathrm{id}-T)\|_\diamond
<
\frac{1}{\sqrt{2}}\,
\|\Theta\|_\diamond\,
\|\mathrm{id}-T\|_\diamond.
$$

This is the theorem formalized as
`Diamond.PositiveGap.NotTight.theorem_not_tight`.

## Proof Ingredients

The argument is more geometric than the main theorem.

### 1. Equality would force simultaneous saturation

If equality held in Theorem 1, then the witness matrix would have to saturate:

- the Hilbert--Schmidt versus trace-norm inequality,
- the partial-transpose norm comparison,
- and the diamond-norm witness bound.

That is already a very rigid situation.

### 2. Rank-one / vectorization machinery

Lemmas 5, 6, and 7 formalize the vectorization map and the swap operator. These let the proof
move between matrix statements and rank-one vector statements cleanly.

### 3. Uhlmann-type purification input

The equality case is pushed into a purification/rank statement: a maximizing witness can be
represented in a form rigid enough that equality in the norm inequalities forces an unexpected
rank defect after partial transpose.

### 4. Contradiction by rank bounds

The final contradiction is that equality would force a matrix to be simultaneously too large and
too small in rank:

$$
\operatorname{rank}(Y_\ast) \le d^2 - d < d^2,
$$

while the equality case requires full rank.

## Why This Folder Matters

The main theorem gives the universal inequality. `PositiveGap/` proves that, in finite
dimension, the inequality is genuinely strict away from the trivial zero case. This is the
mathematical reason the paper calls the bound a strict submultiplicativity statement.
