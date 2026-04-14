---
layout: default
---

# theorem_not_tight

## Source

- Lean file: `Diamond/PositiveGap/NotTight.lean`
- Declaration: `Diamond.PositiveGap.NotTight.theorem_not_tight`

## Statement

If $T$ is a quantum channel and $\mathrm{id}-T \neq 0$, then the inequality from Theorem 1
is strict:

$$
\|\Theta \circ (\mathrm{id}-T)\|_\diamond
<
\frac{1}{\sqrt{2}}\,
\|\Theta\|_\diamond\,
\|\mathrm{id}-T\|_\diamond.
$$

## What This Proves

The constant $1/\sqrt{2}$ is a universal upper bound, but it is not attained by a nonzero
channel difference in finite dimension.

So the theorem is not just quantitatively stronger than naive submultiplicativity. It is also
qualitatively strict away from the trivial zero case.

## Proof Structure

The proof is an equality-case contradiction argument.

### 1. Assume equality in Theorem 1

Start by assuming the right-hand side of Theorem 1 is actually attained.

Then pick a maximizing witness $\rho$ for the left-hand diamond norm and define

$$
X := ((\mathrm{id}-T)\otimes \mathrm{id})(\rho),
\qquad
Y := \Gamma(X),
$$

where $\Gamma$ is partial transpose.

### 2. Force simultaneous saturation of the norm inequalities

Equality in Theorem 1 means that the proof of Theorem 1 must have been sharp at every step.

So $X$ and $Y$ must simultaneously saturate:

- Lemma 2,
- Lemma 3,
- Lemma 1,
- and the witness bound for the diamond norm.

This makes the geometry of $X$ highly rigid.

### 3. Translate equality into structure

From the channel properties, $X$ is Hermitian and traceless, and its partial trace vanishes.
The project then uses:

- vectorization identities,
- the swap operator,
- purification/Uhlmann-style input,
- and rank estimates under partial transpose.

The effect is to show that an equality witness would have to look like a very special rank-two
object.

### 4. Derive the rank contradiction

The equality analysis eventually forces a matrix $Y_\ast$ to satisfy

$$
\operatorname{rank}(Y_\ast) \le d^2 - d < d^2.
$$

But the same equality assumptions also force full-rank behavior. Those conclusions are
incompatible, so equality cannot occur.

## Why This Theorem Matters

Theorem 1 gives the universal estimate.

`theorem_not_tight` shows the estimate has genuine slack in finite dimension for every nonzero
channel difference. This is the formal version of the paper's “positive gap” statement.
