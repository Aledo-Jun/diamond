---
layout: default
---

# alpha_lower_bound

## Source

- Lean file: `Diamond/EndMatter/Eq8.lean`
- Declaration: `Diamond.EndMatter.Eq8.alpha_lower_bound`

## Statement

The project proves the numerical inequality

$$
\frac{2}{\pi} \le \frac{1}{\sqrt{2}}.
$$

Inside the paper, this is read as a lower bound on any universal constant that could replace
$1/\sqrt{2}$ in the main transposition estimate.

## Where It Comes From

This theorem combines three earlier results.

### 1. The abstract upper bound

Theorem 1 gives

$$
\|\Theta \circ (\mathrm{id}-T)\|_\diamond
\le
\alpha\,
\|\Theta\|_\diamond\,
\|\mathrm{id}-T\|_\diamond
$$

with $\alpha = 1/\sqrt{2}$ in the proved theorem.

### 2. The explicit lower bound

Eq. (7) gives

$$
2 \cot\!\left(\frac{\pi}{2d}\right)
\le
\|\Lambda_d\|_\diamond.
$$

### 3. The exact unitary-channel norm

Eq. (8) gives

$$
\|\mathrm{id} - \mathrm{Ad}_{U_d}\|_\diamond = 2.
$$

In the relevant example, $\Lambda_d$ is exactly the transpose composed with that channel
difference, so these three ingredients combine into

$$
2 \cot\!\left(\frac{\pi}{2d}\right)
\le
\frac{1}{\sqrt{2}} \, d \, 2.
$$

After dividing by $d$ and sending $d \to \infty$, the asymptotic cotangent estimate yields

$$
\frac{2}{\pi} \le \frac{1}{\sqrt{2}}.
$$

## Why This Theorem Matters

This is the project's lower-bound obstruction theorem. It shows that no dimension-independent
constant below $2/\pi$ can hold uniformly, even though Theorem 1 proves the upper bound
$1/\sqrt{2}$.
