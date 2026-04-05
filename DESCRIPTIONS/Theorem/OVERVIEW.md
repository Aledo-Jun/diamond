# Theorem Overview

## Purpose

The `Theorem/` folder is the mathematical core of the repository. It isolates three matrix-norm
lemmas and then combines them into the main transposition estimate.

## Proof Pipeline

The structure is:

$$
\text{Lemma 1}
\;+\;
\text{Lemma 2}
\;+\;
\text{Lemma 3}
\Longrightarrow
\text{Theorem 1}
\Longrightarrow
\text{Remark 1}.
$$

### Lemma 1

For Hermitian traceless matrices, the Hilbert--Schmidt norm is controlled by the trace norm:

$$
\|X\|_2 \le \frac{1}{\sqrt{2}} \|X\|_1.
$$

This is where the factor \(1/\sqrt{2}\) enters.

### Lemma 2

For matrices on an \(N\)-dimensional space,

$$
\|Y\|_1 \le \sqrt{N}\,\|Y\|_2.
$$

This is the ordinary comparison between Schatten \(1\)- and \(2\)-norms.

### Lemma 3

Partial transpose preserves the Hilbert--Schmidt norm:

$$
\|\Gamma(X)\|_2 = \|X\|_2.
$$

### Theorem 1

For a quantum channel \(T\),

$$
\|\Theta \circ (\mathrm{id}-T)\|_\diamond
\le
\frac{1}{\sqrt{2}}\,
\|\Theta\|_\diamond\,
\|\mathrm{id}-T\|_\diamond.
$$

The proof rewrites a stabilized witness through partial transpose, applies Lemma 3, then
Lemma 2, then Lemma 1, and finally the witness bound coming from the definition of
\(\|\mathrm{id}-T\|_\diamond\).

### Remark 1

The same argument works for any Hermiticity-preserving, trace-annihilating map \(\Psi\):

$$
\|\Theta \circ \Psi\|_\diamond
\le
\frac{1}{\sqrt{2}}\,
\|\Theta\|_\diamond\,
\|\Psi\|_\diamond.
$$

This is the version used later in the coding argument.

## Why This Folder Matters

Everything after this point is an application or consequence:

- `PositiveGap/` proves the inequality is strict in finite dimension for nonzero channel
  differences.
- `EndMatter/Eq7.lean` and `Eq8.lean` turn the theorem into explicit lower bounds.
- `HolevoWerner/` plugs `Remark 1` into the finite-error coding argument.
