# remark1

## Source

- Lean file: `Diamond/Theorem/Remark1.lean`
- Declaration: `Diamond.Theorem.Remark1.remark1`

## Statement

For every Hermiticity-preserving, trace-annihilating map \(\Psi\),

$$
\|\Theta \circ \Psi\|_\diamond
\le
\frac{1}{\sqrt{2}}\,
\|\Theta\|_\diamond\,
\|\Psi\|_\diamond.
$$

## Mathematical Role

`theorem1` handles the special case \(\Psi = \mathrm{id}-T\) for a quantum channel \(T\).
`remark1` packages the same argument in the exact form needed by the later coding application.

The point is that the proof of Theorem 1 never used anything special about
\(\mathrm{id}-T\) beyond two structural facts:

$$
\Psi(X^\dagger) = \Psi(X)^\dagger,
\qquad
\operatorname{tr}(\Psi(X)) = 0.
$$

Those are precisely the hypotheses of `remark1`.

## Proof Structure

The proof follows the same pattern as Theorem 1, but with the abstract map \(\Psi\) in place of
\(\mathrm{id}-T\).

### 1. Stabilized witness

Take an arbitrary

$$
\rho \in \mathcal{D}(d \otimes d)
$$

and define

$$
M_\rho := (\Psi \otimes \mathrm{id})(\rho).
$$

### 2. Move transpose into partial transpose

Using the standard commuting identity for ancilla extension and transpose,

$$
((\Theta \circ \Psi)\otimes\mathrm{id})(\rho)
=
\Gamma(M_\rho).
$$

### 3. Use the structural hypotheses

Because \(\Psi\) is Hermiticity-preserving and trace-annihilating, the matrix \(M_\rho\) is
Hermitian and traceless.

This is the key input that makes Lemma 1 applicable.

### 4. Apply the same three-lemma chain

Exactly as in Theorem 1,

$$
\|\Gamma(M_\rho)\|_1
\le
\sqrt{d^2}\,\|M_\rho\|_2
\le
\sqrt{d^2}\,\frac{1}{\sqrt{2}}\|M_\rho\|_1.
$$

### 5. Convert back to \(\|\Psi\|_\diamond\)

The witness norm satisfies

$$
\|M_\rho\|_1 \le \|\Psi\|_\diamond,
$$

and \(\sqrt{d^2} = \|\Theta\|_\diamond\), so the stated inequality follows.

## Why This Remark Matters

This is the form used later in the paper.

In the Holevo--Werner coding argument, the perturbation

$$
\Psi
=
\mathrm{id} - \mathcal{D}\circ T^{\otimes m}\circ\mathcal{E}
$$

is naturally Hermiticity-preserving and trace-annihilating. `remark1` is therefore the exact
tool needed to improve the original finite-error threshold.
