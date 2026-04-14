---
layout: default
---

# diamondOp_transpose_tensorPowerChannel_le_pow

## Source

- Lean file: `Diamond/HolevoWerner/Theorem.lean`
- Declaration: `Diamond.HolevoWerner.Theorem.diamondOp_transpose_tensorPowerChannel_le_pow`

## Statement

For the concrete recursive tensor-power channel `tensorPowerChannel T m`,

$$
\left\|(\Theta \circ T^{\otimes m})_{\mathrm{rec}}\right\|_\diamond
\le
\left\|\Theta \circ T\right\|_\diamond^m.
$$

Here the subscript “rec” emphasizes that the repository formalizes $T^{\otimes m}$ as a
specific recursive channel on the block space `TensorPowerType phys m`.

## Why This Theorem Matters

This theorem closes the last formerly external hypothesis in the coding argument.

Earlier versions of the project reduced Corollary 2 to a bound of the form

$$
\left\|\Theta \circ T^{\otimes m}\right\|_\diamond
\le
\left\|\Theta \circ T\right\|_\diamond^m,
$$

but still left that estimate as an assumption. This theorem proves it internally for the
repository's concrete recursive tensor-power object.

## Proof Structure

The proof is by induction on $m$.

### 1. Base cases

The recursive tensor-power channel is normalized so that:

$$
T^{\otimes 0} = \mathrm{id},
\qquad
T^{\otimes 1} = T.
$$

The file proves these base cases explicitly, together with the corresponding transpose-norm
identities.

### 2. Recursive decomposition

The key structural identity is the transposed successor formula:

$$
\Theta \circ T^{\otimes (n+1)}
=
(\mathrm{id} \otimes (\Theta \circ T))
\circ
((\Theta \circ T^{\otimes n}) \otimes \mathrm{id}),
$$

written in the repository using the recursive block type and the left/right tensor-extension
operators.

### 3. Bound the “old block” factor

The term involving $T^{\otimes n}$ acts on a larger ancilla space than the one used in the
definition of `diamondOp`. The proof therefore reindexes the witness space and applies the
generic ancilla-stability theorem already developed earlier:

$$
\|\Phi\|_{\diamond,k} \le \|\Phi\|_\diamond
$$

for Hermiticity-preserving maps.

### 4. Bound the last one-use factor

The final one-use factor is controlled using a new induced trace-norm estimate on Hermitian
inputs:

$$
\|\Psi(X)\|_1 \le \|\Psi\|_\diamond \, \|X\|_1,
$$

in the specific stabilized setting needed by the recursion.

### 5. Close the induction

Combining the recursive decomposition with the two bounds above yields

$$
\left\|\Theta \circ T^{\otimes (n+1)}\right\|_\diamond
\le
\left\|\Theta \circ T\right\|_\diamond\,
\left\|\Theta \circ T^{\otimes n}\right\|_\diamond,
$$

and the induction hypothesis gives the claimed power bound.

## Interpretation

This theorem is the reason the final coding corollary can now be stated for the concrete
recursive tensor-power channel with no extra “middle-channel `diamondOp` bound” hypothesis.
