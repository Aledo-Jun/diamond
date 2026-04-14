---
layout: default
---

# Holevo--Werner Overview

## Purpose

The `HolevoWerner/` folder formalizes the coding-theoretic consequence of the transposition
bound. It separates the original finite-error Holevo--Werner argument from the replacement step
that inserts Theorem 1 / Remark 1.

## The Logical Structure

The paper's proof is now represented explicitly as

$$
\text{original Holevo--Werner converse}
\Longrightarrow
\text{replacement argument}
\Longrightarrow
\text{improved finite-error converse}.
$$

That separation matters because it isolates exactly where the old
$\varepsilon < \tfrac12$ threshold came from and how Theorem 1 replaces it by
$\varepsilon < \tfrac{1}{\sqrt{2}}$.

## Main Layers

### 1. Coding objects

The folder defines:

- rectangular superoperators for encoders and decoders,
- `QuantumCodingScheme`,
- the effective message-space channel
  $$
  \mathcal{D} \circ T^{\otimes m} \circ \mathcal{E}.
  $$

### 2. Original converse

The original Holevo--Werner proof uses a transpose bound on the effective channel and a
submultiplicative estimate for the error term.

### 3. Replacement argument

This is the key abstraction:

if one can improve the error-term estimate

$$
\|\Theta \circ \Psi\|_\diamond \le \alpha \|\Theta\|_\diamond \|\Psi\|_\diamond,
$$

then the same coding proof yields a correspondingly improved finite-error converse.

### 4. Improved converse

Applying Remark 1 with $\alpha = 1/\sqrt{2}$ gives the improved finite-error threshold.

## Tensor-Power Channel

The folder now also contains a concrete recursive formalization of
$T^{\otimes m}$:

$$
T^{\otimes 0} = \mathrm{id},
\qquad
T^{\otimes (n+1)} = (\mathrm{id} \otimes T)\circ (T^{\otimes n} \otimes \mathrm{id}).
$$

In Lean this is the object `tensorPowerChannel T m` on the recursive block space
`TensorPowerType phys m`.

The key new estimate is

$$
\left\|\Theta \circ T^{\otimes m}\right\|_\diamond
\le
\left\|\Theta \circ T\right\|_\diamond^m,
$$

proved internally for the concrete recursive channel rather than assumed as an external input.

## Why This Folder Matters

This is the bridge between the norm inequality and the coding corollary. Without this layer, the
paper's endmatter would remain a prose argument. With it, the repository contains an explicit,
checkable proof path all the way from Theorem 1 to the coding bound.
