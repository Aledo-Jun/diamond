---
layout: default
---

# Setups Overview

## Purpose

`Setups.lean` fixes the mathematical language used everywhere else in the repository. It says
what a channel is, what norm is being used, how ancillas are attached, and what the transposition
map means formally.

## Core Objects

The ambient finite-dimensional operator space is

$$
L(\mathbb{C}^d),
$$

represented in Lean by complex square matrices indexed by a finite type `d`.

The basic objects are:

- `Operator d`:
  a complex \(d \times d\) matrix.
- `Channel d`:
  a complex-linear map
  $$
  L(\mathbb{C}^d) \to L(\mathbb{C}^d).
  $$
- `DensityState d`:
  a positive semidefinite matrix of trace \(1\).

## Norms

Two matrix norms are fixed at the outset.

The Hilbert--Schmidt norm is

$$
\|X\|_2.
$$

The trace norm is

$$
\|X\|_1,
$$

implemented concretely as the sum of singular values.

## Tensor-Stabilized Maps

The key operation is ancilla extension:

$$
\Phi \mapsto \Phi \otimes \mathrm{id}_k.
$$

In Lean this is the map `tensorWithIdentity d k Φ`. It applies \(\Phi\) to the left tensor
factor and leaves the right factor untouched.

The left partial transpose is also defined:

$$
\Theta \otimes \mathrm{id}_k.
$$

This is the operator called `partialTransposeMap`.

## Diamond Norm Convention

The repository uses the paper's finite-dimensional convention

$$
\|\Phi\|_\diamond
:=
\sup_{\rho \in \mathcal{D}(d \otimes d)}
\|(\Phi \otimes \mathrm{id}_d)(\rho)\|_1.
$$

This is why `diamondNorm` and `diamondOp` are the same public object in the code.

The more general fixed-ancilla quantity

$$
\|\Phi\|_{\diamond,k}
:=
\sup_{\rho \in \mathcal{D}(d \otimes k)}
\|(\Phi \otimes \mathrm{id}_k)(\rho)\|_1
$$

is also present as `diamondNormAt`.

## Special Maps

The file also defines:

- `transposeMap`: the ordinary matrix transpose \(\Theta\),
- `idMinus Φ`: the difference \(\mathrm{id} - \Phi\),
- `adMap U`: conjugation by a unitary \(U\),
- `Ud` and `Lambda`: the explicit end-matter maps used in Eq. (7) and Eq. (8).

## Why This File Matters

Every later theorem uses this vocabulary. If you want to understand what the later Lean files are
proving, this is the file that tells you what the symbols mean mathematically. The later modules
do not redefine these objects; they only prove properties about them.
