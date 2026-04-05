# StandardFacts Overview

## Purpose

`StandardFacts.lean` is the background engine of the project. It does not state the main theorem,
but it proves the reductions that make the main theorem and the end-matter arguments readable.

## Main Themes

### 1. Pointwise-to-diamond reductions

Many arguments in the repository are proved by first showing a bound for every density-state
witness and then passing to the supremum. The file packages this pattern in lemmas of the form

$$
\bigl(\forall \rho,\ \|(\Phi \otimes \mathrm{id})(\rho)\|_1 \le b\bigr)
\Longrightarrow
\|\Phi\|_\diamond \le b.
$$

### 2. Hermiticity and trace structure

The project repeatedly uses the fact that physically natural maps preserve Hermiticity or kill
the trace. `StandardFacts.lean` proves those facts for:

- quantum channels,
- `idMinus T`,
- ancilla extensions,
- and transpose-composed maps.

These properties are what allow Lemma 1 and Remark 1 to be applied.

### 3. Contractivity and norm control

The file proves the trace-norm contractivity statements used throughout the coding section:

$$
\|T(X)\|_1 \le \|X\|_1
\quad\text{for Hermitian }X
$$

when \(T\) is a quantum channel, together with the corresponding density-state and diamond-norm
versions.

### 4. Transpose decomposition machinery

One recurring identity is that ancilla extension commutes with left transpose in the form

$$
(\Theta \circ \Phi)\otimes \mathrm{id}

=
\Gamma \circ (\Phi \otimes \mathrm{id}),
$$

where \(\Gamma\) is the partial transpose on the larger space. This is the bridge between the
main theorem and concrete witness computations.

### 5. Witness attainment and spectral decompositions

The file also formalizes finite-dimensional compactness/spectral arguments:

- existence of maximizing density states,
- decomposition of density matrices into pure eigenprojectors,
- reduction from mixed-state bounds to pure-state bounds,
- and trace-norm formulas for Hermitian or positive semidefinite matrices.

### 6. Ancilla compression and expansion

The modern Corollary 2 proof path depends heavily on the fact that pure witnesses can be moved
between ancilla dimensions by isometries. This appears in the file as pure-state compression and
expansion theorems of the form

$$
\psi \in \mathbb{C}^{d \otimes k}
\rightsquigarrow
\phi \in \mathbb{C}^{d \otimes d},
$$

with exact control of the resulting rank-one state after an isometric embedding.

## Why This File Matters

If `Setups.lean` gives the dictionary, then `StandardFacts.lean` gives the reusable grammar.
Theorem 1, the strictness theorem, Eq. (7), Eq. (8), and the Holevo--Werner/Corollary 2 layer
all depend on these reductions.
