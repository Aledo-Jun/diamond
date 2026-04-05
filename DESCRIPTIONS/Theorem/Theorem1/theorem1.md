# theorem1

## Source

- Lean file: `Diamond/Theorem/Theorem1.lean`
- Declaration: `Diamond.Theorem.Theorem1.theorem1`

## Statement

For a quantum channel \(T\),

$$
\left\|\Theta \circ (\mathrm{id}-T)\right\|_\diamond
\le
\frac{1}{\sqrt{2}}\,
\|\Theta\|_\diamond\,
\|\mathrm{id}-T\|_\diamond.
$$

This is the main theorem of the repository.

## What Theorem 1 Says

The transpose map is not merely bounded under diamond-norm composition with a channel
difference. It loses a universal factor of \(1/\sqrt{2}\). That is stronger than the naive
submultiplicative estimate

$$
\|\Theta \circ \Phi\|_\diamond \le \|\Theta\|_\diamond \|\Phi\|_\diamond.
$$

The theorem applies to \(\Phi = \mathrm{id} - T\), which is the form needed both for the main
paper and for the later coding application.

## Proof Structure

The Lean proof is best read in five conceptual blocks.

### 1. Reduce the diamond norm to a fixed ancilla witness

The proof starts with an arbitrary density-state witness

$$
\rho \in \mathcal{D}(d \otimes d).
$$

By the definition of the repository's `diamondOp`, it is enough to bound

$$
\left\|((\Theta \circ (\mathrm{id}-T)) \otimes \mathrm{id})(\rho)\right\|_1.
$$

### 2. Introduce the middle matrix

Set

$$
M_\rho := ((\mathrm{id}-T)\otimes \mathrm{id})(\rho).
$$

The map \(\Theta\) is then moved past ancilla extension using the standard identity

$$
((\Theta \circ \Phi)\otimes \mathrm{id})(\rho)
=
\Gamma\!\left((\Phi\otimes\mathrm{id})(\rho)\right),
$$

where \(\Gamma\) is the partial transpose on the larger bipartite space.

So the target becomes \(\|\Gamma(M_\rho)\|_1\).

### 3. Record the structural properties of \(M_\rho\)

Because \(T\) is a quantum channel, the difference \(\mathrm{id}-T\) is:

- Hermiticity-preserving,
- trace-annihilating.

Therefore \(M_\rho\) is Hermitian and traceless. These are exactly the hypotheses needed for
Lemma 1.

### 4. Chain the three norm lemmas

The core estimate is

$$
\|\Gamma(M_\rho)\|_1
\le
\sqrt{d^2}\,\|\Gamma(M_\rho)\|_2
=
\sqrt{d^2}\,\|M_\rho\|_2
\le
\sqrt{d^2}\,\frac{1}{\sqrt{2}}\|M_\rho\|_1.
$$

Here:

- Lemma 2 gives \(\|\Gamma(M_\rho)\|_1 \le \sqrt{d^2}\,\|\Gamma(M_\rho)\|_2\),
- Lemma 3 gives \(\|\Gamma(M_\rho)\|_2 = \|M_\rho\|_2\),
- Lemma 1 gives \(\|M_\rho\|_2 \le \frac{1}{\sqrt{2}}\|M_\rho\|_1\).

### 5. Convert the witness norm back to a diamond norm

Finally,

$$
\|M_\rho\|_1
\le
\|\mathrm{id}-T\|_\diamond.
$$

The remaining factor \(\sqrt{d^2}\) is identified with \(\|\Theta\|_\diamond\) using the exact
transpose-norm formula proved earlier in the project.

That gives precisely

$$
\left\|((\Theta \circ (\mathrm{id}-T))\otimes\mathrm{id})(\rho)\right\|_1
\le
\frac{1}{\sqrt{2}}\,
\|\Theta\|_\diamond\,
\|\mathrm{id}-T\|_\diamond,
$$

and taking the supremum over \(\rho\) finishes the proof.

## Why This Theorem Matters

This is the single estimate from which the rest of the paper flows:

- `Remark 1` extends it to arbitrary Hermiticity-preserving, trace-annihilating maps.
- `PositiveGap/` proves the bound is strict in finite dimension for nonzero channel differences.
- `HolevoWerner/` plugs the same constant into the finite-error coding argument.
