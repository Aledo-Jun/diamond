# theorem_eq7

## Source

- Lean file: `Diamond/EndMatter/Eq7.lean`
- Declaration: `Diamond.EndMatter.Eq7.theorem_eq7`

## Statement

For \(d \ge 2\),

$$
2 \cot\!\left(\frac{\pi}{2d}\right)
\le
\|\Lambda_d\|_\diamond.
$$

## What Theorem Eq. (7) Does

This theorem gives an explicit lower bound on the diamond norm of the paper's special channel
\(\Lambda_d\). Unlike the abstract upper bounds from the main theorem, this is a concrete witness
computation.

## Proof Structure

The proof is constructive.

### 1. Choose the maximally entangled witness

The file defines the vector

$$
\Omega_d = \frac{1}{\sqrt{d}} \sum_{j=1}^d e_j \otimes e_j
$$

and its rank-one state

$$
\Phi_d = |\Omega_d\rangle\langle\Omega_d|.
$$

This state is then used as the explicit diamond-norm witness.

### 2. Compute \((\Lambda_d \otimes \mathrm{id})(\Phi_d)\)

The witness matrix is expanded exactly in terms of the swap operator and the phase unitary
\(U_d\). In the code, this is the sequence of lemmas around:

- `transpose_phiState_eq_swap`,
- `transpose_ad_phiState_eq_swap_mul_phase`,
- `lambda_phiState_eq`.

The outcome is an explicit matrix formula for the image of \(\Phi_d\).

### 3. Reduce the trace norm to a one-dimensional phase sum

Using the fact that the swap operator is unitary and the witness becomes diagonal after the right
conjugation, the trace norm collapses to

$$
\sum_{k=0}^{d-1} \|1 - U_d(k,k)\|.
$$

This is the hard algebraic simplification step in the file.

### 4. Evaluate the trigonometric sum

Each phase term is rewritten as a sine:

$$
\|1 - U_d(k,k)\|
=
2 \sin\!\left(\frac{\pi k}{d}\right),
$$

and then the finite sine sum is evaluated as

$$
\sum_{k=0}^{d-1} 2 \sin\!\left(\frac{\pi k}{d}\right)
=
2 \cot\!\left(\frac{\pi}{2d}\right).
$$

### 5. Turn the witness value into a diamond-norm lower bound

Since \(\Phi_d\) is a valid density-state witness,

$$
\|(\Lambda_d \otimes \mathrm{id})(\Phi_d)\|_1
\le
\|\Lambda_d\|_\diamond.
$$

Combining the explicit trace-norm computation with this witness bound proves Eq. (7).

## Why This Theorem Matters

Eq. (7) provides the lower-bound side of the paper's constant comparison. Together with Eq. (8)
and Theorem 1, it yields the universal lower bound

$$
\frac{2}{\pi} \le \alpha
$$

for any dimension-independent constant \(\alpha\) in the main transposition inequality.
