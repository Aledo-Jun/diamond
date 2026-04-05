# EndMatter Overview

## Purpose

The `EndMatter/` folder contains the explicit consequences discussed at the end of the paper:

- the lower bound in Eq. (7),
- the unitary-channel identity in Eq. (8),
- the lower bound on any universal constant,
- and the finite-error coding corollary.

## Eq. (7): Explicit Lower Bound

The file `Eq7.lean` constructs a concrete witness for the map \(\Lambda_d\) and proves

$$
2 \cot\!\left(\frac{\pi}{2d}\right) \le \|\Lambda_d\|_\diamond.
$$

The proof is explicit: it writes down the maximally entangled state, evaluates the image under
\(\Lambda_d \otimes \mathrm{id}\), diagonalizes the resulting matrix through the swap operator,
and sums the resulting phases.

## Eq. (8): Exact Unitary Distance

The file `Eq8.lean` proves

$$
\|\mathrm{id} - \mathrm{Ad}_{U_d}\|_\diamond = 2.
$$

This gives the exact error term needed to compare the upper and lower bounds.

## Lower Bound on the Universal Constant

Combining Theorem 1 with Eq. (7) and Eq. (8) yields

$$
\frac{2}{\pi} \le \frac{1}{\sqrt{2}}.
$$

More conceptually, it shows that no dimension-independent constant below \(2/\pi\) can hold
uniformly in the main theorem.

## Corollary 2

The repository now formalizes the paper's finite-error coding consequence using the recursive
tensor-power channel. The canonical theorem is

`Diamond.EndMatter.Corollary2.paper_corollary2`.

Its mathematical content is:

if a coding scheme using \(m\) uses of \(T\) transmits a message space of dimension \(d\) with
error

$$
\varepsilon
=
\frac12
\left\|
\mathrm{id}
- \mathcal{D}\circ T^{\otimes m}\circ \mathcal{E}
\right\|_\diamond
<
\frac{1}{\sqrt{2}},
$$

then

$$
\frac{\log_2 d}{m}
\le
\log_2 \|\Theta \circ T\|_\diamond
+
\frac{1}{m}
\log_2\!\left(\frac{1}{1-\sqrt{2}\varepsilon}\right).
$$

## Why This Folder Matters

The earlier files prove structural inequalities. `EndMatter/` turns those inequalities into
numerical statements, asymptotic consequences, and the coding theorem that motivates the whole
paper.
