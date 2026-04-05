# theorem_eq8

## Source

- Lean file: `Diamond/EndMatter/Eq8.lean`
- Declaration: `Diamond.EndMatter.Eq8.theorem_eq8`

## Statement

For the phase unitary \(U_d\),

$$
\|\mathrm{id} - \mathrm{Ad}_{U_d}\|_\diamond = 2.
$$

## Meaning

The channel \(\mathrm{Ad}_{U_d}\) is unitary conjugation by \(U_d\). This theorem says that its
diamond distance from the identity channel is exactly maximal in the scale relevant to the paper.

## Proof Structure

The proof is short because the heavy lifting already lives in `StandardFacts.lean`.

### 1. Identify the channel

The channel in question is

$$
\mathrm{Ad}_{U_d}(X) = U_d X U_d^\dagger.
$$

The object compared to the identity is therefore

$$
\mathrm{id} - \mathrm{Ad}_{U_d}.
$$

### 2. Verify the unitary hypotheses

The project already proves:

- \(U_d^\dagger U_d = I\),
- \(\operatorname{tr}(U_d) = 0\).

These are exactly the assumptions needed by the general unitary-channel distance formula proved
earlier in the repository.

### 3. Apply the general formula

The final step is an application of the background theorem stating that if \(U\) is unitary and
\(\operatorname{tr}(U)=0\), then

$$
\|\mathrm{id} - \mathrm{Ad}_U\|_\diamond = 2.
$$

Substituting \(U = U_d\) gives the result immediately.

## Why This Theorem Matters

Eq. (8) supplies the exact value needed to compare the upper and lower bounds in the endmatter.
Together with Eq. (7), it turns the abstract norm inequality into a quantitative constraint on
the universal constant.
