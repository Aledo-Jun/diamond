---
layout: default
---

# corollary2

## Source

- Lean file: `Diamond/EndMatter/Corollary2.lean`
- Declaration: `Diamond.EndMatter.Corollary2.corollary2`

## What This Declaration Is

This is the older abstract endmatter wrapper: it states Corollary 2 directly in terms of an
encoder, a decoder, an abstract middle channel `tensorPower`, and the corresponding effective
channel.

In mathematical form, it says:

if

$$
\varepsilon
=
\frac12
\left\|
\mathrm{id}
- \mathcal D \circ \text{tensorPower} \circ \mathcal E
\right\|_\diamond
<
\frac{1}{\sqrt 2},
$$

and if the required transposed effective-channel bound is available, then the improved
Holevo--Werner finite-error converse follows.

## Why It Is No Longer The Canonical Endpoint

This theorem is still correct, but it is no longer the best reader-facing theorem in the
repository, because it treats the $m$-use middle channel abstractly.

The canonical page to read now is:

- [`paper_corollary2.md`](paper_corollary2/)

That newer theorem specializes the argument to the concrete recursive tensor-power object
`tensorPowerChannel T m` and uses the middle-channel `diamondOp` estimate proved internally in
the project.

## Role In The Codebase

Even though it is no longer the canonical paper-facing theorem, this declaration still plays a
useful organizational role:

- it presents the endmatter result at the level of an abstract effective channel,
- it keeps the proof surface compatible with earlier stages of the development,
- and it serves as the bridge between the general Holevo--Werner layer and the fully concrete
  recursive tensor-power specialization.
