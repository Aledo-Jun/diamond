---
layout: default
---

# paper_holevo_werner_improved_converse_of_recursive_tensorPower

## Source

- Lean file: `Diamond/HolevoWerner/Theorem.lean`
- Declaration:
  `Diamond.HolevoWerner.Theorem.paper_holevo_werner_improved_converse_of_recursive_tensorPower`

## Statement

Let a coding scheme use $m$ copies of a channel $T$, with encoder $\mathcal E$ and decoder
$\mathcal D$, and define the decoding error by

$$
\varepsilon
=
\frac12
\left\|
\mathrm{id}
- \mathcal D \circ T^{\otimes m} \circ \mathcal E
\right\|_\diamond
<
\frac{1}{\sqrt 2}.
$$

Then the improved finite-error Holevo--Werner converse gives

$$
\frac{\log_2 d}{m}
\le
\log_2 \|\Theta \circ T\|_\diamond
+
\frac{1}{m}
\log_2\!\left(\frac{1}{1-\sqrt{2}\varepsilon}\right),
$$

where $d$ is the message dimension.

## What Is New Here

This theorem is the coding-level statement after the recursive tensor-power channel has been
fully internalized.

The proof no longer assumes an external estimate on the transposed $m$-use middle channel.
That estimate is now supplied internally by

$$
\left\|\Theta \circ T^{\otimes m}\right\|_\diamond
\le
\left\|\Theta \circ T\right\|_\diamond^m.
$$

## Proof Chain

The theorem is the end of the following chain:

$$
\text{Theorem 1}
\Longrightarrow
\text{Remark 1}
\Longrightarrow
\text{replacement argument}
\Longrightarrow
\text{improved Holevo--Werner converse}
\Longrightarrow
\text{recursive tensor-power specialization}.
$$

More concretely:

1. `Remark 1` gives the improved error-term estimate with the constant $1/\sqrt{2}$.
2. The replacement argument inserts that estimate into the original Holevo--Werner proof.
3. The recursive tensor-power theorem proves the needed middle-channel bound internally.
4. The result is then specialized to the concrete recursive channel `tensorPowerChannel T m`.

## Why This Theorem Matters

This is the theorem-level version of the paper's finite-error coding consequence before it is
presented as the final endmatter corollary. It is the cleanest place in the repository to see
how the norm inequality is converted into a coding bound.
