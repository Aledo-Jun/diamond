---
layout: default
---

# paper_corollary2

## Source

- Lean file: `Diamond/EndMatter/Corollary2.lean`
- Declaration: `Diamond.EndMatter.Corollary2.paper_corollary2`

## Statement

Suppose a coding scheme uses $m$ copies of a channel $T$ to transmit a message space of
dimension $d$, and define the decoding error by

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

Then

$$
\frac{\log_2 d}{m}
\le
\log_2 \|\Theta \circ T\|_\diamond
+
\frac{1}{m}
\log_2\!\left(\frac{1}{1-\sqrt{2}\varepsilon}\right).
$$

This is the canonical paper-facing Corollary 2 theorem in the repository.

## How It Relates To The Paper

The paper writes the middle channel as $T^{\otimes m}$. In the Lean development, that object
is formalized concretely as the recursive channel `tensorPowerChannel T m`.

So the theorem is not merely a wrapper around an abstract placeholder. It is already specialized
to the actual repeated-use channel object used by the code.

## Proof Structure

The endmatter proof is intentionally thin.

### 1. Holevo--Werner layer

The heavy coding argument lives in `HolevoWerner/Theorem.lean`, where the original
Holevo--Werner converse and the replacement argument are formalized explicitly.

### 2. Recursive tensor-power bound

The formerly missing middle-channel estimate is now internal:

$$
\left\|\Theta \circ T^{\otimes m}\right\|_\diamond
\le
\left\|\Theta \circ T\right\|_\diamond^m.
$$

This is the theorem
`Diamond.HolevoWerner.Theorem.diamondOp_transpose_tensorPowerChannel_le_pow`.

### 3. Final specialization

`paper_corollary2` simply packages the improved Holevo--Werner theorem for the concrete
recursive tensor-power channel and presents the result in the exact logarithmic form that
appears in the paper.

## Why This Page Is The Right Entry Point

If you want the final coding statement and not the proof scaffolding, this is the page to read.

If you want the proof behind it, the next pages to open are:

1. [`../../HolevoWerner/Theorem/paper_holevo_werner_improved_converse_of_recursive_tensorPower.md`](../../HolevoWerner/Theorem/paper_holevo_werner_improved_converse_of_recursive_tensorPower/)
2. [`../../HolevoWerner/Theorem/diamondOp_transpose_tensorPowerChannel_le_pow.md`](../../HolevoWerner/Theorem/diamondOp_transpose_tensorPowerChannel_le_pow/)
3. [`../../Theorem/Theorem1/theorem1.md`](../../Theorem/Theorem1/theorem1/)
