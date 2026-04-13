---
layout: default
---

# corollary2_linear_bound

## Source

- Lean file: `Diamond/EndMatter/Corollary2.lean`
- Declaration: `Diamond.EndMatter.Corollary2.corollary2_linear_bound`

## Statement

This is the linear form behind the logarithmic coding inequality. It states that the improved
Holevo--Werner argument yields

$$
(1-\sqrt{2}\,\varepsilon)\, d
\le
\|\Theta \circ T\|_\diamond^m,
$$

where \(d\) is the message dimension.

## Why The Linear Form Matters

The logarithmic corollary

$$
\frac{\log_2 d}{m}
\le
\log_2 \|\Theta \circ T\|_\diamond
+
\frac{1}{m}\log_2\!\left(\frac{1}{1-\sqrt{2}\varepsilon}\right)
$$

is obtained from this linear inequality by elementary logarithmic manipulation.

So the linear theorem is the real quantitative core; the logarithmic statement is its
presentation-friendly form.

## Role In The Proof Chain

The argument runs as follows:

1. prove the improved error-term estimate using `Remark 1`,
2. insert that estimate into the replacement argument,
3. obtain the linear inequality above,
4. pass to the logarithmic form.

The repository keeps both forms because they serve different purposes:

- the linear form is better for norm estimates and algebraic manipulation,
- the logarithmic form matches the standard coding-rate statement in the paper.

## Reader Guidance

If you care about the final paper statement, read:

- [`paper_corollary2.md`](paper_corollary2/)

If you care about the quantitative estimate that actually drives the proof, this page is the
right stopping point.
