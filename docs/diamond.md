# A dimension-independent strict submultiplicativity for the transposition map in diamond norm 

Hyunho Cha* and Jungwoo Lee ${ }^{\dagger}$<br>NextQuantum and Department of Electrical and Computer Engineering, Seoul National University, Seoul 08826, Republic of Korea

(Dated: March 5, 2026)


#### Abstract

The transpose map is the canonical nonphysical map in quantum information that is central to entanglement tests and to the converse for quantum capacity. It has been open whether transposition can satisfy a dimension-independent strict submultiplicativity bound when restricted to physically relevant channel differences. We answer this affirmatively by proving that for every quantum channel $T$ on $\mathrm{L}\left(\mathbb{C}^{d}\right),\|\Theta \circ(\operatorname{id}-T)\| \diamond \leq \frac{1}{\sqrt{2}}\|\Theta\|_{\diamond}\|\mathrm{id}-T\|_{\diamond}$. The same bound holds for all Hermiticity-preserving trace-annihilating maps. Thus, although transposition is extremal in the unrestricted diamondnorm geometry, physical constraints force a universal slack in the submultiplicative bound. As an immediate consequence, the finite-error Holevo-Werner converse extends from decoding errors $\varepsilon<1 / 2$ to $\varepsilon<1 / \sqrt{2}$. This sharpens a basic analytical converse result for quantum communication.


Introduction-Quantum capacity is one of the most subtle basic quantities in quantum information theory. Even its coding theorem is intrinsically regularized 1 3, additivity fails in dramatic ways [2-4], and superactivation shows that two zero-capacity channels can combine to transmit quantum information [5, 6]. These features make simple, computable converse bounds especially valuable, particularly when one wants statements that remain meaningful at nonzero decoding error rather than only in the asymptotic vanishing-error limit [1-5].

Among the mathematical objects that enter such converse bounds, the transpose map holds a unique importance. It is the canonical example of a positive map that is not completely positive, it lies behind the PeresHorodecki separability criterion, and it underpins entanglement measures such as the negativity [7-10]. At the same time, the diamond norm provides the natural stabilized notion of distance for quantum channels and linear maps acting on quantum states [11. The transpose map is extremal in this geometry because its diamond norm grows linearly with dimension, reflecting its maximal deviation from the behavior of completely positive maps 12. This makes the transpose map both mathematically rigid and operationally significant, and helps explain why it repeatedly appears at the interface of entanglement theory, operator theory, and quantum Shannon theory [6-11].

A particularly elegant example is the transpositionbased upper bound on quantum capacity introduced by Holevo and Werner. That bound remains valid in the presence of finite decoding error and has the virtue of being explicit and conceptually transparent. Since then, stronger converse bounds have been developed through semidefinite programming 13, 14, PPT-assisted methods 13, 15, 16, and Rains-type quantities [17, 18. Nevertheless, the Holevo-Werner transposition bound retains

[^0]a special status: it is arguably the cleanest converse in which a genuinely non-completely-positive map enters in an essential way, and it therefore provides a testing ground for understanding what transposition really contributes to quantum coding limits.

In this Letter, we revisit the precise step at which the usual transposition argument loses sharpness. Standard proofs rely on the generic submultiplicativity of the diamond norm, applied to the composition of transposition with the deviation of a channel from the identity. However, that deviation is far from arbitrary. If $T$ is a quantum channel, then the map id $-T$ is automatically Hermiticity preserving and trace-annihilating. After adjoining an ancilla, it therefore sends every bipartite state to a traceless Hermitian operator. This extra structure is invisible to the usual worst-case norm inequality. It has thus raised a natural open question: when the perturbation is restricted to the form id $-T$ for a quantum channel $T$, is the impact of transposition strictly smaller than the general diamond norm bound would predict?

We answer this question in the affirmative. Our main theorem establishes a dimension-independent strict submultiplicativity statement for the transposition map on channel differences. The argument isolates a structural fact in that while transposition is maximally large in diamond norm in the unrestricted worst case, it is uniformly better behaved on trace-annihilating Hermiticitypreserving perturbations.

The result is more than a numerical improvement inside a known converse proof. It identifies a new rigidity property of the transpose map in stabilized norm geometry. The theorem also extends immediately beyond channel differences to arbitrary Hermiticity-preserving, trace-annihilating linear maps, which suggests that the phenomenon is not accidental and may reflect a broader principle about how nonphysical maps interact with perturbations that arise from physical constraints. At the same time, we show that the universal constant is not yet fully understood, framing our result as both a definitive contribution and the basis for a well-posed open problem.

The information-theoretic payoff is immediate. In the finite-error Holevo-Werner converse, the familiar restriction to errors below $1 / 2$ enters exactly through the generic submultiplicativity property. Replacing that step by the strict bound proved here enlarges the admissible error regime to below $1 / \sqrt{2}$ in the diamond-error convention $\frac{1}{2}\|\Phi-\Psi\|_{\diamond}$.

Setup and definitions-Let $\mathcal{H} \cong \mathbb{C}^{d}$ be a $d$-dimensional Hilbert space. We write $\mathrm{L}(\mathcal{H})$ for the space of linear operators on $\mathcal{H}$, and

$$
\mathrm{D}(\mathcal{H})=\{\rho \in \mathrm{L}(\mathcal{H}): \rho \succeq 0, \operatorname{tr}(\rho)=1\}
$$

for the set of density operators.
a. Transposition map. Fix an orthonormal basis $\{|1\rangle, \ldots,|d\rangle\}$ of $\mathcal{H}$. The transposition map $\Theta: \mathrm{L}(\mathcal{H}) \rightarrow \mathrm{L}(\mathcal{H})$ is defined by

$$
\Theta(X)=X^{\top}
$$

which depends on the chosen basis.
b. Quantum channels. A quantum channel $T$ : $\mathrm{L}(\mathcal{H}) \rightarrow \mathrm{L}(\mathcal{H})$ is a completely positive trace-preserving (CPTP) linear map.
c. Norms. The trace norm and Hilbert-Schmidt norm of an operator $X$ are

$$
\|X\|_{1}=\operatorname{tr} \sqrt{X^{\dagger} X}, \quad\|X\|_{2}=\sqrt{\operatorname{tr}\left(X^{\dagger} X\right)}
$$

The diamond norm of a linear map $\Phi: \mathrm{L}(\mathcal{H}) \rightarrow \mathrm{L}(\mathcal{H})$ is

$$
\|\Phi\|_{\diamond}:=\sup _{k \geq 1} \sup _{\rho \in \mathrm{D}\left(\mathcal{H} \otimes \mathbb{C}^{k}\right)}\left\|\left(\Phi \otimes \mathrm{id}_{k}\right)(\rho)\right\|_{1} .
$$

It is standard that for maps acting on $\mathrm{L}\left(\mathbb{C}^{d}\right)$, the supremum over $k$ can be restricted to $k=d$. We will use this without further comment and write id for $\mathrm{id}_{d}$ throughout the paper.

The main result of this work is given by the following theorem.

Theorem 1-Let $\mathcal{H} \cong \mathbb{C}^{d}$ and let $T: \mathrm{L}(\mathcal{H}) \rightarrow \mathrm{L}(\mathcal{H})$ be a quantum channel. Then

$$
\begin{equation*}
\|\Theta \circ(\operatorname{id}-T)\|_{\diamond} \leq \alpha\|\Theta\|_{\diamond}\|\operatorname{id}-T\|_{\diamond} \tag{1}
\end{equation*}
$$

with $\alpha=1 / \sqrt{2}$. In particular, since $\|\Theta\|_{\diamond}=d$ [19],

$$
\|\Theta \circ(\mathrm{id}-T)\|_{\diamond} \leq \frac{d}{\sqrt{2}}\|\mathrm{id}-T\|_{\diamond}
$$

The proof proceeds by reducing to a matrix inequality for the partial transpose applied to traceless Hermitian matrices. The specific form $\Theta \circ(\mathrm{id}-T)$ appears in 20, but the analysis therein relied on the standard diamondnorm submultiplicativity corresponding to the case $\alpha=$ 1. The possibility of obtaining a dimension-independent constant $\alpha<1$ for a stronger submultiplicativity result remained open.

We first present a few useful lemmas.

Lemma 1-If $X=X^{\dagger}$ and $\operatorname{tr}(X)=0$, then

$$
\|X\|_{2} \leq \frac{1}{\sqrt{2}}\|X\|_{1}
$$

Proof. Let $\left\{\lambda_{i}\right\}_{i=1}^{n}$ be the eigenvalues of $X$ (real because $X$ is Hermitian). Write the positive eigenvalues as $p_{1}, \ldots, p_{r} \geq 0$ and the negative eigenvalues as $-q_{1}, \ldots,-q_{s}$ with $q_{1}, \ldots, q_{s}>0$. Since $\operatorname{tr}(X)=\sum_{i} \lambda_{i}=$ 0 , we have

$$
\sum_{i=1}^{r} p_{i}=\sum_{j=1}^{s} q_{j}=: t
$$

Hence

$$
\|X\|_{1}=\sum_{i}\left|\lambda_{i}\right|=\sum_{i=1}^{r} p_{i}+\sum_{j=1}^{s} q_{j}=2 t
$$

Also,

$$
\begin{align*}
\|X\|_{2}^{2} & =\sum_{i} \lambda_{i}^{2}=\sum_{i=1}^{r} p_{i}^{2}+\sum_{j=1}^{s} q_{j}^{2} \\
& \leq\left(\sum_{i=1}^{r} p_{i}\right)^{2}+\left(\sum_{j=1}^{s} q_{j}\right)^{2}=t^{2}+t^{2}=2 t^{2} \tag{2}
\end{align*}
$$

where we used the elementary inequality $\sum a_{i}^{2} \leq\left(\sum a_{i}\right)^{2}$ for nonnegative $a_{i}$. Therefore $\|X\|_{2} \leq \sqrt{2} t=\|X\|_{1} / \sqrt{2}$.

Lemma 2-Let $Y$ be an operator on an $N$-dimensional Hilbert space. Then

$$
\|Y\|_{1} \leq \sqrt{N}\|Y\|_{2}
$$

Proof. Let $s_{1}, \ldots, s_{N}$ be the singular values of $Y$ (padding with zeros if necessary). Then $\|Y\|_{1}=\sum_{i} s_{i}$ and $\|Y\|_{2}=\sqrt{\sum_{i} s_{i}^{2}}$. By Cauchy-Schwarz,

$$
\begin{equation*}
\left(\sum_{i=1}^{N} s_{i}\right)^{2} \leq N \sum_{i=1}^{N} s_{i}^{2} \tag{3}
\end{equation*}
$$

which gives the claim.
Lemma 3-Let $\mathcal{H}, \mathcal{K}$ be finite-dimensional and let $\Theta$ denote transposition on $\mathcal{H}$. Then for all $X \in \mathrm{~L}(\mathcal{H} \otimes \mathcal{K})$,

$$
\|(\Theta \otimes \operatorname{id})(X)\|_{2}=\|X\|_{2} .
$$

Proof. In the computational basis on $\mathcal{H}$, the transposition map is an isometry for the Hilbert-Schmidt inner product:

$$
\langle A, B\rangle_{\mathrm{HS}}:=\operatorname{tr}\left(A^{\dagger} B\right), \quad \operatorname{tr}\left(\left(A^{\top}\right)^{\dagger} B^{\top}\right)=\operatorname{tr}\left(A^{\dagger} B\right)
$$

Applying this entrywise on $\mathcal{H}$ and trivially on $\mathcal{K}$ yields

$$
\operatorname{tr}\left(((\Theta \otimes \operatorname{id})(X))^{\dagger}(\Theta \otimes \operatorname{id})(X)\right)=\operatorname{tr}\left(X^{\dagger} X\right)
$$

i.e. $\|(\Theta \otimes \operatorname{id})(X)\|_{2}=\|X\|_{2}$.

We are now ready to prove Theorem 1.
Proof of Theorem 1. Fix an ancilla $\mathcal{K} \cong \mathbb{C}^{d}$. For any $\rho \in \mathrm{D}(\mathcal{H} \otimes \mathcal{K})$,

$$
\operatorname{tr}(((\mathrm{id}-T) \otimes \mathrm{id})(\rho))=\operatorname{tr}\left((\mathrm{id}-T)\left(\operatorname{tr}_{\mathcal{K}} \rho\right)\right)=0
$$

since id $-T$ is trace-annihilating. Therefore,

$$
\begin{aligned}
& \|(\Theta \circ(\mathrm{id}-T) \otimes \mathrm{id})(\rho)\|_{1} \\
& \leq(\text { Lemma 2 })\|(\Theta \circ(\mathrm{id}-T) \otimes \mathrm{id})(\rho)\|_{2} \\
& =(\text { Lemma 3 })\|((\mathrm{id}-T) \otimes \mathrm{id})(\rho)\|_{2} \\
& \leq(\text { Lemma 1 }) \frac{d}{\sqrt{2}}\|((\mathrm{id}-T) \otimes \mathrm{id})(\rho)\|_{1} \\
& \leq \frac{d}{\sqrt{2}}\|\mathrm{id}-T\|_{\diamond} \\
& =\frac{1}{\sqrt{2}}\|\Theta\|_{\diamond}\|\mathrm{id}-T\|_{\diamond}
\end{aligned}
$$

Taking the supremum over $\rho$,

$$
\|\Theta \circ(\mathrm{id}-T)\|_{\diamond} \leq \frac{1}{\sqrt{2}}\|\Theta\|_{\diamond}\|\mathrm{id}-T\|_{\diamond}
$$

Remark 1-The constant $1 / \sqrt{2}$ is universal (independent of $d$ and $T$ ) and arises from the fact that ((id $T) \otimes \mathrm{id})(\rho)$ is always traceless because $\mathrm{id}-T$ is traceannihilating. Moreover, Theorem 1 immediately generalizes by replacing id $-T$ with any linear map $\Psi: \mathrm{L}(\mathcal{H}) \rightarrow \mathrm{L}(\mathcal{H})$ that is Hermiticity-preserving and traceannihilating. In that case the same argument yields $\|\Theta \circ \Psi\|_{\diamond} \leq \frac{1}{\sqrt{2}}\|\Theta\|_{\diamond}\|\Psi\|_{\diamond}$.

Positive gap in finite dimension-Regrettably, the inequality in Theorem 1 is still not tight for any finite $d$, except in the trivial case $T=\mathrm{id}$, where both LHS and RHS become zero. Fix any nonzero channel difference $\Phi=\mathrm{id}-T \neq 0$ (equivalently $T \neq \mathrm{id}$ ). Rewrite the pointwise inequality (for every $\rho$ ):

$$
\begin{equation*}
\underbrace{\|(\Theta \circ \Phi \otimes \mathrm{id})(\rho)\|_{1}}_{=: L(\rho)} \leq \frac{d}{\sqrt{2}} \underbrace{\|(\Phi \otimes \mathrm{id})(\rho)\|_{1}}_{=: R(\rho)} . \tag{4}
\end{equation*}
$$

Taking suprema gives $\sup _{\rho} L(\rho) \leq \frac{d}{\sqrt{2}} \sup _{\rho} R(\rho)$. In finite dimension, the suprema are maxima, so equality

$$
\sup _{\rho} L(\rho)=\frac{d}{\sqrt{2}} \sup _{\rho} R(\rho)
$$

can only happen if there exists some $\rho_{\star}$ such that $R\left(\rho_{\star}\right)= \sup _{\rho} R(\rho)$ and the pointwise inequality Eq. (4) is tight at $\rho_{\star}$, i.e., $L\left(\rho_{\star}\right)=\frac{d}{\sqrt{2}} R\left(\rho_{\star}\right)$. Let $X_{\star}:=(\Phi \otimes \mathrm{id})\left(\rho_{\star}\right)$. Since $\Phi \neq 0$ and $\rho_{\star}$ maximizes $R$, we have $X_{\star} \neq 0$. Now, the chain of inequalities shows

$$
\left\|(\Theta \otimes \mathrm{id})\left(X_{\star}\right)\right\|_{1} \leq d\left\|X_{\star}\right\|_{2} \leq \frac{d}{\sqrt{2}}\left\|X_{\star}\right\|_{1}
$$

So equality in Theorem 1 forces equality in Lemmas 1 and 2 at some nonzero $X_{\star}$. But the equality conditions of Lemmas 1 and 2 are incompatible (unless $X=0$ ).
d. Equality condition for Lemma 1. For a nonzero traceless Hermitian $X$, equality in Lemma 1 holds iff $X$ has exactly two nonzero eigenvalues, $+t$ and $-t$. This follows from Eq. (2), where equality requires all cross terms to vanish. Equivalently,

$$
\begin{equation*}
\operatorname{rank}\left(X_{\star}\right)=2 \quad \text { (for nonzero equality cases). } \tag{5}
\end{equation*}
$$

e. Equality condition for Lemma 2. Equality in Lemma 2 holds iff $s$ in Eq. (3) is proportional to $(1, \ldots, 1)$, i.e., all singular values are equal. If $Y \neq 0$, that forces all $N$ singular values to be the same positive number, hence

$$
\begin{equation*}
\operatorname{rank}\left((\Theta \otimes \operatorname{id})\left(X_{\star}\right)\right)=\operatorname{rank}\left(Y_{\star}\right)=N=d^{2} \tag{6}
\end{equation*}
$$

To proceed, we need the following definitions and identities.

Definition 1 (Column-major vectorization)-For a matrix $A \in \mathbb{C}^{d \times d}$ with entries $A_{i j}=\langle i| A|j\rangle$, define

$$
|\operatorname{vec}(A)\rangle:=\sum_{i=1}^{d} \sum_{j=1}^{d} A_{i j}|i\rangle_{\mathcal{H}} \otimes|j\rangle_{\mathcal{K}}
$$

Definition 2-The swap operator $F \in \mathrm{~L}(\mathcal{H} \otimes \mathcal{K})$ is defined by:

$$
F(|i\rangle \otimes|j\rangle)=|j\rangle \otimes|i\rangle .
$$

Lemma 4-For any operator $Z \in \mathrm{~L}(\mathcal{H} \otimes \mathcal{K}), \operatorname{tr}_{\mathcal{H}}((T \otimes$ id) $(Z))=\operatorname{tr}_{\mathcal{H}}(Z)$.

Proof. We can write $Z$ as

$$
Z=\sum_{j} A_{j} \otimes B_{j}
$$

where $A_{j} \in \mathrm{~L}(\mathcal{H})$ and $B_{j} \in \mathrm{~L}(\mathcal{K})$. There exists a set of Kraus operators $\left\{E_{k}\right\}$ acting on $\mathcal{H}$ such that

$$
T(X)=\sum_{k} E_{k} X E_{k}^{\dagger}, \quad \sum_{k} E_{k}^{\dagger} E_{k}=\mathrm{id}
$$

By linearity we have
$(T \otimes \mathrm{id}) Z=\sum_{j} T\left(A_{j}\right) \otimes B_{j}=\sum_{j}\left(\sum_{k} E_{k} A_{j} E_{k}^{\dagger}\right) \otimes B_{j}$.

Now we take the partial $\operatorname{trace} \operatorname{tr}_{\mathcal{H}}$ :

$$
\begin{aligned}
\operatorname{tr}_{\mathcal{H}}((T \otimes \mathrm{id}) Z) & =\sum_{j} \operatorname{tr}_{\mathcal{H}}\left(\sum_{k} E_{k} A_{j} E_{k}^{\dagger} \otimes B_{j}\right) \\
& =\sum_{j}\left(\sum_{k} \operatorname{tr}\left(E_{k} A_{j} E_{k}^{\dagger}\right)\right) B_{j} \\
& =\sum_{j} \operatorname{tr}\left(\left(\sum_{k} E_{k}^{\dagger} E_{k}\right) A_{j}\right) B_{j} \\
& =\sum_{j} \operatorname{tr}\left(A_{j}\right) B_{j} .
\end{aligned}
$$

Meanwhile, by the definition of the partial trace on the original operator $Z=\sum_{j} A_{j} \otimes B_{j}$,

$$
\operatorname{tr}_{\mathcal{H}}(Z)=\sum_{j} \operatorname{tr}\left(A_{j}\right) B_{j} .
$$

Thus,

$$
\operatorname{tr}_{\mathcal{H}}((T \otimes \operatorname{id})(Z))=\operatorname{tr}_{\mathcal{H}}(Z) .
$$

Corollary 1- $\operatorname{tr}_{\mathcal{H}}((\Phi \otimes \mathrm{id})(\rho))=0$.
Proof. From Lemma 4 we have

$$
\begin{aligned}
\operatorname{tr}_{\mathcal{H}}((\Phi \otimes \operatorname{id})(\rho)) & =\operatorname{tr}_{\mathcal{H}}(\rho-(T \otimes \operatorname{id})(\rho)) \\
& =\operatorname{tr}_{\mathcal{H}}(\rho)-\operatorname{tr}_{\mathcal{H}}(\rho)=0 .
\end{aligned}
$$ $\square$

Lemma 5-For any $M \in \mathbb{C}^{d \times d}$ on $\mathcal{H}$ and $N \in \mathbb{C}^{d \times d}$ on $\mathcal{K}$,

$$
(M \otimes N)|\operatorname{vec}(A)\rangle=\left|\operatorname{vec}\left(M A N^{\top}\right)\right\rangle .
$$

Lemma 6-For any $X, Y \in \mathbb{C}^{d \times d}$,

$$
F(X \otimes Y)=(Y \otimes X) F .
$$

Lemma $7-(\Theta \otimes \operatorname{id})(|\operatorname{vec}(A)\rangle\langle\operatorname{vec}(B)|) \quad=\quad(\mathrm{id} \otimes \left.A^{\top}\right) F\left(\mathrm{id} \otimes B^{*}\right)$.

Since $X_{\star}$ is Hermitian of rank 2 and traceless, we can write its spectral decomposition as

$$
X_{\star}=t(|\psi\rangle\langle\psi|-|\phi\rangle\langle\phi|),
$$

for some orthogonal $|\psi\rangle,|\phi\rangle \in \mathcal{H} \otimes \mathcal{K}$ and some $t>0$. From Corollary 1 we have $\operatorname{tr}_{\mathcal{H}}\left(X_{\star}\right)=0$, which implies

$$
\operatorname{tr}_{\mathcal{H}}|\psi\rangle\langle\psi|=\operatorname{tr}_{\mathcal{H}}|\phi\rangle\langle\phi| .
$$

By Uhlmann's theorem 21, there exists a unitary $U$ on $\mathcal{H}$ such that

$$
|\phi\rangle=(U \otimes \mathrm{id})|\psi\rangle .
$$

Now choose $A$ such that

$$
|\psi\rangle=|\operatorname{vec}(A)\rangle .
$$

Then, using Lemma 5.

$$
|\phi\rangle=(U \otimes \operatorname{id})|\operatorname{vec}(A)\rangle=|\operatorname{vec}(U A)\rangle .
$$

By linearity,

$$
Y_{\star}=t((\Theta \otimes \operatorname{id})(|\psi\rangle\langle\psi|)-(\Theta \otimes \operatorname{id})(|\phi\rangle\langle\phi|)) .
$$

Using Lemma 7 we get

$$
(\Theta \otimes \operatorname{id})(|\psi\rangle\langle\psi|)=\left(\operatorname{id} \otimes A^{\top}\right) F\left(\operatorname{id} \otimes A^{*}\right)
$$

and

$$
\begin{aligned}
& (\Theta \otimes \operatorname{id})(|\phi\rangle\langle\phi|) \\
& =\left(\operatorname{id} \otimes(U A)^{\top}\right) F\left(\operatorname{id} \otimes(U A)^{*}\right) \\
& =\left(\operatorname{id} \otimes A^{\top} U^{\top}\right) F\left(\operatorname{id} \otimes U^{*} A^{*}\right) \\
& =\left(\operatorname{id} \otimes A^{\top}\right)\left(\operatorname{id} \otimes U^{\top}\right) F\left(\operatorname{id} \otimes U^{*}\right)\left(\operatorname{id} \otimes A^{*}\right)
\end{aligned}
$$

Therefore,

$$
\begin{aligned}
Y_{\star} & =t\left(\mathrm{id} \otimes A^{\top}\right)\left[F-\left(\mathrm{id} \otimes U^{\top}\right) F\left(\mathrm{id} \otimes U^{*}\right)\right]\left(\mathrm{id} \otimes A^{*}\right) \\
& =t\left(\mathrm{id} \otimes A^{\top}\right) F\left(\mathrm{id}-U^{\top} \otimes U^{*}\right)\left(\mathrm{id} \otimes A^{*}\right)
\end{aligned}
$$

where the second equality follows from Lemma 6. From submultiplicativity of rank under multiplication,

$$
\operatorname{rank}\left(Y_{\star}\right) \leq \operatorname{rank}\left(\mathrm{id}-U^{\top} \otimes U^{*}\right) .
$$

Now diagonalize $U$ as $U=V D V^{\dagger}$ with $D= \operatorname{diag}\left(\lambda_{1}, \ldots, \lambda_{d}\right),\left|\lambda_{i}\right|=1$. Then

$$
U^{\top}=V^{*} D V^{\top}, \quad U^{*}=V^{*} D^{*} V^{\top}
$$

so

$$
U^{\top} \otimes U^{*}=\left(V^{*} \otimes V^{*}\right)\left(D \otimes D^{*}\right)\left(V^{\top} \otimes V^{\top}\right)
$$

Thus $U^{\top} \otimes U^{*}$ is similar to $D \otimes D^{*}$, whose eigenvalues are $\lambda_{i} \lambda_{j}^{*}$. In particular, for every $i$,

$$
\lambda_{i} \lambda_{i}^{*}=1
$$

so

$$
\begin{aligned}
& \operatorname{dim} \operatorname{ker}\left(\mathrm{id}-U^{\top} \otimes U^{*}\right) \geq d \\
\Rightarrow \quad & \operatorname{rank}\left(\mathrm{id}-U^{\top} \otimes U^{*}\right) \leq d^{2}-d .
\end{aligned}
$$

Hence

$$
\operatorname{rank}\left(Y_{\star}\right) \leq d^{2}-d<d^{2}
$$

which contradicts Eq. (6).
Improved finite-error bound for quantum capacityHolevo and Werner introduced a simple upper bound on quantum capacity in terms of the diamond norm of the
transposed channel when a fixed nonzero decoding error is permitted [20]. Here we adopt the common convention

$$
\varepsilon:=\frac{1}{2}\left\|\mathrm{id}-\mathcal{D} \circ T^{\otimes m} \circ \mathcal{E}\right\|_{\diamond},
$$

so that the Holevo-Werner bound is valid for $\varepsilon<\frac{1}{2}$.
The place where this restriction enters the argument is the form $\|\Theta \circ \Psi\|_{\diamond} \leq\|\Theta\|_{\diamond}\|\Psi\|_{\diamond}$ applied to the map $\Psi:=\mathrm{id}-\mathcal{D} \circ T^{\otimes m} \circ \mathcal{E}$. However, $\Psi$ is always Hermiticitypreserving and trace-annihilating. Therefore Theorem 1 applies and yields the strictly better bound $\|\Theta \circ \Psi\|_{\diamond} \leq \frac{1}{\sqrt{2}}\|\Theta\|_{\diamond}\|\Psi\|_{\diamond}$. Plugging this refinement into the proof extends the finite-error regime from $\varepsilon<\frac{1}{2}$ to $\varepsilon<\frac{1}{\sqrt{2}}$.

Corollary 2 (partial transposition bound for $\varepsilon$-quantum capacity)-Let $T$ be a channel. If there exists a coding scheme $(\mathcal{E}, \mathcal{D})$ using $m$ uses of $T$ to transmit a message of dimension $d$ with error

$$
\varepsilon=\frac{1}{2}\left\|\mathrm{id}-\mathcal{D} \circ T^{\otimes m} \circ \mathcal{E}\right\|_{\diamond}<\frac{1}{\sqrt{2}},
$$

then

$$
\frac{\log _{2} d}{m} \leq \log _{2}\|\Theta \circ T\|_{\diamond}+\frac{1}{m} \log _{2}\left(\frac{1}{1-\sqrt{2} \varepsilon}\right)
$$

improving upon the finite-blocklength converse of [20]. Moreover, taking $m \rightarrow \infty$ yields the asymptotic statement

$$
Q_{\varepsilon}(T) \leq \log _{2}\|\Theta \circ T\|_{\diamond} \quad \text { for all } \varepsilon<\frac{1}{\sqrt{2}}
$$

More generally, any further improvement of the universal constant in Theorem 1 would translate directly into a larger admissible error range in this corollary, i.e., $\varepsilon<\frac{1}{2 \alpha}$.

Discussion-Although semidefinite-programming converses can be numerically stronger, the present refinement remains meaningful for both operational and conceptual reasons. Operationally, it strengthens the finiteerror Holevo-Werner converse by enlarging the admissible decoding-error regime. Conceptually, it shows that the former threshold was a byproduct of a coarse use of diamond-norm submultiplicativity. Once the perturbation is restricted to the physically natural class of Hermiticity-preserving trace-annihilating maps, transposition exhibits a genuine universal slack.

The remaining gap is now narrower and concrete. Our finite-dimensional analysis shows that the constant $\alpha=1 / \sqrt{2}$ is not tight for any nonzero channel difference, whereas the lower-bound construction implies that no dimension-independent constant below $2 / \pi$ can hold uniformly. Determining the optimal constant would therefore complete the geometric picture and identify the exact finite-error threshold certified by this transposition-based converse.

Problem 1-Determine the optimal absolute constant $\alpha^{*}$ in Theorem 1. At present, $\frac{2}{\pi} \leq \alpha_{*} \leq \frac{1}{\sqrt{2}}$. In particular, does one have the strict improvement $\alpha^{*}<\frac{1}{\sqrt{2}}$ ?
[12,14-16]
Acknowledgments-
[1] I. Devetak and P. W. Shor, Communications in Mathematical Physics 256, 287 (2005).
[2] G. Smith, in 2010 IEEE Information Theory Workshop (IEEE, 2010) pp. 1-5.
[3] S. Singh and N. Datta, Quantum 6, 775 (2022).
[4] G. Smith and P. Wu, IEEE Transactions on Information Theory (2025).
[5] J. Oppenheim, Science 321, 1783 (2008).
[6] G. Smith and J. Yard, Science 321, 1812 (2008).
[7] J. Lee, M. Kim, Y. Park, and S. Lee, Journal of Modern Optics 47, 2151 (2000).
[8] G. Vidal and R. F. Werner, Physical Review A 65, 032314 (2002).
[9] M. B. Plenio, Physical review letters 95, 090503 (2005).
[10] G. Tóth and T. Vértesi, Physical review letters 120, 020506 (2018).
[11] N. Johnston, D. W. Kribs, and V. I. Paulsen, Quantum Inf. Comput. 9, 16 (2009).
[12] J. Watrous, The theory of quantum information (Cambridge university press, 2018).
[13] X. Wang and R. Duan, in 2016 IEEE International Symposium on Information Theory (ISIT) (IEEE, 2016) pp. 1690-1694.
[14] X. Wang, W. Xie, and R. Duan, IEEE Transactions on Information Theory 64, 640 (2017).
[15] A. Müller-Hermes, D. Reeb, and M. M. Wolf, Journal of Mathematical Physics 57 (2016).
[16] X. Wang, K. Fang, and R. Duan, IEEE Transactions on Information Theory 65, 2583 (2018).
[17] M. Tomamichel, M. M. Wilde, and A. Winter, IEEE Transactions on Information Theory 63, 715 (2016).
[18] M. Berta and M. M. Wilde, New Journal of Physics 20, 053044 (2018).
[19] J. Tomiyama, Proceedings of the American Mathematical Society 88, 635 (1983).
[20] A. S. Holevo and R. F. Werner, Physical Review A 63, 032312 (2001).
[21] A. Uhlmann, Reports on Mathematical Physics 9, 273 (1976).
[22] J. Haah, R. Kothari, R. O'Donnell, and E. Tang, in 2023 IEEE 64th Annual Symposium on Foundations of Computer Science (FOCS) (IEEE, 2023) pp. 363-390.

## End Matter

A lower bound on $\alpha$-Fix an integer $d \geq 2$, and consider the unitary

$$
U_{d}=\operatorname{diag}\left(1, \omega, \omega^{2}, \ldots, \omega^{d-1}\right), \quad \omega=e^{2 \pi i / d} .
$$

Let

$$
\operatorname{Ad}_{U_{d}}(X)=U_{d} X U_{d}^{\dagger}
$$

be the corresponding unitary channel, and define

$$
\Lambda_{d}:=\Theta \circ\left(\mathrm{id}-\operatorname{Ad}_{U_{d}}\right) .
$$

The following two statements hold:

$$
\begin{equation*}
\left\|\Lambda_{d}\right\|_{\diamond} \geq 2 \cot \left(\frac{\pi}{2 d}\right) \tag{7}
\end{equation*}
$$

and

$$
\begin{equation*}
\left\|\mathrm{id}-\mathrm{Ad}_{U_{d}}\right\|_{\diamond}=2 . \tag{8}
\end{equation*}
$$

Once these are established, we can substitute $T=\operatorname{Ad}_{U_{d}}$ into Eq. (1). From Eqs. (7) and (8), we obtain

$$
2 \cot \left(\frac{\pi}{2 d}\right) \leq\left\|\Lambda_{d}\right\|_{\diamond} \leq \alpha\|\Theta\|_{\diamond}\left\|\mathrm{id}-\operatorname{Ad}_{U_{d}}\right\|_{\diamond}=2 \alpha d .
$$

Dividing both sides by $2 d$ and taking the limit $d \rightarrow \infty$ implies that any dimension-independent constant $\alpha$ satisfying Eq. (1) for every quantum channel $T$ must satisfy

$$
\alpha \geq \frac{2}{\pi} .
$$

It remains to establish Eqs. (7) and (8).
A lower bound on $\left\|\Lambda_{d}\right\|_{\diamond}$-Let

$$
\left|\Omega_{d}\right\rangle=\frac{1}{\sqrt{d}} \sum_{j=0}^{d-1}|j\rangle \otimes|j\rangle
$$

be the maximally entangled state, and let $\Phi_{d}=\left|\Omega_{d}\right\rangle\left\langle\Omega_{d}\right|$. Then

$$
\left\|\Lambda_{d}\right\|_{\diamond} \geq\left\|\left(\Lambda_{d} \otimes \mathrm{id}\right)\left(\Phi_{d}\right)\right\|_{1} .
$$

Let

$$
E_{i j}:=|i\rangle\langle j|, \quad 0 \leq i, j \leq d-1 .
$$

Expanding $\Phi_{d}$ in this basis gives

$$
\Phi_{d}=\frac{1}{d} \sum_{i, j=0}^{d-1} E_{i j} \otimes E_{i j} .
$$

Since $\Theta\left(E_{i j}\right)=E_{j i}$, we obtain

$$
(\Theta \otimes \mathrm{id})\left(\Phi_{d}\right)=\frac{1}{d} \sum_{i, j=0}^{d-1} E_{j i} \otimes E_{i j}=\frac{1}{d} F .
$$

Next we compute $\left(\Theta \circ \operatorname{Ad}_{U_{d}} \otimes \mathrm{id}\right)\left(\Phi_{d}\right)$ :

$$
\begin{aligned}
& \left(\Theta \circ \operatorname{Ad}_{U_{d}} \otimes \mathrm{id}\right)\left(\Phi_{d}\right) \\
& =\frac{1}{d} \sum_{i, j=0}^{d-1}\left(U_{d} E_{i j} U_{d}^{\dagger}\right)^{T} \otimes E_{i j} \\
& =\frac{1}{d} \sum_{i, j=0}^{d-1} \overline{U_{d}} E_{j i} U_{d}^{T} \otimes E_{i j} \\
& =\frac{1}{d}\left(\overline{U_{d}} \otimes \mathrm{id}\right)\left(\sum_{i, j=0}^{d-1} E_{j i} \otimes E_{i j}\right)\left(U_{d}^{T} \otimes \mathrm{id}\right) \\
& =\frac{1}{d}\left(\overline{U_{d}} \otimes \mathrm{id}\right) F\left(U_{d}^{T} \otimes \mathrm{id}\right) \\
& =\left(\text { Lemma 6) } \frac{1}{d} F\left(U_{d}^{T} \otimes \overline{U_{d}}\right)\right.
\end{aligned}
$$

Subtracting this from $(\Theta \otimes \mathrm{id})\left(\Phi_{d}\right)=\frac{1}{d} F$, we find

$$
\left(\Lambda_{d} \otimes \mathrm{id}\right)\left(\Phi_{d}\right)=\frac{1}{d} F\left(\mathrm{id}-U_{d}^{T} \otimes \overline{U_{d}}\right) .
$$

Thus

$$
\begin{aligned}
\left\|\left(\Lambda_{d} \otimes \mathrm{id}\right)\left(\Phi_{d}\right)\right\|_{1} & =\frac{1}{d}\left\|F\left(\mathrm{id}-U_{d}^{T} \otimes \overline{U_{d}}\right)\right\|_{1} \\
& =\frac{1}{d}\left\|\mathrm{id}-U_{d}^{T} \otimes \overline{U_{d}}\right\|_{1}
\end{aligned}
$$

and we get

$$
\left\|\Lambda_{d}\right\|_{\diamond} \geq \frac{1}{d}\left\|\mathrm{id}-U_{d}^{T} \otimes \overline{U_{d}}\right\|_{1} .
$$

Meanwhile, it follows from the definition of $U_{d}$ that id $U_{d}^{T} \otimes \overline{U_{d}}$ is diagonal with diagonal entries

$$
1-\omega^{a-b}, \quad 0 \leq a, b \leq d-1 .
$$

Therefore

$$
\left\|\Lambda_{d}\right\|_{\diamond} \geq \frac{1}{d} \sum_{a, b=0}^{d-1}\left|1-\omega^{a-b}\right|=\sum_{k=0}^{d-1}\left|1-\omega^{k}\right|=2 \cot \left(\frac{\pi}{2 d}\right),
$$

which proves Eq. (7).
Proof that $\left\|\mathrm{id}-\operatorname{Ad}_{U_{d}}\right\|_{\diamond}=2$-For unitary channels,

$$
\begin{aligned}
& \left\|\operatorname{Ad}_{U}-\operatorname{Ad}_{V}\right\|_{\diamond} \\
& =2 \sqrt{1-\min \left\{|z|^{2}: z \in \operatorname{conv}\left(\lambda_{1}, \ldots, \lambda_{d}\right)\right\}}
\end{aligned}
$$

where $\lambda_{1}, \ldots, \lambda_{d}$ are eigenvalues of $U^{\dagger} V$, and conv means convex hull 22 . Since $\sum_{k=0}^{d-1} \omega^{k}=0$, we get

$$
\left\|\mathrm{id}-\mathrm{Ad}_{U_{d}}\right\|_{\diamond}=2,
$$

which proves Eq. (8).


[^0]:    * ovalavo@snu.ac.kr
    ${ }^{\dagger}$ junglee@snu.ac.kr

