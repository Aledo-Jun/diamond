import Diamond.HolevoWerner.CodingScheme
import Diamond.HolevoWerner.ReplaceArgument
import Diamond.HolevoWerner.TensorPower

open scoped BigOperators
open scoped ComplexOrder
open scoped Kronecker
open scoped MatrixOrder
open scoped Matrix.Norms.Frobenius
open Matrix

namespace Diamond

universe u

noncomputable section

private theorem matrix_finset_sum_apply
    {ι α β R : Type*}
    [AddCommMonoid R]
    (s : Finset ι) (f : ι → Matrix α β R) (a : α) (b : β) :
    ((s.sum f) a) b = s.sum (fun i => ((f i) a) b) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert i s hi ih => simp [hi, ih]

private theorem matrix_sum_apply
    {ι α β R : Type*}
    [Fintype ι] [AddCommMonoid R]
    (f : ι → Matrix α β R) (a : α) (b : β) :
    ((Finset.univ.sum f) a) b = Finset.univ.sum (fun i => ((f i) a) b) := by
  simpa using matrix_finset_sum_apply (s := Finset.univ) (f := f) a b

private theorem sqrt_msg_pair_card
    {msg : Type u} [Fintype msg] :
    Real.sqrt (Fintype.card (msg × msg) : ℝ) = (Fintype.card msg : ℝ) := by
  have hcard : (Fintype.card (msg × msg) : ℝ) = (Fintype.card msg : ℝ) ^ (2 : ℕ) := by
    simp [Fintype.card_prod, Nat.cast_mul, pow_two]
  calc
    Real.sqrt (Fintype.card (msg × msg) : ℝ)
        = Real.sqrt ((Fintype.card msg : ℝ) ^ (2 : ℕ)) := by
            rw [hcard]
    _ = Fintype.card msg := by
          rw [Real.sqrt_sq_eq_abs]
          have hnn : 0 ≤ (Fintype.card msg : ℝ) := by positivity
          simp [abs_of_nonneg hnn]

private theorem traceNormOp_reindex
    {α β : Type u}
    [Fintype α] [DecidableEq α]
    [Fintype β] [DecidableEq β]
    (e : α ≃ β) (X : Matrix α α ℂ) :
    traceNormOp (Matrix.reindex e e X) = traceNormOp X := by
  let A : Matrix α α ℂ := Xᴴ * X
  let B : Matrix β β ℂ := (Matrix.reindex e e X)ᴴ * Matrix.reindex e e X
  have hB : B = Matrix.reindex e e A := by
    simpa [A, B, Matrix.conjTranspose_reindex] using
      (Matrix.reindexLinearEquiv_mul ℂ ℂ e e e Xᴴ X)
  have hchar : B.charpoly = A.charpoly := by
    rw [hB, Matrix.charpoly_reindex]
  have hroots :
      Multiset.map
          ((RCLike.ofReal : ℝ → ℂ) ∘
            (Matrix.isHermitian_conjTranspose_mul_self (Matrix.reindex e e X)).eigenvalues)
          Finset.univ.val =
        Multiset.map
          ((RCLike.ofReal : ℝ → ℂ) ∘
            (Matrix.isHermitian_conjTranspose_mul_self X).eigenvalues)
          Finset.univ.val := by
    rw [← (Matrix.isHermitian_conjTranspose_mul_self (Matrix.reindex e e X)).roots_charpoly_eq_eigenvalues]
    rw [show
          ((Matrix.reindex e e X)ᴴ * Matrix.reindex e e X).charpoly = (Xᴴ * X).charpoly by
            simpa [A, B] using hchar]
    rw [(Matrix.isHermitian_conjTranspose_mul_self X).roots_charpoly_eq_eigenvalues]
  have hvals :
      Multiset.map
          (Matrix.isHermitian_conjTranspose_mul_self (Matrix.reindex e e X)).eigenvalues
          Finset.univ.val =
        Multiset.map (Matrix.isHermitian_conjTranspose_mul_self X).eigenvalues Finset.univ.val := by
    have hre := congrArg (Multiset.map Complex.re) hroots
    simpa [Function.comp_def] using hre
  have hsqrt :
      (Multiset.map Real.sqrt
          (Multiset.map
            (Matrix.isHermitian_conjTranspose_mul_self (Matrix.reindex e e X)).eigenvalues
            Finset.univ.val)).sum =
        (Multiset.map Real.sqrt
          (Multiset.map (Matrix.isHermitian_conjTranspose_mul_self X).eigenvalues
            Finset.univ.val)).sum := by
    exact congrArg Multiset.sum (congrArg (Multiset.map Real.sqrt) hvals)
  simpa [traceNormOp, traceNorm] using hsqrt

private theorem isDensityState_reindex
    {α β : Type u}
    [Fintype α] [DecidableEq α]
    [Fintype β] [DecidableEq β]
    (e : α ≃ β)
    {ρ : Matrix α α ℂ} (hρ : IsDensityState ρ) :
    IsDensityState (Matrix.reindex e e ρ) := by
  refine ⟨?_, ?_⟩
  · simpa [Matrix.reindex_apply] using hρ.1.submatrix e.symm
  · calc
      Matrix.trace (Matrix.reindex e e ρ)
          = ∑ x : α, ρ x x := by
              rw [Matrix.trace]
              exact
                Fintype.sum_equiv e.symm
                  (fun i : β => ρ (e.symm i) (e.symm i))
                  (fun x : α => ρ x x)
                  (fun x => by simp)
      _ = 1 := hρ.2

private theorem tensorWithIdentity_reindex_ancilla_eq
    {d k₁ k₂ : Type u}
    [Fintype d] [DecidableEq d]
    [Fintype k₁] [DecidableEq k₁]
    [Fintype k₂] [DecidableEq k₂]
    (e : k₁ ≃ k₂) (Φ : Channel d) (X : Matrix (d × k₁) (d × k₁) ℂ) :
    Matrix.reindex (Equiv.prodCongr (Equiv.refl d) e) (Equiv.prodCongr (Equiv.refl d) e)
      (tensorWithIdentity d k₁ Φ X) =
      tensorWithIdentity d k₂ Φ
        (Matrix.reindex (Equiv.prodCongr (Equiv.refl d) e) (Equiv.prodCongr (Equiv.refl d) e) X) := by
  ext i j
  rcases i with ⟨a, b⟩
  rcases j with ⟨c, f⟩
  simp [tensorWithIdentity, Matrix.reindex_apply]

private theorem reindex_isHermitian
    {α β : Type u}
    [Fintype α] [DecidableEq α]
    [Fintype β] [DecidableEq β]
    (e : α ≃ β)
    {X : Matrix α α ℂ} (hX : Matrix.IsHermitian X) :
    Matrix.IsHermitian (Matrix.reindex e e X) := by
  unfold Matrix.IsHermitian at hX ⊢
  calc
    (Matrix.reindex e e X)ᴴ = Matrix.reindex e e Xᴴ := by
          simp [Matrix.conjTranspose_reindex]
    _ = Matrix.reindex e e X := by rw [hX]

private theorem tensorWithIdentity_comp
    {d k : Type u}
    [Fintype d] [DecidableEq d]
    [Fintype k] [DecidableEq k]
    (Φ Ψ : Channel d) :
    tensorWithIdentity d k (Ψ.comp Φ) =
      (tensorWithIdentity d k Ψ).comp (tensorWithIdentity d k Φ) := by
  simpa [superoperatorWithIdentity_eq_tensorWithIdentity] using
    (superoperatorWithIdentity_comp (a := d) (b := d) (c := d) (k := k) Φ Ψ)

private theorem tensorWithIdentity_hermiticityPreserving
    {d k : Type u}
    [Fintype d] [DecidableEq d]
    [Fintype k] [DecidableEq k]
    {Φ : Channel d}
    (hΦ : IsHermiticityPreserving Φ) :
    IsHermiticityPreserving (tensorWithIdentity d k Φ) := by
  simpa [superoperatorWithIdentity_eq_tensorWithIdentity] using
    (superoperatorWithIdentity_hermiticityPreserving
      (din := d) (dout := d) (k := k) (Φ := Φ) hΦ)

private theorem identityTensorChannel_hermiticityPreserving
    {d k : Type u}
    [Fintype d] [DecidableEq d]
    [Fintype k] [DecidableEq k]
    {Φ : Channel k}
    (hΦ : IsHermiticityPreserving Φ) :
    IsHermiticityPreserving (identityTensorChannel d k Φ) := by
  intro X
  ext i j
  rcases i with ⟨a, b⟩
  rcases j with ⟨c, e⟩
  let Y : Matrix k k ℂ := fun p q => X (c, p) (a, q)
  have hY :
      Φ Yᴴ b e = ((Φ Y)ᴴ) b e := by
    exact congrArg (fun M : Matrix k k ℂ => M b e) (hΦ Y)
  simpa [Y, identityTensorChannel, Matrix.conjTranspose_apply] using hY

private theorem diamondNormAt_le_of_pointwise
    {d k : Type u}
    [Fintype d] [DecidableEq d] [Nonempty d]
    [Fintype k] [DecidableEq k] [Nonempty k]
    (Φ : Channel d) (b : ℝ)
    (hbound : ∀ ρ : DensityState (d × k),
      traceNormOp (tensorWithIdentity d k Φ ρ.1) ≤ b) :
    diamondNormAt (d := d) (k := k) Φ ≤ b := by
  unfold diamondNormAt
  let i0 : d × k := (Classical.choice ‹Nonempty d›, Classical.choice ‹Nonempty k›)
  let ψ : d × k → ℂ := Pi.single i0 1
  let ρ0 : Matrix (d × k) (d × k) ℂ := Matrix.vecMulVec ψ (star ψ)
  have hρ0 : IsDensityState ρ0 := by
    refine ⟨?_, ?_⟩
    · simpa [ρ0, ψ] using Matrix.posSemidef_vecMulVec_self_star ψ
    · simp [ρ0, ψ, Matrix.trace_vecMulVec]
  apply csSup_le
  · exact ⟨traceNormOp (tensorWithIdentity d k Φ ρ0), ⟨⟨ρ0, hρ0⟩, rfl⟩⟩
  · intro r hr
    rcases hr with ⟨ρ, rfl⟩
    exact hbound ρ

private theorem sub_traceNorm_eq_sum_of_posSemidef_orthogonal
    {d : Type u}
    [Fintype d] [DecidableEq d]
    {P Q : Matrix d d ℂ}
    (hP : P.PosSemidef) (hQ : Q.PosSemidef)
    (hPQ : P * Q = 0) (hQP : Q * P = 0) :
    traceNormOp (P - Q) = traceNormOp P + traceNormOp Q := by
  have hXsq : (P - Q)ᴴ * (P - Q) = (P + Q)ᴴ * (P + Q) := by
    calc
      (P - Q)ᴴ * (P - Q)
          = (P - Q) * (P - Q) := by
              simp [hP.isHermitian.eq, hQ.isHermitian.eq]
      _ = P * P - P * Q - Q * P + Q * Q := by
            noncomm_ring
      _ = P * P + Q * Q := by
            simp [hPQ, hQP]
      _ = (P + Q) * (P + Q) := by
            calc
              P * P + Q * Q = P * P + P * Q + Q * P + Q * Q := by
                    simp [hPQ, hQP]
              _ = (P + Q) * (P + Q) := by
                    noncomm_ring
      _ = (P + Q)ᴴ * (P + Q) := by
            simp [hP.isHermitian.eq, hQ.isHermitian.eq]
  have hnorm : traceNormOp (P - Q) = traceNormOp (P + Q) := by
    exact traceNormOp_eq_of_conjTranspose_mul_self_eq hXsq
  calc
    traceNormOp (P - Q) = traceNormOp (P + Q) := hnorm
    _ = Complex.re (Matrix.trace (P + Q)) := by
          rw [traceNormOp_posSemidef_eq_trace (hP.add hQ)]
    _ = Complex.re (Matrix.trace P) + Complex.re (Matrix.trace Q) := by
          simp [Matrix.trace_add]
    _ = traceNormOp P + traceNormOp Q := by
          rw [traceNormOp_posSemidef_eq_trace hP, traceNormOp_posSemidef_eq_trace hQ]

private theorem traceNormOp_isometric_conj_eq_of_hermitian
    {d k : Type u}
    [Fintype d] [DecidableEq d]
    [Fintype k] [DecidableEq k]
    {K : Matrix k d ℂ} (hK : Kᴴ * K = 1)
    {X : Matrix d d ℂ} (hX : Matrix.IsHermitian X) :
    traceNormOp (K * X * Kᴴ) = traceNormOp X := by
  let U : Matrix d d ℂ := hX.eigenvectorUnitary
  let Ustar : Matrix d d ℂ := star hX.eigenvectorUnitary
  let D : Matrix d d ℂ := Matrix.diagonal (fun i => ((hX.eigenvalues i : ℝ) : ℂ))
  let Dpos : Matrix d d ℂ :=
    Matrix.diagonal (fun i => ((if 0 ≤ hX.eigenvalues i then hX.eigenvalues i else 0 : ℝ) : ℂ))
  let Dneg : Matrix d d ℂ :=
    Matrix.diagonal (fun i => ((if 0 ≤ hX.eigenvalues i then 0 else -hX.eigenvalues i : ℝ) : ℂ))
  let P : Matrix d d ℂ := U * Dpos * Ustar
  let Q : Matrix d d ℂ := U * Dneg * Ustar
  have hU_left : Ustar * U = 1 := by
    simpa [U, Ustar] using (Matrix.mem_unitaryGroup_iff').1 hX.eigenvectorUnitary.property
  have hDpos_pos : Dpos.PosSemidef := by
    refine Matrix.PosSemidef.diagonal ?_
    intro i
    by_cases h : 0 ≤ hX.eigenvalues i
    · simp [h]
    · simp [Dpos, h]
  have hDneg_pos : Dneg.PosSemidef := by
    refine Matrix.PosSemidef.diagonal ?_
    intro i
    by_cases h : 0 ≤ hX.eigenvalues i
    · simp [h]
    · have hle : hX.eigenvalues i ≤ 0 := le_of_not_ge h
      have hnonneg : 0 ≤ (-hX.eigenvalues i : ℝ) := by
        exact neg_nonneg.mpr hle
      have hnonnegC : (0 : ℂ) ≤ ((-hX.eigenvalues i : ℝ) : ℂ) := by
        exact_mod_cast hnonneg
      simpa [Dneg, h] using hnonnegC
  have hDorth1 : Dpos * Dneg = 0 := by
    ext i j
    by_cases hij : i = j
    · subst hij
      by_cases h : 0 ≤ hX.eigenvalues i
      · simp [Dpos, Dneg, h]
      · simp [Dpos, Dneg, h]
    · simp [Dpos, Dneg, hij]
  have hDorth2 : Dneg * Dpos = 0 := by
    ext i j
    by_cases hij : i = j
    · subst hij
      by_cases h : 0 ≤ hX.eigenvalues i
      · simp [Dpos, Dneg, h]
      · simp [Dpos, Dneg, h]
    · simp [Dpos, Dneg, hij]
  have hP_pos : P.PosSemidef := by
    simpa [P, U, Ustar, Matrix.mul_assoc] using hDpos_pos.mul_mul_conjTranspose_same U
  have hQ_pos : Q.PosSemidef := by
    simpa [Q, U, Ustar, Matrix.mul_assoc] using hDneg_pos.mul_mul_conjTranspose_same U
  have hPQ : P * Q = 0 := by
    calc
      P * Q = U * Dpos * (Ustar * U) * Dneg * Ustar := by
            simp [P, Q, Matrix.mul_assoc]
      _ = 0 := by
            simp [hU_left, hDorth1, Matrix.mul_assoc]
  have hQP : Q * P = 0 := by
    calc
      Q * P = U * Dneg * (Ustar * U) * Dpos * Ustar := by
            simp [P, Q, Matrix.mul_assoc]
      _ = 0 := by
            simp [hU_left, hDorth2, Matrix.mul_assoc]
  have hdiag_split : D = Dpos - Dneg := by
    ext i j
    by_cases hij : i = j
    · subst hij
      by_cases h : 0 ≤ hX.eigenvalues i
      · simp [D, Dpos, Dneg, h]
      · simp [D, Dpos, Dneg, h]
    · simp [D, Dpos, Dneg, hij]
  have hdecomp : X = P - Q := by
    calc
      X = U * D * Ustar := by
            simpa [U, Ustar, D, Matrix.mul_assoc, Unitary.conjStarAlgAut_apply] using
              hX.spectral_theorem
      _ = U * (Dpos - Dneg) * Ustar := by
            rw [hdiag_split]
      _ = P - Q := by
            simp [P, Q, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_assoc]
  let P' : Matrix k k ℂ := K * P * Kᴴ
  let Q' : Matrix k k ℂ := K * Q * Kᴴ
  have hP'_pos : P'.PosSemidef := by
    simpa [P', Matrix.mul_assoc] using hP_pos.mul_mul_conjTranspose_same K
  have hQ'_pos : Q'.PosSemidef := by
    simpa [Q', Matrix.mul_assoc] using hQ_pos.mul_mul_conjTranspose_same K
  have hP'Q' : P' * Q' = 0 := by
    calc
      P' * Q' = K * P * (Kᴴ * K) * Q * Kᴴ := by
            simp [P', Q', Matrix.mul_assoc]
      _ = 0 := by
            simp [hK, hPQ, Matrix.mul_assoc]
  have hQ'P' : Q' * P' = 0 := by
    calc
      Q' * P' = K * Q * (Kᴴ * K) * P * Kᴴ := by
            simp [P', Q', Matrix.mul_assoc]
      _ = 0 := by
            simp [hK, hQP, Matrix.mul_assoc]
  have htraceP' : Complex.re (Matrix.trace P') = Complex.re (Matrix.trace P) := by
    calc
      Complex.re (Matrix.trace P') = Complex.re (Matrix.trace ((Kᴴ * K) * P)) := by
        rw [show Matrix.trace P' = Matrix.trace (K * P * Kᴴ) by rfl]
        rw [Matrix.trace_mul_cycle K P Kᴴ]
      _ = Complex.re (Matrix.trace P) := by
            simp [hK]
  have htraceQ' : Complex.re (Matrix.trace Q') = Complex.re (Matrix.trace Q) := by
    calc
      Complex.re (Matrix.trace Q') = Complex.re (Matrix.trace ((Kᴴ * K) * Q)) := by
        rw [show Matrix.trace Q' = Matrix.trace (K * Q * Kᴴ) by rfl]
        rw [Matrix.trace_mul_cycle K Q Kᴴ]
      _ = Complex.re (Matrix.trace Q) := by
            simp [hK]
  have hXtrace : traceNormOp X = traceNormOp P + traceNormOp Q := by
    rw [hdecomp]
    exact sub_traceNorm_eq_sum_of_posSemidef_orthogonal hP_pos hQ_pos hPQ hQP
  have hKdecomp : K * X * Kᴴ = P' - Q' := by
    rw [hdecomp]
    simp [P', Q', Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_assoc]
  calc
    traceNormOp (K * X * Kᴴ) = traceNormOp (P' - Q') := by
          rw [hKdecomp]
    _ = traceNormOp P' + traceNormOp Q' := by
          exact sub_traceNorm_eq_sum_of_posSemidef_orthogonal hP'_pos hQ'_pos hP'Q' hQ'P'
    _ = traceNormOp P + traceNormOp Q := by
          rw [traceNormOp_posSemidef_eq_trace hP'_pos, traceNormOp_posSemidef_eq_trace hQ'_pos,
            traceNormOp_posSemidef_eq_trace hP_pos, traceNormOp_posSemidef_eq_trace hQ_pos,
            htraceP', htraceQ']
    _ = traceNormOp X := by
          exact hXtrace.symm

private theorem right_kronecker_conj_apply
    {d k₁ k₂ : Type u}
    [Fintype d] [DecidableEq d]
    [Fintype k₁] [DecidableEq k₁]
    [Fintype k₂] [DecidableEq k₂]
    (U : Matrix k₂ k₁ ℂ) (X : Matrix (d × k₁) (d × k₁) ℂ)
    (p q : d) (b e : k₂) :
    ((((1 : Matrix d d ℂ) ⊗ₖ U) * X) * (((1 : Matrix d d ℂ) ⊗ₖ U)ᴴ)) (p, b) (q, e) =
      ∑ r : k₁, ∑ s : k₁, U b r * X (p, r) (q, s) * star (U e s) := by
  rw [Matrix.mul_apply, Fintype.sum_prod_type]
  simp_rw [Matrix.mul_apply, Fintype.sum_prod_type]
  simp [Matrix.kroneckerMap_apply, Matrix.one_apply, Matrix.conjTranspose_apply, mul_assoc]
  rw [Finset.sum_eq_single q]
  · simp_rw [Finset.sum_mul]
    rw [Finset.sum_comm]
    simp [mul_assoc]
  · intro x _ hxq
    have hxq' : q ≠ x := by
      exact fun h => hxq h.symm
    simp [hxq']
  · simp

private theorem tensorWithIdentity_right_kronecker_comm
    {d k₁ k₂ : Type u}
    [Fintype d] [DecidableEq d]
    [Fintype k₁] [DecidableEq k₁]
    [Fintype k₂] [DecidableEq k₂]
    (Φ : Channel d) (U : Matrix k₂ k₁ ℂ) (X : Matrix (d × k₁) (d × k₁) ℂ) :
    tensorWithIdentity d k₂ Φ
        ((((1 : Matrix d d ℂ) ⊗ₖ U) * X) * (((1 : Matrix d d ℂ) ⊗ₖ U)ᴴ)) =
      ((1 : Matrix d d ℂ) ⊗ₖ U) * tensorWithIdentity d k₁ Φ X *
        (((1 : Matrix d d ℂ) ⊗ₖ U)ᴴ) := by
  ext i j
  rcases i with ⟨a, b⟩
  rcases j with ⟨c, e⟩
  let Xrs : k₁ → k₁ → Matrix d d ℂ := fun r s => fun p q => X (p, r) (q, s)
  have hslice :
      (fun p q : d =>
        ((((1 : Matrix d d ℂ) ⊗ₖ U) * X) * (((1 : Matrix d d ℂ) ⊗ₖ U)ᴴ)) (p, b) (q, e)) =
        ∑ r : k₁, ∑ s : k₁, (U b r * star (U e s)) • Xrs r s := by
    ext p q
    rw [right_kronecker_conj_apply]
    have hsum_eval :
        (∑ x, ∑ x_1, (U b x * star (U e x_1)) • Xrs x x_1) p q =
          ∑ x, ∑ x_1, U b x * (X (p, x) (q, x_1) * star (U e x_1)) := by
      simp_rw [matrix_sum_apply]
      simp [Xrs, mul_assoc, mul_left_comm, mul_comm]
    simpa [mul_assoc] using hsum_eval.symm
  calc
    tensorWithIdentity d k₂ Φ
        ((((1 : Matrix d d ℂ) ⊗ₖ U) * X) * (((1 : Matrix d d ℂ) ⊗ₖ U)ᴴ)) (a, b) (c, e)
        = Φ (∑ r : k₁, ∑ s : k₁, (U b r * star (U e s)) • Xrs r s) a c := by
            rw [tensorWithIdentity]
            simp [hslice]
    _ = ∑ r : k₁, ∑ s : k₁, U b r * Φ (Xrs r s) a c * star (U e s) := by
          rw [map_sum]
          simp_rw [map_sum, map_smul]
          have hsum_eval :
              (∑ x, ∑ x_1, (U b x * star (U e x_1)) • Φ (Xrs x x_1)) a c =
                ∑ x, ∑ x_1, U b x * (Φ (Xrs x x_1) a c * star (U e x_1)) := by
            simp_rw [matrix_sum_apply]
            simp [mul_assoc, mul_left_comm, mul_comm]
          simpa [mul_assoc] using hsum_eval
    _ = ((((1 : Matrix d d ℂ) ⊗ₖ U) * tensorWithIdentity d k₁ Φ X) *
          (((1 : Matrix d d ℂ) ⊗ₖ U)ᴴ)) (a, b) (c, e) := by
          symm
          simpa [tensorWithIdentity, Xrs, right_kronecker_conj_apply, mul_assoc]

private theorem pure_state_tensorWithIdentity_le_diamondOp_card_le
    {d k : Type u}
    [Fintype d] [DecidableEq d] [Nonempty d]
    [Fintype k] [DecidableEq k] [Nonempty k]
    (hcard : Fintype.card d ≤ Fintype.card k)
    {Φ : Channel d} (hΦ : IsHermiticityPreserving Φ)
    (ψ : (d × k) → ℂ) (hψ : ψ ⬝ᵥ star ψ = 1) :
    traceNormOp (tensorWithIdentity d k Φ (Matrix.vecMulVec ψ (star ψ))) ≤ diamondOp Φ := by
  obtain ⟨φ, U, hU, hφ, hψeq⟩ :=
    pure_state_compression_to_input_dim_with_isometry
      (d := d) (k := k) hcard ψ hψ
  let K : Matrix (d × k) (d × d) ℂ := (1 : Matrix d d ℂ) ⊗ₖ U
  have hK : Kᴴ * K = 1 := by
    dsimp [K]
    calc
      (((1 : Matrix d d ℂ) ⊗ₖ U)ᴴ) * ((1 : Matrix d d ℂ) ⊗ₖ U)
          = ((1 : Matrix d d ℂ)ᴴ * (1 : Matrix d d ℂ)) ⊗ₖ (Uᴴ * U) := by
              rw [Matrix.conjTranspose_kronecker, Matrix.mul_kronecker_mul]
      _ = (1 : Matrix d d ℂ) ⊗ₖ (1 : Matrix d d ℂ) := by
            simp [hU]
      _ = 1 := by
            simpa using (Matrix.one_kronecker_one (α := ℂ) (m := d) (n := d))
  let ρφ : Matrix (d × d) (d × d) ℂ := Matrix.vecMulVec φ (star φ)
  have hρφdens : IsDensityState ρφ := by
    refine ⟨?_, ?_⟩
    · simpa [ρφ] using Matrix.posSemidef_vecMulVec_self_star φ
    · rw [show Matrix.trace ρφ = Matrix.trace (Matrix.vecMulVec φ (star φ)) by rfl]
      rw [Matrix.trace_vecMulVec, hφ]
  have hψvec : ψ = K *ᵥ φ := by
    funext ij
    rcases ij with ⟨i, j⟩
    rw [hψeq]
    simp [K, Matrix.mulVec, dotProduct, Matrix.kroneckerMap_apply, Matrix.one_apply,
      Fintype.sum_prod_type, mul_comm]
  have hρψ :
      Matrix.vecMulVec ψ (star ψ) = K * ρφ * Kᴴ := by
    rw [hψvec]
    calc
      Matrix.vecMulVec (K *ᵥ φ) (star (K *ᵥ φ))
          = K * Matrix.vecMulVec φ (star (K *ᵥ φ)) := by
              rw [Matrix.mul_vecMulVec]
      _ = K * Matrix.vecMulVec φ (Matrix.vecMul (star φ) Kᴴ) := by
            rw [Matrix.star_mulVec]
      _ = K * (Matrix.vecMulVec φ (star φ) * Kᴴ) := by
            rw [← Matrix.vecMulVec_mul]
      _ = K * ρφ * Kᴴ := by
            simp [ρφ, Matrix.mul_assoc]
  have hanc_hpres :
      IsHermiticityPreserving (tensorWithIdentity d d Φ) :=
    tensorWithIdentity_hermiticityPreserving (d := d) (k := d) hΦ
  have hmid_herm :
      Matrix.IsHermitian (tensorWithIdentity d d Φ ρφ) := by
    unfold Matrix.IsHermitian
    calc
      (tensorWithIdentity d d Φ ρφ)ᴴ = tensorWithIdentity d d Φ ρφᴴ := by
            symm
            exact hanc_hpres ρφ
      _ = tensorWithIdentity d d Φ ρφ := by
            rw [hρφdens.1.isHermitian.eq]
  have hKquant : IsQuantumSuperoperator (singleKrausSuperoperator K) := by
    exact singleKrausSuperoperator_isQuantumSuperoperator hK
  have htransport :
      tensorWithIdentity d k Φ (Matrix.vecMulVec ψ (star ψ)) =
        K * tensorWithIdentity d d Φ ρφ * Kᴴ := by
    rw [hρψ]
    simpa [K, superoperatorWithIdentity_eq_tensorWithIdentity] using
      tensorWithIdentity_right_kronecker_comm (Φ := Φ) (U := U) (X := ρφ)
  calc
    traceNormOp (tensorWithIdentity d k Φ (Matrix.vecMulVec ψ (star ψ)))
        = traceNormOp (K * tensorWithIdentity d d Φ ρφ * Kᴴ) := by
            rw [htransport]
    _ ≤ traceNormOp (tensorWithIdentity d d Φ ρφ) := by
          simpa [K, singleKrausSuperoperator] using
            (traceNormOp_quantumSuperoperator_le_of_hermitian
              (Φ := singleKrausSuperoperator K)
              (hΦ := hKquant)
              (X := tensorWithIdentity d d Φ ρφ)
              hmid_herm)
    _ ≤ diamondOp Φ := by
          exact traceNorm_apply_le_diamond (d := d) (k := d) (Φ := Φ) ⟨ρφ, hρφdens⟩

private theorem pure_state_tensorWithIdentity_le_diamondOp_card_ge
    {d k : Type u}
    [Fintype d] [DecidableEq d] [Nonempty d]
    [Fintype k] [DecidableEq k] [Nonempty k]
    (hcard : Fintype.card k ≤ Fintype.card d)
    {Φ : Channel d} (hΦ : IsHermiticityPreserving Φ)
    (ψ : (d × k) → ℂ) (hψ : ψ ⬝ᵥ star ψ = 1) :
    traceNormOp (tensorWithIdentity d k Φ (Matrix.vecMulVec ψ (star ψ))) ≤ diamondOp Φ := by
  obtain ⟨φ, U, hU, hφ, hφeq⟩ :=
    pure_state_expansion_to_input_dim_with_isometry
      (d := d) (k := k) hcard ψ hψ
  let K : Matrix (d × d) (d × k) ℂ := (1 : Matrix d d ℂ) ⊗ₖ U
  have hK : Kᴴ * K = 1 := by
    dsimp [K]
    calc
      (((1 : Matrix d d ℂ) ⊗ₖ U)ᴴ) * ((1 : Matrix d d ℂ) ⊗ₖ U)
          = ((1 : Matrix d d ℂ)ᴴ * (1 : Matrix d d ℂ)) ⊗ₖ (Uᴴ * U) := by
              rw [Matrix.conjTranspose_kronecker, Matrix.mul_kronecker_mul]
      _ = (1 : Matrix d d ℂ) ⊗ₖ (1 : Matrix k k ℂ) := by
            simp [hU]
      _ = 1 := by
            simpa using (Matrix.one_kronecker_one (α := ℂ) (m := d) (n := k))
  let ρψ : Matrix (d × k) (d × k) ℂ := Matrix.vecMulVec ψ (star ψ)
  let ρφ : Matrix (d × d) (d × d) ℂ := Matrix.vecMulVec φ (star φ)
  have hρψdens : IsDensityState ρψ := by
    refine ⟨?_, ?_⟩
    · simpa [ρψ] using Matrix.posSemidef_vecMulVec_self_star ψ
    · rw [show Matrix.trace ρψ = Matrix.trace (Matrix.vecMulVec ψ (star ψ)) by rfl]
      rw [Matrix.trace_vecMulVec, hψ]
  have hρφdens : IsDensityState ρφ := by
    refine ⟨?_, ?_⟩
    · simpa [ρφ] using Matrix.posSemidef_vecMulVec_self_star φ
    · rw [show Matrix.trace ρφ = Matrix.trace (Matrix.vecMulVec φ (star φ)) by rfl]
      rw [Matrix.trace_vecMulVec, hφ]
  have hφvec : φ = K *ᵥ ψ := by
    funext ij
    rcases ij with ⟨i, j⟩
    rw [hφeq]
    simp [K, Matrix.mulVec, dotProduct, Matrix.kroneckerMap_apply, Matrix.one_apply,
      Fintype.sum_prod_type, mul_comm]
  have hρφ :
      ρφ = K * ρψ * Kᴴ := by
    dsimp [ρφ]
    rw [hφvec]
    calc
      Matrix.vecMulVec (K *ᵥ ψ) (star (K *ᵥ ψ))
          = K * Matrix.vecMulVec ψ (star (K *ᵥ ψ)) := by
              rw [Matrix.mul_vecMulVec]
      _ = K * Matrix.vecMulVec ψ (Matrix.vecMul (star ψ) Kᴴ) := by
            rw [Matrix.star_mulVec]
      _ = K * (Matrix.vecMulVec ψ (star ψ) * Kᴴ) := by
            rw [← Matrix.vecMulVec_mul]
      _ = K * ρψ * Kᴴ := by
            simp [ρψ, Matrix.mul_assoc]
  have hanc_hpres :
      IsHermiticityPreserving (tensorWithIdentity d k Φ) :=
    tensorWithIdentity_hermiticityPreserving (d := d) (k := k) hΦ
  have hmid_herm :
      Matrix.IsHermitian (tensorWithIdentity d k Φ ρψ) := by
    unfold Matrix.IsHermitian
    calc
      (tensorWithIdentity d k Φ ρψ)ᴴ = tensorWithIdentity d k Φ ρψᴴ := by
            symm
            exact hanc_hpres ρψ
      _ = tensorWithIdentity d k Φ ρψ := by
            rw [hρψdens.1.isHermitian.eq]
  have htransport :
      tensorWithIdentity d d Φ ρφ =
        K * tensorWithIdentity d k Φ ρψ * Kᴴ := by
    rw [hρφ]
    simpa [K, superoperatorWithIdentity_eq_tensorWithIdentity] using
      tensorWithIdentity_right_kronecker_comm (Φ := Φ) (U := U) (X := ρψ)
  calc
    traceNormOp (tensorWithIdentity d k Φ ρψ)
        = traceNormOp (K * tensorWithIdentity d k Φ ρψ * Kᴴ) := by
            symm
            exact traceNormOp_isometric_conj_eq_of_hermitian hK hmid_herm
    _ = traceNormOp (tensorWithIdentity d d Φ ρφ) := by
          rw [← htransport]
    _ ≤ diamondOp Φ := by
          exact traceNorm_apply_le_diamond (d := d) (k := d) (Φ := Φ) ⟨ρφ, hρφdens⟩

private theorem pure_state_tensorWithIdentity_le_diamondOp
    {d k : Type u}
    [Fintype d] [DecidableEq d] [Nonempty d]
    [Fintype k] [DecidableEq k] [Nonempty k]
    {Φ : Channel d} (hΦ : IsHermiticityPreserving Φ)
    (ψ : (d × k) → ℂ) (hψ : ψ ⬝ᵥ star ψ = 1) :
    traceNormOp (tensorWithIdentity d k Φ (Matrix.vecMulVec ψ (star ψ))) ≤ diamondOp Φ := by
  rcases Nat.le_total (Fintype.card d) (Fintype.card k) with h | h
  · exact pure_state_tensorWithIdentity_le_diamondOp_card_le h hΦ ψ hψ
  · exact pure_state_tensorWithIdentity_le_diamondOp_card_ge h hΦ ψ hψ

private theorem diamondNormAt_le_diamondOp_of_hpres
    {d k : Type u}
    [Fintype d] [DecidableEq d] [Nonempty d]
    [Fintype k] [DecidableEq k] [Nonempty k]
    {Φ : Channel d} (hΦ : IsHermiticityPreserving Φ) :
    diamondNormAt (d := d) (k := k) Φ ≤ diamondOp Φ := by
  refine diamondNormAt_le_of_pointwise (d := d) (k := k) Φ (diamondOp Φ) ?_
  intro ρ
  have hanc_hpres : IsHermiticityPreserving (tensorWithIdentity d k Φ) :=
    tensorWithIdentity_hermiticityPreserving (d := d) (k := k) hΦ
  exact traceNormOp_le_of_densityState_pure_bound
    (Ψ := tensorWithIdentity d k Φ)
    hanc_hpres
    (diamondOp Φ)
    (fun ψ hψ => pure_state_tensorWithIdentity_le_diamondOp hΦ ψ hψ)
    ρ.2

private theorem traceNormOp_le_mul_of_posSemidef_of_density_bound
    {n : Type u}
    [Fintype n] [DecidableEq n]
    {Ψ : Channel n} (hΨ : IsHermiticityPreserving Ψ) (b : ℝ)
    (hbound : ∀ ρ : DensityState n, traceNormOp (Ψ ρ.1) ≤ b)
    {X : Matrix n n ℂ} (hX : X.PosSemidef) :
    traceNormOp (Ψ X) ≤ b * traceNormOp X := by
  by_cases hzero : traceNormOp X = 0
  · have hXzero : X = 0 := (traceNormOp_eq_zero_iff).1 hzero
    subst hXzero
    have htr0 : traceNormOp (0 : Matrix n n ℂ) = 0 := (traceNormOp_eq_zero_iff).2 rfl
    simpa [htr0] using (trNorm_nonneg (0 : Matrix n n ℂ))
  · let r : ℝ := traceNormOp X
    have hr_eq : r = traceNormOp X := rfl
    have hr_nonneg : 0 ≤ r := by
      dsimp [r]
      exact trNorm_nonneg X
    have hr_pos : 0 < r := by
      have hr_ne : r ≠ 0 := by simpa [r] using hzero
      have hr_ne0 : (0 : ℝ) ≠ r := by simpa [eq_comm] using hr_ne
      exact lt_of_le_of_ne hr_nonneg hr_ne0
    have htrace_eq : Matrix.trace X = (r : ℂ) := by
      calc
        Matrix.trace X = ∑ i, ((hX.isHermitian.eigenvalues i : ℝ) : ℂ) := by
              simpa using hX.isHermitian.trace_eq_sum_eigenvalues
        _ = ((∑ i, hX.isHermitian.eigenvalues i : ℝ) : ℂ) := by simp
        _ = (traceNormOp X : ℂ) := by
              congr 1
              calc
                ∑ i, hX.isHermitian.eigenvalues i = Complex.re (Matrix.trace X) := by
                      rw [hX.isHermitian.trace_eq_sum_eigenvalues]
                      simp
                _ = traceNormOp X := by
                      symm
                      exact traceNormOp_posSemidef_eq_trace hX
        _ = (r : ℂ) := by rfl
    let ρ : Matrix n n ℂ := ((r⁻¹ : ℂ) • X)
    have hρdens : IsDensityState ρ := by
      refine ⟨?_, ?_⟩
      · dsimp [ρ]
        have hrinv_nonneg : (0 : ℂ) ≤ (r⁻¹ : ℂ) := by
          exact_mod_cast inv_nonneg.mpr hr_nonneg
        simpa using hX.smul hrinv_nonneg
      · dsimp [ρ]
        rw [Matrix.trace_smul, htrace_eq]
        have hr_ne : (r : ℂ) ≠ 0 := by exact_mod_cast hr_pos.ne'
        simpa [smul_eq_mul] using inv_mul_cancel₀ hr_ne
    have hΨρ_herm : Matrix.IsHermitian (Ψ ρ) := by
      unfold Matrix.IsHermitian
      calc
        (Ψ ρ)ᴴ = Ψ ρᴴ := by
              symm
              exact hΨ ρ
        _ = Ψ ρ := by
              rw [hρdens.1.isHermitian]
    have hX_smul : X = (r : ℂ) • ρ := by
      have hr_ne : (r : ℂ) ≠ 0 := by exact_mod_cast hr_pos.ne'
      have hone : ((r : ℂ) * ((r⁻¹ : ℂ))) = 1 := by
        exact mul_inv_cancel₀ hr_ne
      calc
        X = (1 : ℂ) • X := by simp
        _ = (((r : ℂ) * ((r⁻¹ : ℂ))) : ℂ) • X := by rw [hone]
        _ = (r : ℂ) • ρ := by
              simp [ρ, smul_smul, mul_assoc]
    calc
      traceNormOp (Ψ X)
          = traceNormOp ((r : ℂ) • Ψ ρ) := by
              rw [hX_smul, map_smul]
      _ = r * traceNormOp (Ψ ρ) := by
            exact traceNormOp_real_smul_of_hermitian hΨρ_herm hr_nonneg
      _ ≤ r * b := by
            exact mul_le_mul_of_nonneg_left (hbound ⟨ρ, hρdens⟩) hr_nonneg
      _ = b * traceNormOp X := by
            rw [hr_eq]
            ring

private theorem traceNormOp_le_mul_of_hermitian_of_density_bound
    {n : Type u}
    [Fintype n] [DecidableEq n]
    {Ψ : Channel n} (hΨ : IsHermiticityPreserving Ψ) (b : ℝ)
    (hbound : ∀ ρ : DensityState n, traceNormOp (Ψ ρ.1) ≤ b)
    {X : Matrix n n ℂ} (hX : Matrix.IsHermitian X) :
    traceNormOp (Ψ X) ≤ b * traceNormOp X := by
  let U : Matrix n n ℂ := hX.eigenvectorUnitary
  let Ustar : Matrix n n ℂ := star hX.eigenvectorUnitary
  let D : Matrix n n ℂ := Matrix.diagonal (fun i => ((hX.eigenvalues i : ℝ) : ℂ))
  let Dpos : Matrix n n ℂ :=
    Matrix.diagonal (fun i => ((if 0 ≤ hX.eigenvalues i then hX.eigenvalues i else 0 : ℝ) : ℂ))
  let Dneg : Matrix n n ℂ :=
    Matrix.diagonal (fun i => ((if 0 ≤ hX.eigenvalues i then 0 else -hX.eigenvalues i : ℝ) : ℂ))
  let P : Matrix n n ℂ := U * Dpos * Ustar
  let Q : Matrix n n ℂ := U * Dneg * Ustar
  have hU_left : Ustar * U = 1 := by
    simpa [U, Ustar] using (Matrix.mem_unitaryGroup_iff').1 hX.eigenvectorUnitary.property
  have hDpos_pos : Dpos.PosSemidef := by
    refine Matrix.PosSemidef.diagonal ?_
    intro i
    by_cases h : 0 ≤ hX.eigenvalues i
    · simp [h]
    · simp [Dpos, h]
  have hDneg_pos : Dneg.PosSemidef := by
    refine Matrix.PosSemidef.diagonal ?_
    intro i
    by_cases h : 0 ≤ hX.eigenvalues i
    · simp [h]
    · have hnonneg : 0 ≤ -hX.eigenvalues i := by
        have hle : hX.eigenvalues i ≤ 0 := le_of_not_ge h
        linarith
      have hnonnegC : (0 : ℂ) ≤ ((-hX.eigenvalues i : ℝ) : ℂ) := by
        exact_mod_cast hnonneg
      simpa [h] using hnonnegC
  have hP_pos : P.PosSemidef := by
    simpa [P, U, Ustar, Matrix.mul_assoc] using hDpos_pos.mul_mul_conjTranspose_same U
  have hQ_pos : Q.PosSemidef := by
    simpa [Q, U, Ustar, Matrix.mul_assoc] using hDneg_pos.mul_mul_conjTranspose_same U
  have hDorth1 : Dpos * Dneg = 0 := by
    ext i j
    by_cases hij : i = j
    · subst hij
      by_cases h : 0 ≤ hX.eigenvalues i
      · simp [Dpos, Dneg, h]
      · simp [Dpos, Dneg, h]
    · simp [Dpos, Dneg, hij]
  have hDorth2 : Dneg * Dpos = 0 := by
    ext i j
    by_cases hij : i = j
    · subst hij
      by_cases h : 0 ≤ hX.eigenvalues i
      · simp [Dpos, Dneg, h]
      · simp [Dpos, Dneg, h]
    · simp [Dpos, Dneg, hij]
  have hPQ : P * Q = 0 := by
    calc
      P * Q = U * Dpos * (Ustar * U) * Dneg * Ustar := by
            simp [P, Q, Matrix.mul_assoc]
      _ = 0 := by
            simp [hU_left, hDorth1, Matrix.mul_assoc]
  have hQP : Q * P = 0 := by
    calc
      Q * P = U * Dneg * (Ustar * U) * Dpos * Ustar := by
            simp [P, Q, Matrix.mul_assoc]
      _ = 0 := by
            simp [hU_left, hDorth2, Matrix.mul_assoc]
  have hdiag_split : D = Dpos - Dneg := by
    ext i j
    by_cases hij : i = j
    · subst hij
      by_cases h : 0 ≤ hX.eigenvalues i
      · simp [D, Dpos, Dneg, h]
      · simp [D, Dpos, Dneg, h]
    · simp [D, Dpos, Dneg, hij]
  have hdecomp : X = P - Q := by
    calc
      X = U * D * Ustar := by
            simpa [U, Ustar, D, Matrix.mul_assoc, Unitary.conjStarAlgAut_apply] using
              hX.spectral_theorem
      _ = U * (Dpos - Dneg) * Ustar := by rw [hdiag_split]
      _ = P - Q := by
            simp [P, Q, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_assoc]
  have htraceNormX :
      traceNormOp X = traceNormOp P + traceNormOp Q := by
    rw [hdecomp]
    exact sub_traceNorm_eq_sum_of_posSemidef_orthogonal hP_pos hQ_pos hPQ hQP
  have hΨP_herm : Matrix.IsHermitian (Ψ P) := by
    unfold Matrix.IsHermitian
    calc
      (Ψ P)ᴴ = Ψ Pᴴ := by
            symm
            exact hΨ P
      _ = Ψ P := by rw [hP_pos.isHermitian]
  have hΨQ_herm : Matrix.IsHermitian (Ψ Q) := by
    unfold Matrix.IsHermitian
    calc
      (Ψ Q)ᴴ = Ψ Qᴴ := by
            symm
            exact hΨ Q
      _ = Ψ Q := by rw [hQ_pos.isHermitian]
  have htri :
      traceNormOp (Ψ X) ≤ traceNormOp (Ψ P) + traceNormOp (Ψ Q) := by
    rw [hdecomp, map_sub, sub_eq_add_neg]
    simpa [traceNormOp_neg] using traceNormOp_add_le_of_hermitian hΨP_herm hΨQ_herm.neg
  calc
    traceNormOp (Ψ X) ≤ traceNormOp (Ψ P) + traceNormOp (Ψ Q) := htri
    _ ≤ b * traceNormOp P + b * traceNormOp Q := by
          exact add_le_add
            (traceNormOp_le_mul_of_posSemidef_of_density_bound hΨ b hbound hP_pos)
            (traceNormOp_le_mul_of_posSemidef_of_density_bound hΨ b hbound hQ_pos)
    _ = b * traceNormOp X := by
          rw [htraceNormX]
          ring

private theorem diamondNormAt_nonneg
    {d k : Type u}
    [Fintype d] [DecidableEq d] [Nonempty d]
    [Fintype k] [DecidableEq k] [Nonempty k]
    (Φ : Channel d) :
    0 ≤ diamondNormAt (d := d) (k := k) Φ := by
  let i0 : d × k := (Classical.choice ‹Nonempty d›, Classical.choice ‹Nonempty k›)
  let ψ : d × k → ℂ := Pi.single i0 1
  let ρ0 : DensityState (d × k) := by
    refine ⟨Matrix.vecMulVec ψ (star ψ), ?_⟩
    refine ⟨?_, ?_⟩
    · simpa [ψ] using Matrix.posSemidef_vecMulVec_self_star ψ
    · simp [ψ, Matrix.trace_vecMulVec]
  exact le_trans (trNorm_nonneg _) (traceNorm_apply_le_diamond (d := d) (k := k) (Φ := Φ) ρ0)

private theorem diamondOp_nonneg
    {d : Type u}
    [Fintype d] [DecidableEq d] [Nonempty d]
    (Φ : Channel d) :
    0 ≤ diamondOp Φ :=
  diamondNormAt_nonneg (d := d) (k := d) Φ

private def prodSwapAssocEquiv (a b c : Type u) : ((a × b) × c) ≃ b × (a × c) where
  toFun := fun x => (x.1.2, (x.1.1, x.2))
  invFun := fun x => ((x.2.1, x.1), x.2.2)
  left_inv := by intro x; cases x; rfl
  right_inv := by
    intro x
    rcases x with ⟨b, ac⟩
    rcases ac with ⟨a, c⟩
    rfl

private theorem tensorWithIdentity_stabilized_left_reindex_eq
    {a b c : Type u}
    [Fintype a] [DecidableEq a]
    [Fintype b] [DecidableEq b]
    [Fintype c] [DecidableEq c]
    (Φ : Channel a) (X : Matrix (((a × b) × c)) (((a × b) × c)) ℂ) :
    Matrix.reindex (Equiv.prodAssoc a b c) (Equiv.prodAssoc a b c)
      (tensorWithIdentity (a × b) c (tensorWithIdentity a b Φ) X) =
      tensorWithIdentity a (b × c) Φ
        (Matrix.reindex (Equiv.prodAssoc a b c) (Equiv.prodAssoc a b c) X) := by
  ext i j
  rcases i with ⟨p, q⟩
  rcases j with ⟨r, s⟩
  rfl

private theorem tensorWithIdentity_stabilized_right_reindex_eq
    {a b c : Type u}
    [Fintype a] [DecidableEq a]
    [Fintype b] [DecidableEq b]
    [Fintype c] [DecidableEq c]
    (Φ : Channel b) (X : Matrix (((a × b) × c)) (((a × b) × c)) ℂ) :
    Matrix.reindex (prodSwapAssocEquiv a b c) (prodSwapAssocEquiv a b c)
      (tensorWithIdentity (a × b) c (identityTensorChannel a b Φ) X) =
      tensorWithIdentity b (a × c) Φ
        (Matrix.reindex (prodSwapAssocEquiv a b c) (prodSwapAssocEquiv a b c) X) := by
  ext i j
  rcases i with ⟨p, q⟩
  rcases j with ⟨r, s⟩
  rfl

/-- The effective-channel data that the Holevo-Werner proof actually uses. This matches
the paper's proof surface more closely than the coding-scheme packaging: once the
effective map `D ∘ T^{⊗ m} ∘ E` is fixed, only its quantumness, the transposed-code
bound, and the error identity are needed. -/
structure HolevoWernerEffectiveData
    {phys msg : Type u}
    [Fintype phys] [DecidableEq phys]
    [Fintype msg] [DecidableEq msg] [Nonempty msg]
    (effective : Channel msg) (T : Channel phys) (m : ℕ) (ε : ℝ) : Prop where
  heffective : IsQuantumChannel effective
  htranspose_code_bound :
    diamondOp ((transposeMap msg).comp effective) ≤
      (diamondOp ((transposeMap phys).comp T)) ^ m
  herror :
    ε = (1 / 2 : ℝ) * diamondOp (idMinus effective)

/-- The additional submultiplicativity input used in the original Holevo-Werner proof. -/
structure OriginalHolevoWernerEffectiveData
    {phys msg : Type u}
    [Fintype phys] [DecidableEq phys]
    [Fintype msg] [DecidableEq msg] [Nonempty msg]
    (effective : Channel msg) (T : Channel phys) (m : ℕ) (ε : ℝ) : Prop extends
    HolevoWernerEffectiveData effective T m ε where
  hsubmult :
    diamondOp ((transposeMap msg).comp (idMinus effective)) ≤
      diamondOp (transposeMap msg) * diamondOp (idMinus effective)

/-- The original Holevo-Werner submultiplicativity step yields the concrete error-term
bound with coefficient `2`. This isolates the exact point in the original proof where
the `ε < 1 / 2` threshold comes from. -/
theorem holevo_werner_original_error_term_bound
    {phys msg : Type u}
    [Fintype phys] [DecidableEq phys]
    [Fintype msg] [DecidableEq msg] [Nonempty msg]
    {scheme : QuantumCodingScheme phys msg}
    {T : Channel phys} {m : ℕ} {ε : ℝ}
    (hdata : OriginalHolevoWernerCodeData scheme T m ε) :
    diamondOp ((transposeMap msg).comp (idMinus scheme.effective)) ≤
      2 * (Fintype.card msg : ℝ) * ε := by
  have herror_eq : diamondOp (idMinus scheme.effective) = 2 * ε := by
    nlinarith [hdata.toHolevoWernerCodeData.herror]
  calc
    diamondOp ((transposeMap msg).comp (idMinus scheme.effective)) ≤
        diamondOp (transposeMap msg) * diamondOp (idMinus scheme.effective) := hdata.hsubmult
    _ = Real.sqrt (Fintype.card (msg × msg) : ℝ) * (2 * ε) := by
          rw [transpose_diamond_exact (d := msg), herror_eq]
    _ = (Fintype.card msg : ℝ) * (2 * ε) := by
          rw [sqrt_msg_pair_card]
    _ = 2 * (Fintype.card msg : ℝ) * ε := by ring

/-- The original Holevo-Werner submultiplicativity step written directly at the level of
the effective channel `D ∘ T^{⊗ m} ∘ E`. -/
theorem holevo_werner_original_error_term_bound_effective
    {phys msg : Type u}
    [Fintype phys] [DecidableEq phys]
    [Fintype msg] [DecidableEq msg] [Nonempty msg]
    {effective : Channel msg}
    {T : Channel phys} {m : ℕ} {ε : ℝ}
    (hdata : OriginalHolevoWernerEffectiveData effective T m ε) :
    diamondOp ((transposeMap msg).comp (idMinus effective)) ≤
      2 * (Fintype.card msg : ℝ) * ε := by
  have herror_eq : diamondOp (idMinus effective) = 2 * ε := by
    nlinarith [hdata.toHolevoWernerEffectiveData.herror]
  calc
    diamondOp ((transposeMap msg).comp (idMinus effective)) ≤
        diamondOp (transposeMap msg) * diamondOp (idMinus effective) := hdata.hsubmult
    _ = Real.sqrt (Fintype.card (msg × msg) : ℝ) * (2 * ε) := by
          rw [transpose_diamond_exact (d := msg), herror_eq]
    _ = (Fintype.card msg : ℝ) * (2 * ε) := by
          rw [sqrt_msg_pair_card]
    _ = 2 * (Fintype.card msg : ℝ) * ε := by ring

/-- Remark 1 supplies the improved error-term bound with coefficient `√2`. This is the
precise replacement step used in the paper to upgrade the Holevo-Werner converse. -/
theorem holevo_werner_improved_error_term_bound
    {phys msg : Type u}
    [Fintype phys] [DecidableEq phys]
    [Fintype msg] [DecidableEq msg] [Nonempty msg]
    {scheme : QuantumCodingScheme phys msg}
    {T : Channel phys} {m : ℕ} {ε : ℝ}
    (hdata : HolevoWernerCodeData scheme T m ε) :
    diamondOp ((transposeMap msg).comp (idMinus scheme.effective)) ≤
      Real.sqrt 2 * (Fintype.card msg : ℝ) * ε := by
  have hrem :=
    remark1 (d := msg) (Ψ := idMinus scheme.effective)
      (idMinus_isHermiticityPreserving scheme.effective scheme.effective_isQuantumChannel)
      (idMinus_isTraceAnnihilating scheme.effective scheme.effective_isQuantumChannel)
  have herror_eq : diamondOp (idMinus scheme.effective) = 2 * ε := by
    nlinarith [hdata.herror]
  have hsqrt2_ne : Real.sqrt 2 ≠ 0 := by positivity
  calc
    diamondOp ((transposeMap msg).comp (idMinus scheme.effective)) ≤
        (1 / Real.sqrt 2) * diamondOp (transposeMap msg) * diamondOp (idMinus scheme.effective) :=
          hrem
    _ = (1 / Real.sqrt 2) * Real.sqrt (Fintype.card (msg × msg) : ℝ) * (2 * ε) := by
          rw [transpose_diamond_exact (d := msg), herror_eq]
    _ = (1 / Real.sqrt 2) * (Fintype.card msg : ℝ) * (2 * ε) := by
          rw [sqrt_msg_pair_card]
    _ = Real.sqrt 2 * (Fintype.card msg : ℝ) * ε := by
          have hsqrt2 : 2 / Real.sqrt 2 = Real.sqrt 2 := by
            apply (div_eq_iff hsqrt2_ne).2
            nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 2 by positivity)]
          calc
            (1 / Real.sqrt 2) * (Fintype.card msg : ℝ) * (2 * ε)
                = ((2 / Real.sqrt 2) * (Fintype.card msg : ℝ)) * ε := by ring
            _ = (Real.sqrt 2 * (Fintype.card msg : ℝ)) * ε := by rw [hsqrt2]
            _ = Real.sqrt 2 * (Fintype.card msg : ℝ) * ε := by ring

/-- Remark 1 supplies the improved error-term bound directly at the level of the effective
channel `D ∘ T^{⊗ m} ∘ E`. -/
theorem holevo_werner_improved_error_term_bound_effective
    {phys msg : Type u}
    [Fintype phys] [DecidableEq phys]
    [Fintype msg] [DecidableEq msg] [Nonempty msg]
    {effective : Channel msg}
    {T : Channel phys} {m : ℕ} {ε : ℝ}
    (hdata : HolevoWernerEffectiveData effective T m ε) :
    diamondOp ((transposeMap msg).comp (idMinus effective)) ≤
      Real.sqrt 2 * (Fintype.card msg : ℝ) * ε := by
  have hrem :=
    remark1 (d := msg) (Ψ := idMinus effective)
      (idMinus_isHermiticityPreserving effective hdata.heffective)
      (idMinus_isTraceAnnihilating effective hdata.heffective)
  have herror_eq : diamondOp (idMinus effective) = 2 * ε := by
    nlinarith [hdata.herror]
  have hsqrt2_ne : Real.sqrt 2 ≠ 0 := by positivity
  calc
    diamondOp ((transposeMap msg).comp (idMinus effective)) ≤
        (1 / Real.sqrt 2) * diamondOp (transposeMap msg) * diamondOp (idMinus effective) := hrem
    _ = (1 / Real.sqrt 2) * Real.sqrt (Fintype.card (msg × msg) : ℝ) * (2 * ε) := by
          rw [transpose_diamond_exact (d := msg), herror_eq]
    _ = (1 / Real.sqrt 2) * (Fintype.card msg : ℝ) * (2 * ε) := by
          rw [sqrt_msg_pair_card]
    _ = Real.sqrt 2 * (Fintype.card msg : ℝ) * ε := by
          have hsqrt2 : 2 / Real.sqrt 2 = Real.sqrt 2 := by
            apply (div_eq_iff hsqrt2_ne).2
            nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 2 by positivity)]
          calc
            (1 / Real.sqrt 2) * (Fintype.card msg : ℝ) * (2 * ε)
                = ((2 / Real.sqrt 2) * (Fintype.card msg : ℝ)) * ε := by ring
            _ = (Real.sqrt 2 * (Fintype.card msg : ℝ)) * ε := by rw [hsqrt2]
            _ = Real.sqrt 2 * (Fintype.card msg : ℝ) * ε := by ring

/-- Step 1 of the paper logic: the original finite-error Holevo-Werner converse,
packaged for a quantum coding scheme together with the original submultiplicativity
input. -/
theorem holevo_werner_original_linear_bound
    {phys msg : Type u}
    [Fintype phys] [DecidableEq phys]
    [Fintype msg] [DecidableEq msg] [Nonempty msg]
    {scheme : QuantumCodingScheme phys msg}
    {T : Channel phys} {m : ℕ} {ε : ℝ}
    (hdata : OriginalHolevoWernerCodeData scheme T m ε) :
    (1 - 2 * ε) * (Fintype.card msg : ℝ) ≤
      (diamondOp ((transposeMap phys).comp T)) ^ m := by
  let heff : OriginalHolevoWernerEffectiveData scheme.effective T m ε :=
    { toHolevoWernerEffectiveData :=
        { heffective := scheme.effective_isQuantumChannel
          htranspose_code_bound := hdata.toHolevoWernerCodeData.htranspose_code_bound
          herror := hdata.toHolevoWernerCodeData.herror }
      hsubmult := hdata.hsubmult }
  exact holevo_werner_linear_bound_of_error_term
    T m scheme.encoder scheme.decoder scheme.tensorPower ε 2
    (transpose_triangle_of_quantumChannel scheme.effective scheme.effective_isQuantumChannel)
    hdata.toHolevoWernerCodeData.htranspose_code_bound
    (holevo_werner_original_error_term_bound_effective heff)

/-- Logarithmic form of the original finite-error Holevo-Werner converse. -/
theorem holevo_werner_original_bound
    {phys msg : Type u}
    [Fintype phys] [DecidableEq phys]
    [Fintype msg] [DecidableEq msg] [Nonempty msg]
    {scheme : QuantumCodingScheme phys msg}
    {T : Channel phys} {m : ℕ} {ε : ℝ}
    (hdata : OriginalHolevoWernerCodeData scheme T m ε)
    (hm : 0 < m) (hε : ε < 1 / 2) :
    Real.logb 2 (Fintype.card msg : ℝ) / (m : ℝ) ≤
      Real.logb 2 (diamondOp ((transposeMap phys).comp T)) +
        (1 / (m : ℝ)) * Real.logb 2 (1 / (1 - 2 * ε)) := by
  exact holevo_werner_bound_of_linear_bound
    T m ε 2
    (holevo_werner_original_linear_bound hdata)
    hm hε (by norm_num)

/-- Step 1 at the level of the paper's effective channel `D ∘ T^{⊗ m} ∘ E`. -/
theorem holevo_werner_original_linear_bound_effective
    {phys msg : Type u}
    [Fintype phys] [DecidableEq phys]
    [Fintype msg] [DecidableEq msg] [Nonempty msg]
    {effective : Channel msg}
    {T : Channel phys} {m : ℕ} {ε : ℝ}
    (hdata : OriginalHolevoWernerEffectiveData effective T m ε) :
    (1 - 2 * ε) * (Fintype.card msg : ℝ) ≤
      (diamondOp ((transposeMap phys).comp T)) ^ m := by
  have htri :
      diamondOp (transposeMap msg) ≤
        diamondOp ((transposeMap msg).comp effective) +
          diamondOp ((transposeMap msg).comp (idMinus effective)) := by
    exact transpose_triangle_of_quantumChannel effective
      hdata.toHolevoWernerEffectiveData.heffective
  rw [transpose_diamond_exact (d := msg)] at htri
  rw [sqrt_msg_pair_card] at htri
  have hlinear :
      (1 - 2 * ε) * (Fintype.card msg : ℝ) ≤
        diamondOp ((transposeMap msg).comp effective) := by
    nlinarith [htri, holevo_werner_original_error_term_bound_effective hdata]
  calc
    (1 - 2 * ε) * (Fintype.card msg : ℝ) ≤
        diamondOp ((transposeMap msg).comp effective) := hlinear
    _ ≤ (diamondOp ((transposeMap phys).comp T)) ^ m :=
      hdata.toHolevoWernerEffectiveData.htranspose_code_bound

/-- Logarithmic form of the original finite-error Holevo-Werner converse at the level of
the effective channel. -/
theorem holevo_werner_original_bound_effective
    {phys msg : Type u}
    [Fintype phys] [DecidableEq phys]
    [Fintype msg] [DecidableEq msg] [Nonempty msg]
    {effective : Channel msg}
    {T : Channel phys} {m : ℕ} {ε : ℝ}
    (hdata : OriginalHolevoWernerEffectiveData effective T m ε)
    (hm : 0 < m) (hε : ε < 1 / 2) :
    Real.logb 2 (Fintype.card msg : ℝ) / (m : ℝ) ≤
      Real.logb 2 (diamondOp ((transposeMap phys).comp T)) +
        (1 / (m : ℝ)) * Real.logb 2 (1 / (1 - 2 * ε)) := by
  exact holevo_werner_bound_of_linear_bound
    T m ε 2
    (holevo_werner_original_linear_bound_effective hdata)
    hm hε (by norm_num)

/-- Step 2 of the paper logic: the replacement argument. If the transposed error term
admits the improved `c * dim * ε` estimate, the same Holevo-Werner proof yields the
corresponding linear converse with coefficient `c`. -/
theorem holevo_werner_linear_bound_of_replacement_argument
    {phys msg : Type u}
    [Fintype phys] [DecidableEq phys]
    [Fintype msg] [DecidableEq msg] [Nonempty msg]
    {scheme : QuantumCodingScheme phys msg}
    (T : Channel phys) (m : ℕ) (ε c : ℝ)
    (hdata : HolevoWernerCodeData scheme T m ε)
    (herror_term :
      diamondOp ((transposeMap msg).comp (idMinus scheme.effective)) ≤
        c * (Fintype.card msg : ℝ) * ε) :
    (1 - c * ε) * (Fintype.card msg : ℝ) ≤
      (diamondOp ((transposeMap phys).comp T)) ^ m := by
  exact holevo_werner_linear_bound_of_error_term
    T m scheme.encoder scheme.decoder scheme.tensorPower ε c
    (transpose_triangle_of_quantumChannel scheme.effective scheme.effective_isQuantumChannel)
    hdata.htranspose_code_bound herror_term

/-- Step 2 of the paper logic at the level of the effective channel. -/
theorem holevo_werner_linear_bound_of_replacement_argument_effective
    {phys msg : Type u}
    [Fintype phys] [DecidableEq phys]
    [Fintype msg] [DecidableEq msg] [Nonempty msg]
    {effective : Channel msg}
    (T : Channel phys) (m : ℕ) (ε c : ℝ)
    (hdata : HolevoWernerEffectiveData effective T m ε)
    (herror_term :
      diamondOp ((transposeMap msg).comp (idMinus effective)) ≤
        c * (Fintype.card msg : ℝ) * ε) :
    (1 - c * ε) * (Fintype.card msg : ℝ) ≤
      (diamondOp ((transposeMap phys).comp T)) ^ m := by
  have htri :
      diamondOp (transposeMap msg) ≤
        diamondOp ((transposeMap msg).comp effective) +
          diamondOp ((transposeMap msg).comp (idMinus effective)) := by
    exact transpose_triangle_of_quantumChannel effective hdata.heffective
  rw [transpose_diamond_exact (d := msg)] at htri
  rw [sqrt_msg_pair_card] at htri
  have hlinear :
      (1 - c * ε) * (Fintype.card msg : ℝ) ≤
        diamondOp ((transposeMap msg).comp effective) := by
    nlinarith [htri, herror_term]
  calc
    (1 - c * ε) * (Fintype.card msg : ℝ) ≤
        diamondOp ((transposeMap msg).comp effective) := hlinear
    _ ≤ (diamondOp ((transposeMap phys).comp T)) ^ m := hdata.htranspose_code_bound

/-- Logarithmic form of the replacement argument. -/
theorem holevo_werner_bound_of_replacement_argument
    {phys msg : Type u}
    [Fintype phys] [DecidableEq phys]
    [Fintype msg] [DecidableEq msg] [Nonempty msg]
    {scheme : QuantumCodingScheme phys msg}
    (T : Channel phys) (m : ℕ) (ε c : ℝ)
    (hdata : HolevoWernerCodeData scheme T m ε)
    (herror_term :
      diamondOp ((transposeMap msg).comp (idMinus scheme.effective)) ≤
        c * (Fintype.card msg : ℝ) * ε)
    (hm : 0 < m) (hε : ε < 1 / c) (hc : 0 < c) :
    Real.logb 2 (Fintype.card msg : ℝ) / (m : ℝ) ≤
      Real.logb 2 (diamondOp ((transposeMap phys).comp T)) +
        (1 / (m : ℝ)) * Real.logb 2 (1 / (1 - c * ε)) := by
  exact holevo_werner_bound_of_linear_bound
    T m ε c
    (holevo_werner_linear_bound_of_replacement_argument T m ε c hdata herror_term)
    hm hε hc

/-- Logarithmic form of the replacement argument at the level of the effective channel. -/
theorem holevo_werner_bound_of_replacement_argument_effective
    {phys msg : Type u}
    [Fintype phys] [DecidableEq phys]
    [Fintype msg] [DecidableEq msg] [Nonempty msg]
    {effective : Channel msg}
    (T : Channel phys) (m : ℕ) (ε c : ℝ)
    (hdata : HolevoWernerEffectiveData effective T m ε)
    (herror_term :
      diamondOp ((transposeMap msg).comp (idMinus effective)) ≤
        c * (Fintype.card msg : ℝ) * ε)
    (hm : 0 < m) (hε : ε < 1 / c) (hc : 0 < c) :
    Real.logb 2 (Fintype.card msg : ℝ) / (m : ℝ) ≤
      Real.logb 2 (diamondOp ((transposeMap phys).comp T)) +
        (1 / (m : ℝ)) * Real.logb 2 (1 / (1 - c * ε)) := by
  exact holevo_werner_bound_of_linear_bound
    T m ε c
    (holevo_werner_linear_bound_of_replacement_argument_effective T m ε c hdata herror_term)
    hm hε hc

/-- The original `htranspose_code_bound` assumption is implied by the decoder-reduced
pointwise bound obtained from the standard Holevo-Werner factorization
`Θ ∘ D = D̄ ∘ Θ`. -/
theorem ReducedTransposeCodeBoundData.of_middle_pointwise_bound
    {phys msg : Type u}
    [Fintype phys] [DecidableEq phys]
    [Fintype msg] [DecidableEq msg] [Nonempty msg]
    {scheme : QuantumCodingScheme phys msg}
    {T : Channel phys} {m : ℕ}
    (hmiddle :
      ∀ ρ : DensityState (msg × msg),
        traceNormOp
          (superoperatorWithIdentity msg phys msg
            (((transposeMap phys).comp scheme.tensorPower).comp scheme.encoder) ρ.1) ≤
          (diamondOp ((transposeMap phys).comp T)) ^ m) :
    ReducedTransposeCodeBoundData scheme T m := by
  refine { hpointwise := ?_ }
  intro ρ
  have htrans_tensor :
      ∀ X, ((transposeMap phys).comp scheme.tensorPower) Xᴴ =
        (((transposeMap phys).comp scheme.tensorPower) X)ᴴ := by
    intro X
    calc
      ((transposeMap phys).comp scheme.tensorPower) Xᴴ
          = transposeMap phys (scheme.tensorPower Xᴴ) := by rfl
      _ = transposeMap phys ((scheme.tensorPower X)ᴴ) := by
            rw [scheme.htensorPower.hermiticity_preserving]
      _ = (transposeMap phys (scheme.tensorPower X))ᴴ := by
            exact transposeMap_hermiticityPreserving (d := phys) (scheme.tensorPower X)
  have hmid_hpres :
      ∀ X,
        ((((transposeMap phys).comp scheme.tensorPower).comp scheme.encoder) Xᴴ) =
          (((((transposeMap phys).comp scheme.tensorPower).comp scheme.encoder) X))ᴴ := by
    intro X
    calc
      ((((transposeMap phys).comp scheme.tensorPower).comp scheme.encoder) Xᴴ)
          = ((transposeMap phys).comp scheme.tensorPower) (scheme.encoder Xᴴ) := by rfl
      _ = ((transposeMap phys).comp scheme.tensorPower) ((scheme.encoder X)ᴴ) := by
            rw [scheme.hencoder.hermiticity_preserving]
      _ = (((((transposeMap phys).comp scheme.tensorPower).comp scheme.encoder) X))ᴴ := by
            simpa [LinearMap.comp_apply] using htrans_tensor (scheme.encoder X)
  have hmid_herm :
      Matrix.IsHermitian
        (superoperatorWithIdentity msg phys msg
          (((transposeMap phys).comp scheme.tensorPower).comp scheme.encoder) ρ.1) := by
    unfold Matrix.IsHermitian
    calc
      (superoperatorWithIdentity msg phys msg
        (((transposeMap phys).comp scheme.tensorPower).comp scheme.encoder) ρ.1)ᴴ
          =
        superoperatorWithIdentity msg phys msg
          (((transposeMap phys).comp scheme.tensorPower).comp scheme.encoder) ρ.1ᴴ := by
            symm
            exact
              superoperatorWithIdentity_hermiticityPreserving
                (din := msg) (dout := phys) (k := msg)
                (Φ := (((transposeMap phys).comp scheme.tensorPower).comp scheme.encoder))
                hmid_hpres ρ.1
      _ =
        superoperatorWithIdentity msg phys msg
          (((transposeMap phys).comp scheme.tensorPower).comp scheme.encoder) ρ.1 := by
            rw [ρ.2.1.isHermitian.eq]
  have hcontract :
      traceNormOp
          ((superoperatorWithIdentity phys msg msg
              (transposeConjugateSuperoperator scheme.decoder)).comp
            (superoperatorWithIdentity msg phys msg
              (((transposeMap phys).comp scheme.tensorPower).comp scheme.encoder)) ρ.1) ≤
        traceNormOp
          (superoperatorWithIdentity msg phys msg
            (((transposeMap phys).comp scheme.tensorPower).comp scheme.encoder) ρ.1) := by
    simpa [LinearMap.comp_apply] using
      (traceNormOp_quantumSuperoperator_le_of_hermitian
        (Φ := superoperatorWithIdentity phys msg msg
          (transposeConjugateSuperoperator scheme.decoder))
        (hΦ := superoperatorWithIdentity_isQuantumSuperoperator
          (din := phys) (dout := msg) (k := msg)
          (transposeConjugateSuperoperator_isQuantumSuperoperator scheme.hdecoder))
        (X := superoperatorWithIdentity msg phys msg
          (((transposeMap phys).comp scheme.tensorPower).comp scheme.encoder) ρ.1)
        hmid_herm)
  exact le_trans hcontract (hmiddle ρ)

/-- The decoder-reduced pointwise bound follows from a post-encoder pointwise bound for the
ancilla-extended transposed physical middle channel. -/
theorem ReducedTransposeCodeBoundData.of_post_encoder_reduction
    {phys msg : Type u}
    [Fintype phys] [DecidableEq phys]
    [Fintype msg] [DecidableEq msg] [Nonempty msg]
    {scheme : QuantumCodingScheme phys msg}
    {T : Channel phys} {m : ℕ}
    (hpost : PostEncoderTransposeCodeBoundData scheme T m) :
    ReducedTransposeCodeBoundData scheme T m := by
  refine ReducedTransposeCodeBoundData.of_middle_pointwise_bound ?_
  intro ρ
  let σmat : Matrix (phys × msg) (phys × msg) ℂ :=
    superoperatorWithIdentity msg phys msg scheme.encoder ρ.1
  have hσ : IsDensityState σmat := by
    exact quantumSuperoperator_maps_densityState
      (superoperatorWithIdentity msg phys msg scheme.encoder)
      (superoperatorWithIdentity_isQuantumSuperoperator
        (din := msg) (dout := phys) (k := msg) scheme.hencoder)
      ρ.2
  have hrewrite :
      superoperatorWithIdentity msg phys msg
        (((transposeMap phys).comp scheme.tensorPower).comp scheme.encoder) ρ.1 =
        superoperatorWithIdentity phys phys msg
          ((transposeMap phys).comp scheme.tensorPower) σmat := by
    simp [σmat, ← superoperatorWithIdentity_comp
      (Φ := scheme.encoder)
      (Ψ := ((transposeMap phys).comp scheme.tensorPower))]
  rw [hrewrite]
  exact hpost.hpointwise ⟨σmat, hσ⟩

/-- The post-encoder pointwise bound follows from the corresponding fixed-ancilla
diamond-norm bound for the transposed physical middle channel. -/
theorem PostEncoderTransposeCodeBoundData.of_diamondAt_bound
    {phys msg : Type u}
    [Fintype phys] [DecidableEq phys]
    [Fintype msg] [DecidableEq msg] [Nonempty msg]
    {scheme : QuantumCodingScheme phys msg}
    {T : Channel phys} {m : ℕ}
    (hbound : PostEncoderDiamondAtBoundData scheme T m) :
    PostEncoderTransposeCodeBoundData scheme T m := by
  refine { hpointwise := ?_ }
  intro σ
  exact le_trans
    (traceNorm_apply_le_diamond
      (d := phys) (k := msg)
      (Φ := ((transposeMap phys).comp scheme.tensorPower)) σ)
    hbound.hbound

/-- The pure-state post-encoder bound follows directly from the corresponding fixed-ancilla
diamond-norm bound for the transposed physical middle channel. -/
theorem PostEncoderPureTransposeCodeBoundData.of_diamondAt_bound
    {phys msg : Type u}
    [Fintype phys] [DecidableEq phys]
    [Fintype msg] [DecidableEq msg] [Nonempty msg]
    {scheme : QuantumCodingScheme phys msg}
    {T : Channel phys} {m : ℕ}
    (hbound : PostEncoderDiamondAtBoundData scheme T m) :
    PostEncoderPureTransposeCodeBoundData scheme T m := by
  refine { hpointwise := ?_ }
  intro ψ hψ
  let ρ : DensityState (phys × msg) := by
    refine ⟨Matrix.vecMulVec ψ (star ψ), ?_⟩
    refine ⟨?_, ?_⟩
    · simpa using Matrix.posSemidef_vecMulVec_self_star ψ
    · rw [Matrix.trace_vecMulVec, hψ]
  exact le_trans
    (traceNorm_apply_le_diamond
      (d := phys) (k := msg)
      (Φ := ((transposeMap phys).comp scheme.tensorPower)) ρ)
    hbound.hbound

/-- The post-encoder density-state bound follows from the corresponding pure-state bound,
since the ancilla-extended transposed physical middle map is Hermiticity-preserving. -/
theorem PostEncoderTransposeCodeBoundData.of_pure_state_bound
    {phys msg : Type u}
    [Fintype phys] [DecidableEq phys]
    [Fintype msg] [DecidableEq msg] [Nonempty msg]
    {scheme : QuantumCodingScheme phys msg}
    {T : Channel phys} {m : ℕ}
    (hpure : PostEncoderPureTransposeCodeBoundData scheme T m) :
    PostEncoderTransposeCodeBoundData scheme T m := by
  refine { hpointwise := ?_ }
  intro σ
  have hmid_hpres : IsHermiticityPreserving ((transposeMap phys).comp scheme.tensorPower) := by
    exact hermiticityPreserving_comp
      (Ψ := transposeMap phys)
      (Φ := scheme.tensorPower)
      (transposeMap_hermiticityPreserving (d := phys))
      scheme.htensorPower.hermiticity_preserving
  have hanc_hpres :
      IsHermiticityPreserving
        (superoperatorWithIdentity phys phys msg
          ((transposeMap phys).comp scheme.tensorPower)) := by
    exact superoperatorWithIdentity_hermiticityPreserving
      (din := phys) (dout := phys) (k := msg)
      (Φ := ((transposeMap phys).comp scheme.tensorPower))
      hmid_hpres
  exact traceNormOp_le_of_densityState_pure_bound
    (Ψ := superoperatorWithIdentity phys phys msg
      ((transposeMap phys).comp scheme.tensorPower))
    hanc_hpres
    ((diamondOp ((transposeMap phys).comp T)) ^ m)
    hpure.hpointwise
    σ.2

/-- If the message ancilla dimension is at least the physical input dimension, then the
post-encoder pure-state bound follows from the ordinary `diamondOp` bound on the transposed
physical middle channel by compressing pure witnesses down to ancilla `phys`. -/
theorem PostEncoderPureTransposeCodeBoundData.of_diamondOp_bound_card_le
    {phys msg : Type u}
    [Fintype phys] [DecidableEq phys] [Nonempty phys]
    [Fintype msg] [DecidableEq msg] [Nonempty msg]
    {scheme : QuantumCodingScheme phys msg}
    {T : Channel phys} {m : ℕ}
    (hcard : Fintype.card phys ≤ Fintype.card msg)
    (hbound :
      diamondOp ((transposeMap phys).comp scheme.tensorPower) ≤
        (diamondOp ((transposeMap phys).comp T)) ^ m) :
    PostEncoderPureTransposeCodeBoundData scheme T m := by
  refine { hpointwise := ?_ }
  intro ψ hψ
  obtain ⟨φ, U, hU, hφ, hψeq⟩ :=
    pure_state_compression_to_input_dim_with_isometry
      (d := phys) (k := msg) hcard ψ hψ
  let Φ : Channel phys := (transposeMap phys).comp scheme.tensorPower
  let K : Matrix (phys × msg) (phys × phys) ℂ := (1 : Matrix phys phys ℂ) ⊗ₖ U
  have hK : Kᴴ * K = 1 := by
    dsimp [K]
    calc
      (((1 : Matrix phys phys ℂ) ⊗ₖ U)ᴴ) * ((1 : Matrix phys phys ℂ) ⊗ₖ U)
          = ((1 : Matrix phys phys ℂ)ᴴ * (1 : Matrix phys phys ℂ)) ⊗ₖ (Uᴴ * U) := by
              rw [Matrix.conjTranspose_kronecker, Matrix.mul_kronecker_mul]
      _ = (1 : Matrix phys phys ℂ) ⊗ₖ (1 : Matrix phys phys ℂ) := by
            simp [hU]
      _ = 1 := by
            simpa using (Matrix.one_kronecker_one (α := ℂ) (m := phys) (n := phys))
  let ρφ : Matrix (phys × phys) (phys × phys) ℂ := Matrix.vecMulVec φ (star φ)
  have hρφdens : IsDensityState ρφ := by
    refine ⟨?_, ?_⟩
    · simpa [ρφ] using Matrix.posSemidef_vecMulVec_self_star φ
    · rw [show Matrix.trace ρφ = Matrix.trace (Matrix.vecMulVec φ (star φ)) by rfl]
      rw [Matrix.trace_vecMulVec, hφ]
  have hψvec : ψ = K *ᵥ φ := by
    funext ij
    rcases ij with ⟨i, j⟩
    rw [hψeq]
    simp [K, Matrix.mulVec, dotProduct, Matrix.kroneckerMap_apply, Matrix.one_apply,
      Fintype.sum_prod_type, mul_comm]
  have hρψ :
      Matrix.vecMulVec ψ (star ψ) = K * ρφ * Kᴴ := by
    rw [hψvec]
    calc
      Matrix.vecMulVec (K *ᵥ φ) (star (K *ᵥ φ))
          = K * Matrix.vecMulVec φ (star (K *ᵥ φ)) := by
              rw [Matrix.mul_vecMulVec]
      _ = K * Matrix.vecMulVec φ (Matrix.vecMul (star φ) Kᴴ) := by
            rw [Matrix.star_mulVec]
      _ = K * (Matrix.vecMulVec φ (star φ) * Kᴴ) := by
            rw [← Matrix.vecMulVec_mul]
      _ = K * ρφ * Kᴴ := by
            simp [ρφ, Matrix.mul_assoc]
  have hΦ_hpres : IsHermiticityPreserving Φ := by
    exact hermiticityPreserving_comp
      (Ψ := transposeMap phys)
      (Φ := scheme.tensorPower)
      (transposeMap_hermiticityPreserving (d := phys))
      scheme.htensorPower.hermiticity_preserving
  have hanc_hpres :
      IsHermiticityPreserving (superoperatorWithIdentity phys phys phys Φ) := by
    exact superoperatorWithIdentity_hermiticityPreserving
      (din := phys) (dout := phys) (k := phys)
      (Φ := Φ)
      hΦ_hpres
  have hmid_herm :
      Matrix.IsHermitian (superoperatorWithIdentity phys phys phys Φ ρφ) := by
    unfold Matrix.IsHermitian
    calc
      (superoperatorWithIdentity phys phys phys Φ ρφ)ᴴ
          = superoperatorWithIdentity phys phys phys Φ ρφᴴ := by
              symm
              exact hanc_hpres ρφ
      _ = superoperatorWithIdentity phys phys phys Φ ρφ := by
            rw [hρφdens.1.isHermitian.eq]
  have hKquant : IsQuantumSuperoperator (singleKrausSuperoperator K) := by
    refine
      { trace_preserving := ?_
        hermiticity_preserving := ?_
        kraus := ?_ }
    · intro X
      calc
        Matrix.trace (singleKrausSuperoperator K X) = Matrix.trace (K * X * Kᴴ) := by
              rfl
        _ = Matrix.trace ((Kᴴ * K) * X) := by
              simpa [Matrix.mul_assoc] using Matrix.trace_mul_cycle K X Kᴴ
        _ = Matrix.trace X := by
              simp [hK]
    · intro X
      simpa [singleKrausSuperoperator, Matrix.conjTranspose_mul, Matrix.mul_assoc]
    · refine ⟨PUnit, inferInstance, inferInstance, (fun _ => K), ?_, ?_⟩
      · intro X
        simp [singleKrausSuperoperator]
      · simpa using hK
  have htransport :
      superoperatorWithIdentity phys phys msg Φ (Matrix.vecMulVec ψ (star ψ)) =
        K * superoperatorWithIdentity phys phys phys Φ ρφ * Kᴴ := by
    rw [hρψ]
    simpa [K, superoperatorWithIdentity_eq_tensorWithIdentity] using
      tensorWithIdentity_right_kronecker_comm (Φ := Φ) (U := U) (X := ρφ)
  calc
    traceNormOp
        (superoperatorWithIdentity phys phys msg Φ (Matrix.vecMulVec ψ (star ψ)))
        = traceNormOp (K * superoperatorWithIdentity phys phys phys Φ ρφ * Kᴴ) := by
            rw [htransport]
    _ ≤ traceNormOp (superoperatorWithIdentity phys phys phys Φ ρφ) := by
          simpa [K, singleKrausSuperoperator] using
            (traceNormOp_quantumSuperoperator_le_of_hermitian
              (Φ := singleKrausSuperoperator K)
              (hΦ := hKquant)
              (X := superoperatorWithIdentity phys phys phys Φ ρφ)
              hmid_herm)
    _ ≤ diamondOp Φ := by
          exact traceNorm_apply_le_diamond
            (d := phys) (k := phys) (Φ := Φ) ⟨ρφ, hρφdens⟩
    _ ≤ (diamondOp ((transposeMap phys).comp T)) ^ m := hbound

/-- If the message ancilla dimension is at most the physical input dimension, then the
post-encoder pure-state bound follows from the ordinary `diamondOp` bound on the transposed
physical middle channel by expanding pure witnesses up to ancilla `phys`. -/
theorem PostEncoderPureTransposeCodeBoundData.of_diamondOp_bound_card_ge
    {phys msg : Type u}
    [Fintype phys] [DecidableEq phys] [Nonempty phys]
    [Fintype msg] [DecidableEq msg] [Nonempty msg]
    {scheme : QuantumCodingScheme phys msg}
    {T : Channel phys} {m : ℕ}
    (hcard : Fintype.card msg ≤ Fintype.card phys)
    (hbound :
      diamondOp ((transposeMap phys).comp scheme.tensorPower) ≤
        (diamondOp ((transposeMap phys).comp T)) ^ m) :
    PostEncoderPureTransposeCodeBoundData scheme T m := by
  refine { hpointwise := ?_ }
  intro ψ hψ
  obtain ⟨φ, U, hU, hφ, hφeq⟩ :=
    pure_state_expansion_to_input_dim_with_isometry
      (d := phys) (k := msg) hcard ψ hψ
  let Φ : Channel phys := (transposeMap phys).comp scheme.tensorPower
  let K : Matrix (phys × phys) (phys × msg) ℂ := (1 : Matrix phys phys ℂ) ⊗ₖ U
  have hK : Kᴴ * K = 1 := by
    dsimp [K]
    calc
      (((1 : Matrix phys phys ℂ) ⊗ₖ U)ᴴ) * ((1 : Matrix phys phys ℂ) ⊗ₖ U)
          = ((1 : Matrix phys phys ℂ)ᴴ * (1 : Matrix phys phys ℂ)) ⊗ₖ (Uᴴ * U) := by
              rw [Matrix.conjTranspose_kronecker, Matrix.mul_kronecker_mul]
      _ = (1 : Matrix phys phys ℂ) ⊗ₖ (1 : Matrix msg msg ℂ) := by
            simp [hU]
      _ = 1 := by
            simpa using (Matrix.one_kronecker_one (α := ℂ) (m := phys) (n := msg))
  let ρψ : Matrix (phys × msg) (phys × msg) ℂ := Matrix.vecMulVec ψ (star ψ)
  let ρφ : Matrix (phys × phys) (phys × phys) ℂ := Matrix.vecMulVec φ (star φ)
  have hρψdens : IsDensityState ρψ := by
    refine ⟨?_, ?_⟩
    · simpa [ρψ] using Matrix.posSemidef_vecMulVec_self_star ψ
    · rw [show Matrix.trace ρψ = Matrix.trace (Matrix.vecMulVec ψ (star ψ)) by rfl]
      rw [Matrix.trace_vecMulVec, hψ]
  have hρφdens : IsDensityState ρφ := by
    refine ⟨?_, ?_⟩
    · simpa [ρφ] using Matrix.posSemidef_vecMulVec_self_star φ
    · rw [show Matrix.trace ρφ = Matrix.trace (Matrix.vecMulVec φ (star φ)) by rfl]
      rw [Matrix.trace_vecMulVec, hφ]
  have hφvec : φ = K *ᵥ ψ := by
    funext ij
    rcases ij with ⟨i, j⟩
    rw [hφeq]
    simp [K, Matrix.mulVec, dotProduct, Matrix.kroneckerMap_apply, Matrix.one_apply,
      Fintype.sum_prod_type, mul_comm]
  have hρφ :
      ρφ = K * ρψ * Kᴴ := by
    dsimp [ρφ]
    rw [hφvec]
    calc
      Matrix.vecMulVec (K *ᵥ ψ) (star (K *ᵥ ψ))
          = K * Matrix.vecMulVec ψ (star (K *ᵥ ψ)) := by
              rw [Matrix.mul_vecMulVec]
      _ = K * Matrix.vecMulVec ψ (Matrix.vecMul (star ψ) Kᴴ) := by
            rw [Matrix.star_mulVec]
      _ = K * (Matrix.vecMulVec ψ (star ψ) * Kᴴ) := by
            rw [← Matrix.vecMulVec_mul]
      _ = K * ρψ * Kᴴ := by
            simp [ρψ, Matrix.mul_assoc]
  have hΦ_hpres : IsHermiticityPreserving Φ := by
    exact hermiticityPreserving_comp
      (Ψ := transposeMap phys)
      (Φ := scheme.tensorPower)
      (transposeMap_hermiticityPreserving (d := phys))
      scheme.htensorPower.hermiticity_preserving
  have hanc_hpres_msg :
      IsHermiticityPreserving (superoperatorWithIdentity phys phys msg Φ) := by
    exact superoperatorWithIdentity_hermiticityPreserving
      (din := phys) (dout := phys) (k := msg) (Φ := Φ) hΦ_hpres
  have hmid_herm :
      Matrix.IsHermitian (superoperatorWithIdentity phys phys msg Φ ρψ) := by
    unfold Matrix.IsHermitian
    calc
      (superoperatorWithIdentity phys phys msg Φ ρψ)ᴴ
          = superoperatorWithIdentity phys phys msg Φ ρψᴴ := by
              symm
              exact hanc_hpres_msg ρψ
      _ = superoperatorWithIdentity phys phys msg Φ ρψ := by
            rw [hρψdens.1.isHermitian.eq]
  have htransport :
      superoperatorWithIdentity phys phys phys Φ ρφ =
        K * superoperatorWithIdentity phys phys msg Φ ρψ * Kᴴ := by
    rw [hρφ]
    simpa [K, superoperatorWithIdentity_eq_tensorWithIdentity] using
      tensorWithIdentity_right_kronecker_comm (Φ := Φ) (U := U) (X := ρψ)
  calc
    traceNormOp
        (superoperatorWithIdentity phys phys msg Φ ρψ)
        = traceNormOp
            (K * superoperatorWithIdentity phys phys msg Φ ρψ * Kᴴ) := by
              symm
              exact traceNormOp_isometric_conj_eq_of_hermitian hK hmid_herm
    _ = traceNormOp (superoperatorWithIdentity phys phys phys Φ ρφ) := by
          rw [← htransport]
    _ ≤ diamondOp Φ := by
          exact traceNorm_apply_le_diamond
            (d := phys) (k := phys) (Φ := Φ) ⟨ρφ, hρφdens⟩
    _ ≤ (diamondOp ((transposeMap phys).comp T)) ^ m := hbound

/-- In the literal same-type case `msg = phys`, the post-encoder pointwise bound follows
directly from the ordinary `diamondOp` bound on the transposed physical middle channel. -/
theorem PostEncoderTransposeCodeBoundData.of_diamondOp_bound_same_type
    {phys : Type u}
    [Fintype phys] [DecidableEq phys] [Nonempty phys]
    {scheme : QuantumCodingScheme phys phys}
    {T : Channel phys} {m : ℕ}
    (hbound :
      diamondOp ((transposeMap phys).comp scheme.tensorPower) ≤
        (diamondOp ((transposeMap phys).comp T)) ^ m) :
    PostEncoderTransposeCodeBoundData scheme T m := by
  refine { hpointwise := ?_ }
  intro σ
  exact le_trans
    (traceNorm_apply_le_diamond
      (d := phys) (k := phys)
      (Φ := ((transposeMap phys).comp scheme.tensorPower)) σ)
    (by simpa [diamondOp, diamondNorm, diamondNormAt] using hbound)

/-- In the same-dimension case `msg = phys`, the remaining fixed-ancilla bound is exactly the
ordinary `diamondOp` bound by definition. -/
theorem PostEncoderDiamondAtBoundData.of_diamondOp_bound_same_type
    {phys : Type u}
    [Fintype phys] [DecidableEq phys] [Nonempty phys]
    {scheme : QuantumCodingScheme phys phys}
    {T : Channel phys} {m : ℕ}
    (hbound :
      diamondOp ((transposeMap phys).comp scheme.tensorPower) ≤
        (diamondOp ((transposeMap phys).comp T)) ^ m) :
    PostEncoderDiamondAtBoundData scheme T m := by
  refine { hbound := ?_ }
  simpa [diamondOp, diamondNorm, diamondNormAt] using hbound

/-- If the message ancilla type is merely equivalent to the physical input type, then the
remaining fixed-ancilla bound also reduces to the ordinary `diamondOp` bound by reindexing
the ancilla witness space. -/
theorem PostEncoderDiamondAtBoundData.of_diamondOp_bound_equiv
    {phys msg : Type u}
    [Fintype phys] [DecidableEq phys] [Nonempty phys]
    [Fintype msg] [DecidableEq msg] [Nonempty msg]
    {scheme : QuantumCodingScheme phys msg}
    {T : Channel phys} {m : ℕ}
    (e : msg ≃ phys)
    (hbound :
      diamondOp ((transposeMap phys).comp scheme.tensorPower) ≤
        (diamondOp ((transposeMap phys).comp T)) ^ m) :
    PostEncoderDiamondAtBoundData scheme T m := by
  refine { hbound := ?_ }
  refine diamondNormAt_le_of_pointwise
    (d := phys) (k := msg)
    ((transposeMap phys).comp scheme.tensorPower)
    ((diamondOp ((transposeMap phys).comp T)) ^ m) ?_
  intro ρ
  let E : phys × msg ≃ phys × phys := Equiv.prodCongr (Equiv.refl phys) e
  let ρ' : DensityState (phys × phys) := ⟨Matrix.reindex E E ρ.1, isDensityState_reindex E ρ.2⟩
  calc
    traceNormOp (tensorWithIdentity phys msg ((transposeMap phys).comp scheme.tensorPower) ρ.1)
        =
      traceNormOp
        (Matrix.reindex E E
          (tensorWithIdentity phys msg ((transposeMap phys).comp scheme.tensorPower) ρ.1)) := by
            symm
            exact traceNormOp_reindex E
              (tensorWithIdentity phys msg ((transposeMap phys).comp scheme.tensorPower) ρ.1)
    _ =
      traceNormOp
        (tensorWithIdentity phys phys ((transposeMap phys).comp scheme.tensorPower) ρ'.1) := by
          rw [tensorWithIdentity_reindex_ancilla_eq
            (d := phys) (k₁ := msg) (k₂ := phys)
            e ((transposeMap phys).comp scheme.tensorPower) ρ.1]
    _ ≤ diamondOp ((transposeMap phys).comp scheme.tensorPower) := by
          exact traceNorm_apply_le_diamond
            (d := phys) (k := phys)
            (Φ := ((transposeMap phys).comp scheme.tensorPower)) ρ'
    _ ≤ (diamondOp ((transposeMap phys).comp T)) ^ m := hbound

/-- If the message ancilla has the same cardinality as the physical input type, then the
remaining fixed-ancilla bound also reduces to the ordinary `diamondOp` bound by choosing
an ancilla equivalence. -/
theorem PostEncoderDiamondAtBoundData.of_diamondOp_bound_card_eq
    {phys msg : Type u}
    [Fintype phys] [DecidableEq phys] [Nonempty phys]
    [Fintype msg] [DecidableEq msg] [Nonempty msg]
    {scheme : QuantumCodingScheme phys msg}
    {T : Channel phys} {m : ℕ}
    (hcard : Fintype.card msg = Fintype.card phys)
    (hbound :
      diamondOp ((transposeMap phys).comp scheme.tensorPower) ≤
        (diamondOp ((transposeMap phys).comp T)) ^ m) :
    PostEncoderDiamondAtBoundData scheme T m := by
  exact PostEncoderDiamondAtBoundData.of_diamondOp_bound_equiv
    (scheme := scheme) (T := T) (m := m) (Fintype.equivOfCardEq hcard) hbound

/-- The decoder-reduced pointwise bound follows directly from the fixed-ancilla
diamond-norm bound for the transposed physical middle channel. -/
theorem ReducedTransposeCodeBoundData.of_diamondAt_bound
    {phys msg : Type u}
    [Fintype phys] [DecidableEq phys]
    [Fintype msg] [DecidableEq msg] [Nonempty msg]
    {scheme : QuantumCodingScheme phys msg}
    {T : Channel phys} {m : ℕ}
    (hbound : PostEncoderDiamondAtBoundData scheme T m) :
    ReducedTransposeCodeBoundData scheme T m := by
  exact ReducedTransposeCodeBoundData.of_post_encoder_reduction
    (PostEncoderTransposeCodeBoundData.of_diamondAt_bound hbound)

/-- In the literal same-type case `msg = phys`, the decoder-reduced pointwise bound follows
directly from the ordinary `diamondOp` bound on the transposed physical middle channel. -/
theorem ReducedTransposeCodeBoundData.of_diamondOp_bound_same_type
    {phys : Type u}
    [Fintype phys] [DecidableEq phys] [Nonempty phys]
    {scheme : QuantumCodingScheme phys phys}
    {T : Channel phys} {m : ℕ}
    (hbound :
      diamondOp ((transposeMap phys).comp scheme.tensorPower) ≤
        (diamondOp ((transposeMap phys).comp T)) ^ m) :
    ReducedTransposeCodeBoundData scheme T m := by
  exact ReducedTransposeCodeBoundData.of_diamondAt_bound
    (PostEncoderDiamondAtBoundData.of_diamondOp_bound_same_type hbound)

/-- If the message ancilla has the same cardinality as the physical input type, then the
decoder-reduced pointwise bound follows from the ordinary `diamondOp` bound on the
transposed physical middle channel. -/
theorem ReducedTransposeCodeBoundData.of_diamondOp_bound_card_eq
    {phys msg : Type u}
    [Fintype phys] [DecidableEq phys] [Nonempty phys]
    [Fintype msg] [DecidableEq msg] [Nonempty msg]
    {scheme : QuantumCodingScheme phys msg}
    {T : Channel phys} {m : ℕ}
    (hcard : Fintype.card msg = Fintype.card phys)
    (hbound :
      diamondOp ((transposeMap phys).comp scheme.tensorPower) ≤
        (diamondOp ((transposeMap phys).comp T)) ^ m) :
    ReducedTransposeCodeBoundData scheme T m := by
  exact ReducedTransposeCodeBoundData.of_diamondAt_bound
    (PostEncoderDiamondAtBoundData.of_diamondOp_bound_card_eq hcard hbound)

/-- The original `htranspose_code_bound` assumption is implied by the decoder-reduced
pointwise bound obtained from the standard Holevo-Werner factorization
`Θ ∘ D = D̄ ∘ Θ`. -/
theorem transpose_code_bound_of_decoder_reduction
    {phys msg : Type u}
    [Fintype phys] [DecidableEq phys]
    [Fintype msg] [DecidableEq msg] [Nonempty msg]
    {scheme : QuantumCodingScheme phys msg}
    {T : Channel phys} {m : ℕ}
    (hred : ReducedTransposeCodeBoundData scheme T m) :
    diamondOp ((transposeMap msg).comp scheme.effective) ≤
      (diamondOp ((transposeMap phys).comp T)) ^ m := by
  refine diamond_le_of_pointwise_nonempty
    (d := msg) (Φ := (transposeMap msg).comp scheme.effective)
    ((diamondOp ((transposeMap phys).comp T)) ^ m) ?_
  intro ρ
  rw [traceNorm_transpose_effective_eq_conjugated_decoder
    scheme.encoder scheme.decoder scheme.tensorPower ρ]
  exact hred.hpointwise ρ

/-- Packaged `HolevoWernerCodeData` built from the decoder-reduced pointwise bound and the
usual error identity. This is the cleanest remaining assumption currently supported by the
repo for the finite-error corollary. -/
theorem HolevoWernerCodeData.of_decoder_reduction
    {phys msg : Type u}
    [Fintype phys] [DecidableEq phys]
    [Fintype msg] [DecidableEq msg] [Nonempty msg]
    {scheme : QuantumCodingScheme phys msg}
    {T : Channel phys} {m : ℕ} {ε : ℝ}
    (hred : ReducedTransposeCodeBoundData scheme T m)
    (herror : ε = (1 / 2 : ℝ) * diamondOp (idMinus scheme.effective)) :
    HolevoWernerCodeData scheme T m ε := by
  refine
    { htranspose_code_bound := transpose_code_bound_of_decoder_reduction hred
      herror := herror }

/-- Packaged `HolevoWernerCodeData` built directly from the pure-state post-encoder pointwise
bound for the ancilla-extended transposed physical middle channel. -/
theorem HolevoWernerCodeData.of_pure_state_bound
    {phys msg : Type u}
    [Fintype phys] [DecidableEq phys]
    [Fintype msg] [DecidableEq msg] [Nonempty msg]
    {scheme : QuantumCodingScheme phys msg}
    {T : Channel phys} {m : ℕ} {ε : ℝ}
    (hpure : PostEncoderPureTransposeCodeBoundData scheme T m)
    (herror : ε = (1 / 2 : ℝ) * diamondOp (idMinus scheme.effective)) :
    HolevoWernerCodeData scheme T m ε := by
  exact HolevoWernerCodeData.of_decoder_reduction
    (ReducedTransposeCodeBoundData.of_post_encoder_reduction
      (PostEncoderTransposeCodeBoundData.of_pure_state_bound hpure))
    herror

/-- Packaged `HolevoWernerCodeData` from the ordinary `diamondOp` bound when the message
ancilla dimension is at least the physical input dimension. -/
theorem HolevoWernerCodeData.of_diamondOp_bound_card_le
    {phys msg : Type u}
    [Fintype phys] [DecidableEq phys] [Nonempty phys]
    [Fintype msg] [DecidableEq msg] [Nonempty msg]
    {scheme : QuantumCodingScheme phys msg}
    {T : Channel phys} {m : ℕ} {ε : ℝ}
    (hcard : Fintype.card phys ≤ Fintype.card msg)
    (hbound :
      diamondOp ((transposeMap phys).comp scheme.tensorPower) ≤
        (diamondOp ((transposeMap phys).comp T)) ^ m)
    (herror : ε = (1 / 2 : ℝ) * diamondOp (idMinus scheme.effective)) :
    HolevoWernerCodeData scheme T m ε := by
  exact HolevoWernerCodeData.of_pure_state_bound
    (PostEncoderPureTransposeCodeBoundData.of_diamondOp_bound_card_le hcard hbound)
    herror

/-- Packaged `HolevoWernerCodeData` from the ordinary `diamondOp` bound when the message
ancilla dimension is at most the physical input dimension. -/
theorem HolevoWernerCodeData.of_diamondOp_bound_card_ge
    {phys msg : Type u}
    [Fintype phys] [DecidableEq phys] [Nonempty phys]
    [Fintype msg] [DecidableEq msg] [Nonempty msg]
    {scheme : QuantumCodingScheme phys msg}
    {T : Channel phys} {m : ℕ} {ε : ℝ}
    (hcard : Fintype.card msg ≤ Fintype.card phys)
    (hbound :
      diamondOp ((transposeMap phys).comp scheme.tensorPower) ≤
        (diamondOp ((transposeMap phys).comp T)) ^ m)
    (herror : ε = (1 / 2 : ℝ) * diamondOp (idMinus scheme.effective)) :
    HolevoWernerCodeData scheme T m ε := by
  exact HolevoWernerCodeData.of_pure_state_bound
    (PostEncoderPureTransposeCodeBoundData.of_diamondOp_bound_card_ge hcard hbound)
    herror

/-- Packaged `HolevoWernerCodeData` from the ordinary `diamondOp` bound on the transposed
physical middle channel, with no extra cardinality assumptions. -/
theorem HolevoWernerCodeData.of_diamondOp_bound
    {phys msg : Type u}
    [Fintype phys] [DecidableEq phys] [Nonempty phys]
    [Fintype msg] [DecidableEq msg] [Nonempty msg]
    {scheme : QuantumCodingScheme phys msg}
    {T : Channel phys} {m : ℕ} {ε : ℝ}
    (hbound :
      diamondOp ((transposeMap phys).comp scheme.tensorPower) ≤
        (diamondOp ((transposeMap phys).comp T)) ^ m)
    (herror : ε = (1 / 2 : ℝ) * diamondOp (idMinus scheme.effective)) :
    HolevoWernerCodeData scheme T m ε := by
  rcases Nat.le_total (Fintype.card phys) (Fintype.card msg) with h | h
  · exact HolevoWernerCodeData.of_diamondOp_bound_card_le h hbound herror
  · exact HolevoWernerCodeData.of_diamondOp_bound_card_ge h hbound herror

/-- Packaged `HolevoWernerCodeData` built directly from the post-encoder pointwise bound
for the ancilla-extended transposed physical middle channel. -/
theorem HolevoWernerCodeData.of_post_encoder_reduction
    {phys msg : Type u}
    [Fintype phys] [DecidableEq phys]
    [Fintype msg] [DecidableEq msg] [Nonempty msg]
    {scheme : QuantumCodingScheme phys msg}
    {T : Channel phys} {m : ℕ} {ε : ℝ}
    (hpost : PostEncoderTransposeCodeBoundData scheme T m)
    (herror : ε = (1 / 2 : ℝ) * diamondOp (idMinus scheme.effective)) :
    HolevoWernerCodeData scheme T m ε := by
  exact HolevoWernerCodeData.of_decoder_reduction
    (ReducedTransposeCodeBoundData.of_post_encoder_reduction hpost) herror

/-- Packaged `HolevoWernerCodeData` built directly from the fixed-ancilla
diamond-norm bound on the transposed physical middle channel. -/
theorem HolevoWernerCodeData.of_diamondAt_bound
    {phys msg : Type u}
    [Fintype phys] [DecidableEq phys]
    [Fintype msg] [DecidableEq msg] [Nonempty msg]
    {scheme : QuantumCodingScheme phys msg}
    {T : Channel phys} {m : ℕ} {ε : ℝ}
    (hbound : PostEncoderDiamondAtBoundData scheme T m)
    (herror : ε = (1 / 2 : ℝ) * diamondOp (idMinus scheme.effective)) :
    HolevoWernerCodeData scheme T m ε := by
  exact HolevoWernerCodeData.of_decoder_reduction
    (ReducedTransposeCodeBoundData.of_diamondAt_bound hbound) herror

/-- Packaged `HolevoWernerCodeData` from the ordinary `diamondOp` bound in the literal
same-type case `msg = phys`. -/
theorem HolevoWernerCodeData.of_diamondOp_bound_same_type
    {phys : Type u}
    [Fintype phys] [DecidableEq phys] [Nonempty phys]
    {scheme : QuantumCodingScheme phys phys}
    {T : Channel phys} {m : ℕ} {ε : ℝ}
    (hbound :
      diamondOp ((transposeMap phys).comp scheme.tensorPower) ≤
        (diamondOp ((transposeMap phys).comp T)) ^ m)
    (herror : ε = (1 / 2 : ℝ) * diamondOp (idMinus scheme.effective)) :
    HolevoWernerCodeData scheme T m ε := by
  exact HolevoWernerCodeData.of_diamondAt_bound
    (PostEncoderDiamondAtBoundData.of_diamondOp_bound_same_type hbound) herror

/-- Packaged `HolevoWernerCodeData` from the ordinary `diamondOp` bound when the message
type has the same cardinality as the physical input type. -/
theorem HolevoWernerCodeData.of_diamondOp_bound_card_eq
    {phys msg : Type u}
    [Fintype phys] [DecidableEq phys] [Nonempty phys]
    [Fintype msg] [DecidableEq msg] [Nonempty msg]
    {scheme : QuantumCodingScheme phys msg}
    {T : Channel phys} {m : ℕ} {ε : ℝ}
    (hcard : Fintype.card msg = Fintype.card phys)
    (hbound :
      diamondOp ((transposeMap phys).comp scheme.tensorPower) ≤
        (diamondOp ((transposeMap phys).comp T)) ^ m)
    (herror : ε = (1 / 2 : ℝ) * diamondOp (idMinus scheme.effective)) :
    HolevoWernerCodeData scheme T m ε := by
  exact HolevoWernerCodeData.of_diamondAt_bound
    (PostEncoderDiamondAtBoundData.of_diamondOp_bound_card_eq hcard hbound) herror

/-- The specific replacement step coming from Remark 1 / Theorem 1. -/
theorem holevo_werner_improved_linear_bound
    {phys msg : Type u}
    [Fintype phys] [DecidableEq phys]
    [Fintype msg] [DecidableEq msg] [Nonempty msg]
    {scheme : QuantumCodingScheme phys msg}
    {T : Channel phys} {m : ℕ} {ε : ℝ}
    (hdata : HolevoWernerCodeData scheme T m ε) :
    (1 - Real.sqrt 2 * ε) * (Fintype.card msg : ℝ) ≤
      (diamondOp ((transposeMap phys).comp T)) ^ m := by
  let heff : HolevoWernerEffectiveData scheme.effective T m ε :=
    { heffective := scheme.effective_isQuantumChannel
      htranspose_code_bound := hdata.htranspose_code_bound
      herror := hdata.herror }
  exact holevo_werner_linear_bound_of_replacement_argument T m ε (Real.sqrt 2)
    hdata (holevo_werner_improved_error_term_bound_effective heff)

/-- Step 3 of the paper logic, written directly at the level of the effective channel. -/
theorem holevo_werner_improved_linear_bound_effective
    {phys msg : Type u}
    [Fintype phys] [DecidableEq phys]
    [Fintype msg] [DecidableEq msg] [Nonempty msg]
    {effective : Channel msg}
    {T : Channel phys} {m : ℕ} {ε : ℝ}
    (hdata : HolevoWernerEffectiveData effective T m ε) :
    (1 - Real.sqrt 2 * ε) * (Fintype.card msg : ℝ) ≤
      (diamondOp ((transposeMap phys).comp T)) ^ m := by
  exact holevo_werner_linear_bound_of_replacement_argument_effective T m ε (Real.sqrt 2)
    hdata (holevo_werner_improved_error_term_bound_effective hdata)

/-- Improved finite-error Holevo-Werner linear converse when quantumness is supplied only
for the effective channel. This is the form directly consumed by the current endmatter
corollary wrapper. -/
theorem holevo_werner_improved_linear_bound_of_quantum_effective
    {phys msg : Type u}
    [Fintype phys] [DecidableEq phys]
    [Fintype msg] [DecidableEq msg] [Nonempty msg]
    (T : Channel phys) (m : ℕ)
    (encoder : Superoperator msg phys)
    (decoder : Superoperator phys msg)
    (tensorPower : Channel phys)
    (ε : ℝ)
    (heffective : IsQuantumChannel (effectiveChannel encoder decoder tensorPower))
    (htranspose_code_bound :
      diamondOp ((transposeMap msg).comp (effectiveChannel encoder decoder tensorPower)) ≤
        (diamondOp ((transposeMap phys).comp T)) ^ m)
    (herror :
      ε = (1 / 2 : ℝ) * diamondOp (idMinus (effectiveChannel encoder decoder tensorPower))) :
    (1 - Real.sqrt 2 * ε) * (Fintype.card msg : ℝ) ≤
      (diamondOp ((transposeMap phys).comp T)) ^ m := by
  let hdata : HolevoWernerEffectiveData
      (effectiveChannel encoder decoder tensorPower) T m ε :=
    { heffective := heffective
      htranspose_code_bound := htranspose_code_bound
      herror := herror }
  exact holevo_werner_improved_linear_bound_effective hdata

/-- Step 3 of the paper logic: plugging the improved replacement into the original
Holevo-Werner proof gives the improved finite-error converse. -/
theorem holevo_werner_improved_bound
    {phys msg : Type u}
    [Fintype phys] [DecidableEq phys]
    [Fintype msg] [DecidableEq msg] [Nonempty msg]
    {scheme : QuantumCodingScheme phys msg}
    {T : Channel phys} {m : ℕ} {ε : ℝ}
    (hdata : HolevoWernerCodeData scheme T m ε)
    (hm : 0 < m) (hε : ε < 1 / Real.sqrt 2) :
    Real.logb 2 (Fintype.card msg : ℝ) / (m : ℝ) ≤
      Real.logb 2 (diamondOp ((transposeMap phys).comp T)) +
        (1 / (m : ℝ)) * Real.logb 2 (1 / (1 - Real.sqrt 2 * ε)) := by
  let heff : HolevoWernerEffectiveData scheme.effective T m ε :=
    { heffective := scheme.effective_isQuantumChannel
      htranspose_code_bound := hdata.htranspose_code_bound
      herror := hdata.herror }
  exact holevo_werner_bound_of_replacement_argument T m ε (Real.sqrt 2)
    hdata (holevo_werner_improved_error_term_bound_effective heff)
    hm hε (by positivity)

/-- Logarithmic form of the improved finite-error Holevo-Werner converse at the level of
the effective channel. -/
theorem holevo_werner_improved_bound_effective
    {phys msg : Type u}
    [Fintype phys] [DecidableEq phys]
    [Fintype msg] [DecidableEq msg] [Nonempty msg]
    {effective : Channel msg}
    {T : Channel phys} {m : ℕ} {ε : ℝ}
    (hdata : HolevoWernerEffectiveData effective T m ε)
    (hm : 0 < m) (hε : ε < 1 / Real.sqrt 2) :
    Real.logb 2 (Fintype.card msg : ℝ) / (m : ℝ) ≤
      Real.logb 2 (diamondOp ((transposeMap phys).comp T)) +
        (1 / (m : ℝ)) * Real.logb 2 (1 / (1 - Real.sqrt 2 * ε)) := by
  exact holevo_werner_bound_of_replacement_argument_effective T m ε (Real.sqrt 2)
    hdata (holevo_werner_improved_error_term_bound_effective hdata)
    hm hε (by positivity)

/-- Logarithmic form of the improved finite-error Holevo-Werner converse when quantumness
is supplied only for the effective channel. -/
theorem holevo_werner_improved_bound_of_quantum_effective
    {phys msg : Type u}
    [Fintype phys] [DecidableEq phys]
    [Fintype msg] [DecidableEq msg] [Nonempty msg]
    (T : Channel phys) (m : ℕ)
    (encoder : Superoperator msg phys)
    (decoder : Superoperator phys msg)
    (tensorPower : Channel phys)
    (ε : ℝ)
    (heffective : IsQuantumChannel (effectiveChannel encoder decoder tensorPower))
    (htranspose_code_bound :
      diamondOp ((transposeMap msg).comp (effectiveChannel encoder decoder tensorPower)) ≤
        (diamondOp ((transposeMap phys).comp T)) ^ m)
    (herror :
      ε = (1 / 2 : ℝ) * diamondOp (idMinus (effectiveChannel encoder decoder tensorPower)))
    (hm : 0 < m) (hε : ε < 1 / Real.sqrt 2) :
    Real.logb 2 (Fintype.card msg : ℝ) / (m : ℝ) ≤
      Real.logb 2 (diamondOp ((transposeMap phys).comp T)) +
        (1 / (m : ℝ)) * Real.logb 2 (1 / (1 - Real.sqrt 2 * ε)) := by
  let hdata : HolevoWernerEffectiveData
      (effectiveChannel encoder decoder tensorPower) T m ε :=
    { heffective := heffective
      htranspose_code_bound := htranspose_code_bound
      herror := herror }
  exact holevo_werner_improved_bound_effective hdata hm hε

/-- For a block coding scheme, the coded transpose bound is implied by the ordinary
`diamondOp` bound on the transposed block middle channel itself. -/
theorem effective_transpose_bound_of_block_middle_diamondOp_bound
    {block msg : Type u}
    [Fintype block] [DecidableEq block] [Nonempty block]
    [Fintype msg] [DecidableEq msg] [Nonempty msg]
    (encoder : Superoperator msg block)
    (decoder : Superoperator block msg)
    (tensorPower : Channel block)
    (hencoder : IsQuantumSuperoperator encoder)
    (hdecoder : IsQuantumSuperoperator decoder)
    (htensorPower : IsQuantumChannel tensorPower) :
    diamondOp ((transposeMap msg).comp (effectiveChannel encoder decoder tensorPower)) ≤
      diamondOp ((transposeMap block).comp tensorPower) := by
  let scheme : QuantumCodingScheme block msg :=
    { encoder := encoder
      decoder := decoder
      tensorPower := tensorPower
      hencoder := hencoder
      hdecoder := hdecoder
      htensorPower := htensorPower }
  let ε : ℝ := (1 / 2 : ℝ) * diamondOp (idMinus scheme.effective)
  have hbound :
      diamondOp ((transposeMap block).comp scheme.tensorPower) ≤
        (diamondOp ((transposeMap block).comp tensorPower)) ^ (1 : ℕ) := by
    simpa [scheme, pow_one] using
      (le_rfl : diamondOp ((transposeMap block).comp tensorPower) ≤
        diamondOp ((transposeMap block).comp tensorPower))
  have hdata :
      HolevoWernerCodeData scheme tensorPower 1 ε :=
    HolevoWernerCodeData.of_diamondOp_bound
      (scheme := scheme) (T := tensorPower) (m := 1) (ε := ε)
      hbound rfl
  simpa [scheme, QuantumCodingScheme.effective, effectiveChannel, pow_one] using
    hdata.htranspose_code_bound

/-- Improved finite-error Holevo-Werner converse for a block coding scheme:
encoder/decoder and the `m`-use physical middle channel live on an arbitrary block space,
while the converse rate is controlled by a single-use base channel `T`. -/
theorem holevo_werner_improved_bound_of_block_tensorPower_diamondOp_bound
    {base block msg : Type u}
    [Fintype base] [DecidableEq base]
    [Fintype block] [DecidableEq block]
    [Fintype msg] [DecidableEq msg] [Nonempty msg]
    (T : Channel base) (m : ℕ)
    (encoder : Superoperator msg block)
    (decoder : Superoperator block msg)
    (tensorPower : Channel block)
    (ε : ℝ)
    (heffective : IsQuantumChannel (effectiveChannel encoder decoder tensorPower))
    (htranspose_code_bound :
      diamondOp ((transposeMap msg).comp (effectiveChannel encoder decoder tensorPower)) ≤
        (diamondOp ((transposeMap base).comp T)) ^ m)
    (herror :
      ε =
        (1 / 2 : ℝ) *
          diamondOp (idMinus (effectiveChannel encoder decoder tensorPower)))
    (hm : 0 < m) (hε : ε < 1 / Real.sqrt 2) :
    Real.logb 2 (Fintype.card msg : ℝ) / (m : ℝ) ≤
      Real.logb 2 (diamondOp ((transposeMap base).comp T)) +
        (1 / (m : ℝ)) * Real.logb 2 (1 / (1 - Real.sqrt 2 * ε)) := by
  let hdata : HolevoWernerEffectiveData
      (effectiveChannel encoder decoder tensorPower) T m ε :=
    { heffective := heffective
      htranspose_code_bound := htranspose_code_bound
      herror := herror }
  exact holevo_werner_improved_bound_effective hdata hm hε

/-- Improved finite-error Holevo-Werner converse for a block coding scheme from the ordinary
`diamondOp` bound on the transposed block middle channel. -/
theorem holevo_werner_improved_bound_of_block_middle_diamondOp_bound
    {base block msg : Type u}
    [Fintype base] [DecidableEq base]
    [Fintype block] [DecidableEq block] [Nonempty block]
    [Fintype msg] [DecidableEq msg] [Nonempty msg]
    (T : Channel base) (m : ℕ)
    (encoder : Superoperator msg block)
    (decoder : Superoperator block msg)
    (tensorPower : Channel block)
    (ε : ℝ)
    (hencoder : IsQuantumSuperoperator encoder)
    (hdecoder : IsQuantumSuperoperator decoder)
    (htensorPower : IsQuantumChannel tensorPower)
    (hbound :
      diamondOp ((transposeMap block).comp tensorPower) ≤
        (diamondOp ((transposeMap base).comp T)) ^ m)
    (herror :
      ε =
        (1 / 2 : ℝ) *
          diamondOp (idMinus (effectiveChannel encoder decoder tensorPower)))
    (hm : 0 < m) (hε : ε < 1 / Real.sqrt 2) :
    Real.logb 2 (Fintype.card msg : ℝ) / (m : ℝ) ≤
      Real.logb 2 (diamondOp ((transposeMap base).comp T)) +
        (1 / (m : ℝ)) * Real.logb 2 (1 / (1 - Real.sqrt 2 * ε)) := by
  have heffective : IsQuantumChannel (effectiveChannel encoder decoder tensorPower) :=
    effectiveChannel_isQuantumChannel hencoder htensorPower hdecoder
  have hcoded :
      diamondOp ((transposeMap msg).comp (effectiveChannel encoder decoder tensorPower)) ≤
        (diamondOp ((transposeMap base).comp T)) ^ m := by
    exact le_trans
      (effective_transpose_bound_of_block_middle_diamondOp_bound
        encoder decoder tensorPower hencoder hdecoder htensorPower)
      hbound
  exact holevo_werner_improved_bound_of_block_tensorPower_diamondOp_bound
    T m encoder decoder tensorPower ε heffective hcoded herror hm hε

/-- Improved finite-error Holevo-Werner linear converse for a block coding scheme from the
ordinary `diamondOp` bound on the transposed block middle channel. -/
theorem holevo_werner_improved_linear_bound_of_block_middle_diamondOp_bound
    {base block msg : Type u}
    [Fintype base] [DecidableEq base]
    [Fintype block] [DecidableEq block] [Nonempty block]
    [Fintype msg] [DecidableEq msg] [Nonempty msg]
    (T : Channel base) (m : ℕ)
    (encoder : Superoperator msg block)
    (decoder : Superoperator block msg)
    (tensorPower : Channel block)
    (ε : ℝ)
    (hencoder : IsQuantumSuperoperator encoder)
    (hdecoder : IsQuantumSuperoperator decoder)
    (htensorPower : IsQuantumChannel tensorPower)
    (hbound :
      diamondOp ((transposeMap block).comp tensorPower) ≤
        (diamondOp ((transposeMap base).comp T)) ^ m)
    (herror :
      ε =
        (1 / 2 : ℝ) *
          diamondOp (idMinus (effectiveChannel encoder decoder tensorPower))) :
    (1 - Real.sqrt 2 * ε) * (Fintype.card msg : ℝ) ≤
      (diamondOp ((transposeMap base).comp T)) ^ m := by
  have heffective : IsQuantumChannel (effectiveChannel encoder decoder tensorPower) :=
    effectiveChannel_isQuantumChannel hencoder htensorPower hdecoder
  have hcoded :
      diamondOp ((transposeMap msg).comp (effectiveChannel encoder decoder tensorPower)) ≤
        (diamondOp ((transposeMap base).comp T)) ^ m := by
    exact le_trans
      (effective_transpose_bound_of_block_middle_diamondOp_bound
        encoder decoder tensorPower hencoder hdecoder htensorPower)
      hbound
  let hdata : HolevoWernerEffectiveData
      (effectiveChannel encoder decoder tensorPower) T m ε :=
    { heffective := heffective
      htranspose_code_bound := hcoded
      herror := herror }
  exact holevo_werner_improved_linear_bound_effective hdata

/-- Paper-facing improved converse for a block coding scheme from the ordinary `diamondOp`
bound on the transposed block middle channel. -/
theorem paper_holevo_werner_improved_converse_of_block_middle_diamondOp_bound
    {base block msg : Type u}
    [Fintype base] [DecidableEq base]
    [Fintype block] [DecidableEq block] [Nonempty block]
    [Fintype msg] [DecidableEq msg] [Nonempty msg]
    (T : Channel base) (m : ℕ)
    (encoder : Superoperator msg block)
    (decoder : Superoperator block msg)
    (tensorPower : Channel block)
    (ε : ℝ)
    (hencoder : IsQuantumSuperoperator encoder)
    (hdecoder : IsQuantumSuperoperator decoder)
    (htensorPower : IsQuantumChannel tensorPower)
    (hbound :
      diamondOp ((transposeMap block).comp tensorPower) ≤
        (diamondOp ((transposeMap base).comp T)) ^ m)
    (herror :
      ε =
        (1 / 2 : ℝ) *
          diamondOp (idMinus (effectiveChannel encoder decoder tensorPower)))
    (hm : 0 < m) (hε : ε < 1 / Real.sqrt 2) :
    Real.logb 2 (Fintype.card msg : ℝ) / (m : ℝ) ≤
      Real.logb 2 (diamondOp ((transposeMap base).comp T)) +
        (1 / (m : ℝ)) * Real.logb 2 (1 / (1 - Real.sqrt 2 * ε)) := by
  exact holevo_werner_improved_bound_of_block_middle_diamondOp_bound
    T m encoder decoder tensorPower ε hencoder hdecoder htensorPower hbound herror hm hε

/-- Ordinary `diamondOp` bound for the concrete recursive tensor-power channel. -/
theorem diamondOp_transpose_tensorPowerChannel_le_pow
    {phys : Type u}
    [Fintype phys] [DecidableEq phys] [Nonempty phys]
    (T : Channel phys) (hT : IsQuantumChannel T) :
    ∀ m : ℕ,
      diamondOp ((transposeMap (TensorPowerType phys m)).comp (tensorPowerChannel T m)) ≤
        (diamondOp ((transposeMap phys).comp T)) ^ m
  | 0 => by
      simpa [TensorPowerType, tensorPowerChannel_zero_eq] using
        (show diamondOp (transposeMap PUnit) ≤ (1 : ℝ) by
          rw [transpose_diamond_exact (d := PUnit)]
          norm_num)
  | n + 1 => by
      let block := TensorPowerType phys n
      let baseΦ : Channel phys := (transposeMap phys).comp T
      let Ωn : Channel block := (transposeMap block).comp (tensorPowerChannel T n)
      let Ωnext : Channel (block × phys) :=
        (transposeMap (block × phys)).comp (tensorPowerChannel T (n + 1))
      let A : Channel (block × phys) := identityTensorChannel block phys baseΦ
      let B : Channel (block × phys) := tensorWithIdentity block phys Ωn
      have hbase_hpres : IsHermiticityPreserving baseΦ := by
        exact hermiticityPreserving_comp
          (Ψ := transposeMap phys)
          (Φ := T)
          (transposeMap_hermiticityPreserving (d := phys))
          hT.hermiticity_preserving
      have hΩn_hpres : IsHermiticityPreserving Ωn := by
        exact hermiticityPreserving_comp
          (Ψ := transposeMap block)
          (Φ := tensorPowerChannel T n)
          (transposeMap_hermiticityPreserving (d := block))
          (tensorPowerChannel_isQuantumChannel (hT := hT) n).hermiticity_preserving
      have hA_hpres : IsHermiticityPreserving A :=
        identityTensorChannel_hermiticityPreserving (d := block) (k := phys) hbase_hpres
      have hB_hpres : IsHermiticityPreserving B :=
        tensorWithIdentity_hermiticityPreserving (d := block) (k := phys) hΩn_hpres
      have hΩnext_eq : Ωnext = A.comp B := by
        simpa [Ωnext, A, B, Ωn, block, baseΦ] using transpose_tensorPowerChannel_succ_eq T n
      have hbase_nonneg : 0 ≤ diamondOp baseΦ := diamondOp_nonneg baseΦ
      refine diamond_le_of_pointwise_nonempty
        (d := block × phys) (Φ := Ωnext) ((diamondOp baseΦ) ^ (n + 1)) ?_
      intro ρ
      let eB : ((block × phys) × (block × phys)) ≃ block × (phys × (block × phys)) :=
        Equiv.prodAssoc block phys (block × phys)
      let eA : ((block × phys) × (block × phys)) ≃ phys × (block × (block × phys)) :=
        prodSwapAssocEquiv block phys (block × phys)
      let X1 : Matrix ((block × phys) × (block × phys)) ((block × phys) × (block × phys)) ℂ :=
        tensorWithIdentity (block × phys) (block × phys) B ρ.1
      let ρB : DensityState (block × (phys × (block × phys))) :=
        ⟨Matrix.reindex eB eB ρ.1, isDensityState_reindex eB ρ.2⟩
      have hX1_reindex :
          Matrix.reindex eB eB X1 =
            tensorWithIdentity block (phys × (block × phys)) Ωn ρB.1 := by
        simpa [X1, ρB, B] using
          tensorWithIdentity_stabilized_left_reindex_eq
            (a := block) (b := phys) (c := block × phys) Ωn ρ.1
      have hX1_bound : traceNormOp X1 ≤ diamondOp Ωn := by
        calc
          traceNormOp X1 = traceNormOp (Matrix.reindex eB eB X1) := by
                symm
                exact traceNormOp_reindex eB X1
          _ = traceNormOp
                (tensorWithIdentity block (phys × (block × phys)) Ωn ρB.1) := by
                rw [hX1_reindex]
          _ ≤ diamondNormAt (d := block) (k := phys × (block × phys)) Ωn := by
                exact traceNorm_apply_le_diamond
                  (d := block) (k := phys × (block × phys)) (Φ := Ωn) ρB
          _ ≤ diamondOp Ωn := diamondNormAt_le_diamondOp_of_hpres hΩn_hpres
      have hX1_herm : Matrix.IsHermitian X1 := by
        unfold X1 Matrix.IsHermitian
        calc
          (tensorWithIdentity (block × phys) (block × phys) B ρ.1)ᴴ
              = tensorWithIdentity (block × phys) (block × phys) B ρ.1ᴴ := by
                    symm
                    exact
                      (tensorWithIdentity_hermiticityPreserving
                        (d := block × phys) (k := block × phys) hB_hpres) ρ.1
          _ = tensorWithIdentity (block × phys) (block × phys) B ρ.1 := by
                rw [ρ.2.1.isHermitian]
      let X1A : Matrix (phys × (block × (block × phys))) (phys × (block × (block × phys))) ℂ :=
        Matrix.reindex eA eA X1
      have hX1A_herm : Matrix.IsHermitian X1A := reindex_isHermitian eA hX1_herm
      have hA_density :
          ∀ σ : DensityState (phys × (block × (block × phys))),
            traceNormOp (tensorWithIdentity phys (block × (block × phys)) baseΦ σ.1) ≤
              diamondOp baseΦ := by
        intro σ
        exact le_trans
          (traceNorm_apply_le_diamond
            (d := phys) (k := block × (block × phys)) (Φ := baseΦ) σ)
          (diamondNormAt_le_diamondOp_of_hpres hbase_hpres)
      have hYsplit :
          tensorWithIdentity (block × phys) (block × phys) Ωnext ρ.1 =
            tensorWithIdentity (block × phys) (block × phys) A X1 := by
        rw [hΩnext_eq, tensorWithIdentity_comp]
        rfl
      have hA_reindex :
          Matrix.reindex eA eA
            (tensorWithIdentity (block × phys) (block × phys) A X1) =
            tensorWithIdentity phys (block × (block × phys)) baseΦ X1A := by
        simpa [A, X1A, baseΦ] using
          tensorWithIdentity_stabilized_right_reindex_eq
            (a := block) (b := phys) (c := block × phys) baseΦ X1
      calc
        traceNormOp (tensorWithIdentity (block × phys) (block × phys) Ωnext ρ.1)
            = traceNormOp (tensorWithIdentity (block × phys) (block × phys) A X1) := by
                rw [hYsplit]
        _ = traceNormOp
              (Matrix.reindex eA eA
                (tensorWithIdentity (block × phys) (block × phys) A X1)) := by
                symm
                exact traceNormOp_reindex eA
                  (tensorWithIdentity (block × phys) (block × phys) A X1)
        _ = traceNormOp (tensorWithIdentity phys (block × (block × phys)) baseΦ X1A) := by
              rw [hA_reindex]
        _ ≤ diamondOp baseΦ * traceNormOp X1A := by
              exact
                traceNormOp_le_mul_of_hermitian_of_density_bound
                  (Ψ := tensorWithIdentity phys (block × (block × phys)) baseΦ)
                  (tensorWithIdentity_hermiticityPreserving
                    (d := phys) (k := block × (block × phys)) hbase_hpres)
                  (diamondOp baseΦ)
                  hA_density
                  hX1A_herm
        _ = diamondOp baseΦ * traceNormOp X1 := by
              rw [traceNormOp_reindex eA X1]
        _ ≤ diamondOp baseΦ * diamondOp Ωn := by
              exact mul_le_mul_of_nonneg_left hX1_bound hbase_nonneg
        _ ≤ diamondOp baseΦ * (diamondOp baseΦ) ^ n := by
              exact mul_le_mul_of_nonneg_left (diamondOp_transpose_tensorPowerChannel_le_pow T hT n) hbase_nonneg
        _ = (diamondOp baseΦ) ^ (n + 1) := by
              simp [pow_succ, mul_comm, mul_left_comm, mul_assoc]

/-- Improved finite-error Holevo-Werner converse on the concrete recursive `m`-use channel
object `tensorPowerChannel T m`, still assuming the coded transpose bound. -/
theorem holevo_werner_improved_bound_of_recursive_tensorPower_channel
    {phys msg : Type u}
    [Fintype phys] [DecidableEq phys]
    [Fintype msg] [DecidableEq msg] [Nonempty msg]
    (T : Channel phys) (hT : IsQuantumChannel T) (m : ℕ)
    (encoder : Superoperator msg (TensorPowerType phys m))
    (decoder : Superoperator (TensorPowerType phys m) msg)
    (ε : ℝ)
    (hencoder : IsQuantumSuperoperator encoder)
    (hdecoder : IsQuantumSuperoperator decoder)
    (htranspose_code_bound :
      diamondOp
          ((transposeMap msg).comp
            (effectiveChannel encoder decoder (tensorPowerChannel T m))) ≤
        (diamondOp ((transposeMap phys).comp T)) ^ m)
    (herror :
      ε =
        (1 / 2 : ℝ) *
          diamondOp (idMinus (effectiveChannel encoder decoder (tensorPowerChannel T m))))
    (hm : 0 < m) (hε : ε < 1 / Real.sqrt 2) :
    Real.logb 2 (Fintype.card msg : ℝ) / (m : ℝ) ≤
      Real.logb 2 (diamondOp ((transposeMap phys).comp T)) +
        (1 / (m : ℝ)) * Real.logb 2 (1 / (1 - Real.sqrt 2 * ε)) := by
  have htensorPower : IsQuantumChannel (tensorPowerChannel T m) :=
    tensorPowerChannel_isQuantumChannel (hT := hT) m
  exact holevo_werner_improved_bound_of_block_tensorPower_diamondOp_bound
    T m encoder decoder (tensorPowerChannel T m) ε
    (effectiveChannel_isQuantumChannel hencoder htensorPower hdecoder)
    htranspose_code_bound herror hm hε

/-- Improved finite-error Holevo-Werner converse on the concrete recursive `m`-use channel
object `tensorPowerChannel T m`, from the ordinary `diamondOp` bound on that concrete
middle channel itself. -/
theorem holevo_werner_improved_bound_of_recursive_tensorPower_diamondOp_bound
    {phys msg : Type u}
    [Fintype phys] [DecidableEq phys] [Nonempty phys]
    [Fintype msg] [DecidableEq msg] [Nonempty msg]
    (T : Channel phys) (hT : IsQuantumChannel T) (m : ℕ)
    (encoder : Superoperator msg (TensorPowerType phys m))
    (decoder : Superoperator (TensorPowerType phys m) msg)
    (ε : ℝ)
    (hencoder : IsQuantumSuperoperator encoder)
    (hdecoder : IsQuantumSuperoperator decoder)
    (hbound :
      diamondOp
          ((transposeMap (TensorPowerType phys m)).comp (tensorPowerChannel T m)) ≤
        (diamondOp ((transposeMap phys).comp T)) ^ m)
    (herror :
      ε =
        (1 / 2 : ℝ) *
          diamondOp (idMinus (effectiveChannel encoder decoder (tensorPowerChannel T m))))
    (hm : 0 < m) (hε : ε < 1 / Real.sqrt 2) :
    Real.logb 2 (Fintype.card msg : ℝ) / (m : ℝ) ≤
      Real.logb 2 (diamondOp ((transposeMap phys).comp T)) +
        (1 / (m : ℝ)) * Real.logb 2 (1 / (1 - Real.sqrt 2 * ε)) := by
  have htensorPower : IsQuantumChannel (tensorPowerChannel T m) :=
    tensorPowerChannel_isQuantumChannel (hT := hT) m
  exact holevo_werner_improved_bound_of_block_middle_diamondOp_bound
    T m encoder decoder (tensorPowerChannel T m) ε
    hencoder hdecoder htensorPower hbound herror hm hε

/-- Improved finite-error Holevo-Werner converse on the concrete recursive `m`-use channel
object `tensorPowerChannel T m`, with the recursive middle-channel `diamondOp` bound proved
internally. -/
theorem holevo_werner_improved_bound_of_recursive_tensorPower
    {phys msg : Type u}
    [Fintype phys] [DecidableEq phys] [Nonempty phys]
    [Fintype msg] [DecidableEq msg] [Nonempty msg]
    (T : Channel phys) (hT : IsQuantumChannel T) (m : ℕ)
    (encoder : Superoperator msg (TensorPowerType phys m))
    (decoder : Superoperator (TensorPowerType phys m) msg)
    (ε : ℝ)
    (hencoder : IsQuantumSuperoperator encoder)
    (hdecoder : IsQuantumSuperoperator decoder)
    (herror :
      ε =
        (1 / 2 : ℝ) *
          diamondOp (idMinus (effectiveChannel encoder decoder (tensorPowerChannel T m))))
    (hm : 0 < m) (hε : ε < 1 / Real.sqrt 2) :
    Real.logb 2 (Fintype.card msg : ℝ) / (m : ℝ) ≤
      Real.logb 2 (diamondOp ((transposeMap phys).comp T)) +
        (1 / (m : ℝ)) * Real.logb 2 (1 / (1 - Real.sqrt 2 * ε)) := by
  exact holevo_werner_improved_bound_of_recursive_tensorPower_diamondOp_bound
    T hT m encoder decoder ε hencoder hdecoder
    (diamondOp_transpose_tensorPowerChannel_le_pow T hT m)
    herror hm hε

/-- Improved finite-error Holevo-Werner linear converse on the concrete recursive `m`-use
channel object `tensorPowerChannel T m`, with the recursive middle-channel `diamondOp`
bound proved internally. -/
theorem holevo_werner_improved_linear_bound_of_recursive_tensorPower
    {phys msg : Type u}
    [Fintype phys] [DecidableEq phys] [Nonempty phys]
    [Fintype msg] [DecidableEq msg] [Nonempty msg]
    (T : Channel phys) (hT : IsQuantumChannel T) (m : ℕ)
    (encoder : Superoperator msg (TensorPowerType phys m))
    (decoder : Superoperator (TensorPowerType phys m) msg)
    (ε : ℝ)
    (hencoder : IsQuantumSuperoperator encoder)
    (hdecoder : IsQuantumSuperoperator decoder)
    (herror :
      ε =
        (1 / 2 : ℝ) *
          diamondOp (idMinus (effectiveChannel encoder decoder (tensorPowerChannel T m)))) :
    (1 - Real.sqrt 2 * ε) * (Fintype.card msg : ℝ) ≤
      (diamondOp ((transposeMap phys).comp T)) ^ m := by
  have htensorPower : IsQuantumChannel (tensorPowerChannel T m) :=
    tensorPowerChannel_isQuantumChannel (hT := hT) m
  exact holevo_werner_improved_linear_bound_of_block_middle_diamondOp_bound
    T m encoder decoder (tensorPowerChannel T m) ε
    hencoder hdecoder htensorPower
    (diamondOp_transpose_tensorPowerChannel_le_pow T hT m)
    herror

/-- Paper-facing alias for the recursive-tensor-power wrapper with the coded transpose bound. -/
theorem paper_holevo_werner_improved_converse_of_recursive_tensorPower_channel
    {phys msg : Type u}
    [Fintype phys] [DecidableEq phys]
    [Fintype msg] [DecidableEq msg] [Nonempty msg]
    (T : Channel phys) (hT : IsQuantumChannel T) (m : ℕ)
    (encoder : Superoperator msg (TensorPowerType phys m))
    (decoder : Superoperator (TensorPowerType phys m) msg)
    (ε : ℝ)
    (hencoder : IsQuantumSuperoperator encoder)
    (hdecoder : IsQuantumSuperoperator decoder)
    (htranspose_code_bound :
      diamondOp
          ((transposeMap msg).comp
            (effectiveChannel encoder decoder (tensorPowerChannel T m))) ≤
        (diamondOp ((transposeMap phys).comp T)) ^ m)
    (herror :
      ε =
        (1 / 2 : ℝ) *
          diamondOp (idMinus (effectiveChannel encoder decoder (tensorPowerChannel T m))))
    (hm : 0 < m) (hε : ε < 1 / Real.sqrt 2) :
    Real.logb 2 (Fintype.card msg : ℝ) / (m : ℝ) ≤
      Real.logb 2 (diamondOp ((transposeMap phys).comp T)) +
        (1 / (m : ℝ)) * Real.logb 2 (1 / (1 - Real.sqrt 2 * ε)) := by
  exact holevo_werner_improved_bound_of_recursive_tensorPower_channel
    T hT m encoder decoder ε hencoder hdecoder htranspose_code_bound herror hm hε

/-- Paper-facing alias for the recursive-tensor-power wrapper from the ordinary `diamondOp`
bound on the concrete recursive channel itself. -/
theorem paper_holevo_werner_improved_converse_of_recursive_tensorPower_diamondOp_bound
    {phys msg : Type u}
    [Fintype phys] [DecidableEq phys] [Nonempty phys]
    [Fintype msg] [DecidableEq msg] [Nonempty msg]
    (T : Channel phys) (hT : IsQuantumChannel T) (m : ℕ)
    (encoder : Superoperator msg (TensorPowerType phys m))
    (decoder : Superoperator (TensorPowerType phys m) msg)
    (ε : ℝ)
    (hencoder : IsQuantumSuperoperator encoder)
    (hdecoder : IsQuantumSuperoperator decoder)
    (hbound :
      diamondOp
          ((transposeMap (TensorPowerType phys m)).comp (tensorPowerChannel T m)) ≤
        (diamondOp ((transposeMap phys).comp T)) ^ m)
    (herror :
      ε =
        (1 / 2 : ℝ) *
          diamondOp (idMinus (effectiveChannel encoder decoder (tensorPowerChannel T m))))
    (hm : 0 < m) (hε : ε < 1 / Real.sqrt 2) :
    Real.logb 2 (Fintype.card msg : ℝ) / (m : ℝ) ≤
      Real.logb 2 (diamondOp ((transposeMap phys).comp T)) +
        (1 / (m : ℝ)) * Real.logb 2 (1 / (1 - Real.sqrt 2 * ε)) := by
  exact holevo_werner_improved_bound_of_recursive_tensorPower_diamondOp_bound
    T hT m encoder decoder ε hencoder hdecoder hbound herror hm hε

/-- Paper-facing alias for the recursive-tensor-power improved converse with the
middle-channel `diamondOp` bound proved internally. -/
theorem paper_holevo_werner_improved_converse_of_recursive_tensorPower
    {phys msg : Type u}
    [Fintype phys] [DecidableEq phys] [Nonempty phys]
    [Fintype msg] [DecidableEq msg] [Nonempty msg]
    (T : Channel phys) (hT : IsQuantumChannel T) (m : ℕ)
    (encoder : Superoperator msg (TensorPowerType phys m))
    (decoder : Superoperator (TensorPowerType phys m) msg)
    (ε : ℝ)
    (hencoder : IsQuantumSuperoperator encoder)
    (hdecoder : IsQuantumSuperoperator decoder)
    (herror :
      ε =
        (1 / 2 : ℝ) *
          diamondOp (idMinus (effectiveChannel encoder decoder (tensorPowerChannel T m))))
    (hm : 0 < m) (hε : ε < 1 / Real.sqrt 2) :
    Real.logb 2 (Fintype.card msg : ℝ) / (m : ℝ) ≤
      Real.logb 2 (diamondOp ((transposeMap phys).comp T)) +
        (1 / (m : ℝ)) * Real.logb 2 (1 / (1 - Real.sqrt 2 * ε)) := by
  exact holevo_werner_improved_bound_of_recursive_tensorPower
    T hT m encoder decoder ε hencoder hdecoder herror hm hε

/-- Paper-facing linear alias for the recursive-tensor-power improved converse with the
middle-channel `diamondOp` bound proved internally. -/
theorem paper_holevo_werner_improved_linear_converse_of_recursive_tensorPower
    {phys msg : Type u}
    [Fintype phys] [DecidableEq phys] [Nonempty phys]
    [Fintype msg] [DecidableEq msg] [Nonempty msg]
    (T : Channel phys) (hT : IsQuantumChannel T) (m : ℕ)
    (encoder : Superoperator msg (TensorPowerType phys m))
    (decoder : Superoperator (TensorPowerType phys m) msg)
    (ε : ℝ)
    (hencoder : IsQuantumSuperoperator encoder)
    (hdecoder : IsQuantumSuperoperator decoder)
    (herror :
      ε =
        (1 / 2 : ℝ) *
          diamondOp (idMinus (effectiveChannel encoder decoder (tensorPowerChannel T m)))) :
    (1 - Real.sqrt 2 * ε) * (Fintype.card msg : ℝ) ≤
      (diamondOp ((transposeMap phys).comp T)) ^ m := by
  exact holevo_werner_improved_linear_bound_of_recursive_tensorPower
    T hT m encoder decoder ε hencoder hdecoder herror

/-- Improved linear Holevo-Werner converse from the post-encoder pointwise middle-map bound. -/
theorem holevo_werner_improved_linear_bound_of_post_encoder_reduction
    {phys msg : Type u}
    [Fintype phys] [DecidableEq phys]
    [Fintype msg] [DecidableEq msg] [Nonempty msg]
    {scheme : QuantumCodingScheme phys msg}
    {T : Channel phys} {m : ℕ} {ε : ℝ}
    (hpost : PostEncoderTransposeCodeBoundData scheme T m)
    (herror : ε = (1 / 2 : ℝ) * diamondOp (idMinus scheme.effective)) :
    (1 - Real.sqrt 2 * ε) * (Fintype.card msg : ℝ) ≤
      (diamondOp ((transposeMap phys).comp T)) ^ m := by
  exact holevo_werner_improved_linear_bound
    (HolevoWernerCodeData.of_post_encoder_reduction hpost herror)

/-- Improved linear Holevo-Werner converse from the pure-state post-encoder pointwise middle-map
bound. -/
theorem holevo_werner_improved_linear_bound_of_pure_state_bound
    {phys msg : Type u}
    [Fintype phys] [DecidableEq phys]
    [Fintype msg] [DecidableEq msg] [Nonempty msg]
    {scheme : QuantumCodingScheme phys msg}
    {T : Channel phys} {m : ℕ} {ε : ℝ}
    (hpure : PostEncoderPureTransposeCodeBoundData scheme T m)
    (herror : ε = (1 / 2 : ℝ) * diamondOp (idMinus scheme.effective)) :
    (1 - Real.sqrt 2 * ε) * (Fintype.card msg : ℝ) ≤
      (diamondOp ((transposeMap phys).comp T)) ^ m := by
  exact holevo_werner_improved_linear_bound
    (HolevoWernerCodeData.of_pure_state_bound hpure herror)

/-- Improved logarithmic Holevo-Werner converse from the post-encoder pointwise middle-map
bound. -/
theorem holevo_werner_improved_bound_of_post_encoder_reduction
    {phys msg : Type u}
    [Fintype phys] [DecidableEq phys]
    [Fintype msg] [DecidableEq msg] [Nonempty msg]
    {scheme : QuantumCodingScheme phys msg}
    {T : Channel phys} {m : ℕ} {ε : ℝ}
    (hpost : PostEncoderTransposeCodeBoundData scheme T m)
    (herror : ε = (1 / 2 : ℝ) * diamondOp (idMinus scheme.effective))
    (hm : 0 < m) (hε : ε < 1 / Real.sqrt 2) :
    Real.logb 2 (Fintype.card msg : ℝ) / (m : ℝ) ≤
      Real.logb 2 (diamondOp ((transposeMap phys).comp T)) +
        (1 / (m : ℝ)) * Real.logb 2 (1 / (1 - Real.sqrt 2 * ε)) := by
  exact holevo_werner_improved_bound
    (HolevoWernerCodeData.of_post_encoder_reduction hpost herror) hm hε

/-- Improved logarithmic Holevo-Werner converse from the pure-state post-encoder pointwise
middle-map bound. -/
theorem holevo_werner_improved_bound_of_pure_state_bound
    {phys msg : Type u}
    [Fintype phys] [DecidableEq phys]
    [Fintype msg] [DecidableEq msg] [Nonempty msg]
    {scheme : QuantumCodingScheme phys msg}
    {T : Channel phys} {m : ℕ} {ε : ℝ}
    (hpure : PostEncoderPureTransposeCodeBoundData scheme T m)
    (herror : ε = (1 / 2 : ℝ) * diamondOp (idMinus scheme.effective))
    (hm : 0 < m) (hε : ε < 1 / Real.sqrt 2) :
    Real.logb 2 (Fintype.card msg : ℝ) / (m : ℝ) ≤
      Real.logb 2 (diamondOp ((transposeMap phys).comp T)) +
        (1 / (m : ℝ)) * Real.logb 2 (1 / (1 - Real.sqrt 2 * ε)) := by
  exact holevo_werner_improved_bound
    (HolevoWernerCodeData.of_pure_state_bound hpure herror) hm hε

/-- Improved linear Holevo-Werner converse from the ordinary `diamondOp` middle-map bound
when the message ancilla dimension is at least the physical input dimension. -/
theorem holevo_werner_improved_linear_bound_of_diamondOp_bound_card_le
    {phys msg : Type u}
    [Fintype phys] [DecidableEq phys] [Nonempty phys]
    [Fintype msg] [DecidableEq msg] [Nonempty msg]
    {scheme : QuantumCodingScheme phys msg}
    {T : Channel phys} {m : ℕ} {ε : ℝ}
    (hcard : Fintype.card phys ≤ Fintype.card msg)
    (hbound :
      diamondOp ((transposeMap phys).comp scheme.tensorPower) ≤
        (diamondOp ((transposeMap phys).comp T)) ^ m)
    (herror : ε = (1 / 2 : ℝ) * diamondOp (idMinus scheme.effective)) :
    (1 - Real.sqrt 2 * ε) * (Fintype.card msg : ℝ) ≤
      (diamondOp ((transposeMap phys).comp T)) ^ m := by
  exact holevo_werner_improved_linear_bound
    (HolevoWernerCodeData.of_diamondOp_bound_card_le hcard hbound herror)

/-- Improved logarithmic Holevo-Werner converse from the ordinary `diamondOp` middle-map
bound when the message ancilla dimension is at least the physical input dimension. -/
theorem holevo_werner_improved_bound_of_diamondOp_bound_card_le
    {phys msg : Type u}
    [Fintype phys] [DecidableEq phys] [Nonempty phys]
    [Fintype msg] [DecidableEq msg] [Nonempty msg]
    {scheme : QuantumCodingScheme phys msg}
    {T : Channel phys} {m : ℕ} {ε : ℝ}
    (hcard : Fintype.card phys ≤ Fintype.card msg)
    (hbound :
      diamondOp ((transposeMap phys).comp scheme.tensorPower) ≤
        (diamondOp ((transposeMap phys).comp T)) ^ m)
    (herror : ε = (1 / 2 : ℝ) * diamondOp (idMinus scheme.effective))
    (hm : 0 < m) (hε : ε < 1 / Real.sqrt 2) :
    Real.logb 2 (Fintype.card msg : ℝ) / (m : ℝ) ≤
      Real.logb 2 (diamondOp ((transposeMap phys).comp T)) +
        (1 / (m : ℝ)) * Real.logb 2 (1 / (1 - Real.sqrt 2 * ε)) := by
  exact holevo_werner_improved_bound
    (HolevoWernerCodeData.of_diamondOp_bound_card_le hcard hbound herror) hm hε

/-- Improved linear Holevo-Werner converse from the ordinary `diamondOp` middle-map bound
when the message ancilla dimension is at most the physical input dimension. -/
theorem holevo_werner_improved_linear_bound_of_diamondOp_bound_card_ge
    {phys msg : Type u}
    [Fintype phys] [DecidableEq phys] [Nonempty phys]
    [Fintype msg] [DecidableEq msg] [Nonempty msg]
    {scheme : QuantumCodingScheme phys msg}
    {T : Channel phys} {m : ℕ} {ε : ℝ}
    (hcard : Fintype.card msg ≤ Fintype.card phys)
    (hbound :
      diamondOp ((transposeMap phys).comp scheme.tensorPower) ≤
        (diamondOp ((transposeMap phys).comp T)) ^ m)
    (herror : ε = (1 / 2 : ℝ) * diamondOp (idMinus scheme.effective)) :
    (1 - Real.sqrt 2 * ε) * (Fintype.card msg : ℝ) ≤
      (diamondOp ((transposeMap phys).comp T)) ^ m := by
  exact holevo_werner_improved_linear_bound
    (HolevoWernerCodeData.of_diamondOp_bound_card_ge hcard hbound herror)

/-- Improved logarithmic Holevo-Werner converse from the ordinary `diamondOp` middle-map
bound when the message ancilla dimension is at most the physical input dimension. -/
theorem holevo_werner_improved_bound_of_diamondOp_bound_card_ge
    {phys msg : Type u}
    [Fintype phys] [DecidableEq phys] [Nonempty phys]
    [Fintype msg] [DecidableEq msg] [Nonempty msg]
    {scheme : QuantumCodingScheme phys msg}
    {T : Channel phys} {m : ℕ} {ε : ℝ}
    (hcard : Fintype.card msg ≤ Fintype.card phys)
    (hbound :
      diamondOp ((transposeMap phys).comp scheme.tensorPower) ≤
        (diamondOp ((transposeMap phys).comp T)) ^ m)
    (herror : ε = (1 / 2 : ℝ) * diamondOp (idMinus scheme.effective))
    (hm : 0 < m) (hε : ε < 1 / Real.sqrt 2) :
    Real.logb 2 (Fintype.card msg : ℝ) / (m : ℝ) ≤
      Real.logb 2 (diamondOp ((transposeMap phys).comp T)) +
        (1 / (m : ℝ)) * Real.logb 2 (1 / (1 - Real.sqrt 2 * ε)) := by
  exact holevo_werner_improved_bound
    (HolevoWernerCodeData.of_diamondOp_bound_card_ge hcard hbound herror) hm hε

/-- Improved Holevo-Werner converse from the ordinary `diamondOp` middle-map bound, with no
extra cardinality assumptions. -/
theorem holevo_werner_improved_bound_of_diamondOp_bound
    {phys msg : Type u}
    [Fintype phys] [DecidableEq phys] [Nonempty phys]
    [Fintype msg] [DecidableEq msg] [Nonempty msg]
    {scheme : QuantumCodingScheme phys msg}
    {T : Channel phys} {m : ℕ} {ε : ℝ}
    (hbound :
      diamondOp ((transposeMap phys).comp scheme.tensorPower) ≤
        (diamondOp ((transposeMap phys).comp T)) ^ m)
    (herror : ε = (1 / 2 : ℝ) * diamondOp (idMinus scheme.effective))
    (hm : 0 < m) (hε : ε < 1 / Real.sqrt 2) :
    Real.logb 2 (Fintype.card msg : ℝ) / (m : ℝ) ≤
      Real.logb 2 (diamondOp ((transposeMap phys).comp T)) +
        (1 / (m : ℝ)) * Real.logb 2 (1 / (1 - Real.sqrt 2 * ε)) := by
  exact holevo_werner_improved_bound
    (HolevoWernerCodeData.of_diamondOp_bound hbound herror) hm hε

/-- Improved linear Holevo-Werner converse from the fixed-ancilla `diamondNormAt` middle-map
bound. -/
theorem holevo_werner_improved_linear_bound_of_diamondAt_bound
    {phys msg : Type u}
    [Fintype phys] [DecidableEq phys]
    [Fintype msg] [DecidableEq msg] [Nonempty msg]
    {scheme : QuantumCodingScheme phys msg}
    {T : Channel phys} {m : ℕ} {ε : ℝ}
    (hbound : PostEncoderDiamondAtBoundData scheme T m)
    (herror : ε = (1 / 2 : ℝ) * diamondOp (idMinus scheme.effective)) :
    (1 - Real.sqrt 2 * ε) * (Fintype.card msg : ℝ) ≤
      (diamondOp ((transposeMap phys).comp T)) ^ m := by
  exact holevo_werner_improved_linear_bound
    (HolevoWernerCodeData.of_diamondAt_bound hbound herror)

/-- Improved logarithmic Holevo-Werner converse from the fixed-ancilla `diamondNormAt`
middle-map bound. -/
theorem holevo_werner_improved_bound_of_diamondAt_bound
    {phys msg : Type u}
    [Fintype phys] [DecidableEq phys]
    [Fintype msg] [DecidableEq msg] [Nonempty msg]
    {scheme : QuantumCodingScheme phys msg}
    {T : Channel phys} {m : ℕ} {ε : ℝ}
    (hbound : PostEncoderDiamondAtBoundData scheme T m)
    (herror : ε = (1 / 2 : ℝ) * diamondOp (idMinus scheme.effective))
    (hm : 0 < m) (hε : ε < 1 / Real.sqrt 2) :
    Real.logb 2 (Fintype.card msg : ℝ) / (m : ℝ) ≤
      Real.logb 2 (diamondOp ((transposeMap phys).comp T)) +
        (1 / (m : ℝ)) * Real.logb 2 (1 / (1 - Real.sqrt 2 * ε)) := by
  exact holevo_werner_improved_bound
    (HolevoWernerCodeData.of_diamondAt_bound hbound herror) hm hε

/-- Improved linear Holevo-Werner converse from the ordinary `diamondOp` middle-map bound in
the literal same-type case `msg = phys`. -/
theorem holevo_werner_improved_linear_bound_of_diamondOp_bound_same_type
    {phys : Type u}
    [Fintype phys] [DecidableEq phys] [Nonempty phys]
    {scheme : QuantumCodingScheme phys phys}
    {T : Channel phys} {m : ℕ} {ε : ℝ}
    (hbound :
      diamondOp ((transposeMap phys).comp scheme.tensorPower) ≤
        (diamondOp ((transposeMap phys).comp T)) ^ m)
    (herror : ε = (1 / 2 : ℝ) * diamondOp (idMinus scheme.effective)) :
    (1 - Real.sqrt 2 * ε) * (Fintype.card phys : ℝ) ≤
      (diamondOp ((transposeMap phys).comp T)) ^ m := by
  exact holevo_werner_improved_linear_bound
    (HolevoWernerCodeData.of_diamondOp_bound_same_type hbound herror)

/-- Improved logarithmic Holevo-Werner converse from the ordinary `diamondOp` middle-map
bound in the literal same-type case `msg = phys`. -/
theorem holevo_werner_improved_bound_of_diamondOp_bound_same_type
    {phys : Type u}
    [Fintype phys] [DecidableEq phys] [Nonempty phys]
    {scheme : QuantumCodingScheme phys phys}
    {T : Channel phys} {m : ℕ} {ε : ℝ}
    (hbound :
      diamondOp ((transposeMap phys).comp scheme.tensorPower) ≤
        (diamondOp ((transposeMap phys).comp T)) ^ m)
    (herror : ε = (1 / 2 : ℝ) * diamondOp (idMinus scheme.effective))
    (hm : 0 < m) (hε : ε < 1 / Real.sqrt 2) :
    Real.logb 2 (Fintype.card phys : ℝ) / (m : ℝ) ≤
      Real.logb 2 (diamondOp ((transposeMap phys).comp T)) +
        (1 / (m : ℝ)) * Real.logb 2 (1 / (1 - Real.sqrt 2 * ε)) := by
  exact holevo_werner_improved_bound
    (HolevoWernerCodeData.of_diamondOp_bound_same_type hbound herror) hm hε

/-- Improved linear Holevo-Werner converse from the ordinary `diamondOp` middle-map bound
when the message type has the same cardinality as the physical input type. -/
theorem holevo_werner_improved_linear_bound_of_diamondOp_bound_card_eq
    {phys msg : Type u}
    [Fintype phys] [DecidableEq phys] [Nonempty phys]
    [Fintype msg] [DecidableEq msg] [Nonempty msg]
    {scheme : QuantumCodingScheme phys msg}
    {T : Channel phys} {m : ℕ} {ε : ℝ}
    (hcard : Fintype.card msg = Fintype.card phys)
    (hbound :
      diamondOp ((transposeMap phys).comp scheme.tensorPower) ≤
        (diamondOp ((transposeMap phys).comp T)) ^ m)
    (herror : ε = (1 / 2 : ℝ) * diamondOp (idMinus scheme.effective)) :
    (1 - Real.sqrt 2 * ε) * (Fintype.card msg : ℝ) ≤
      (diamondOp ((transposeMap phys).comp T)) ^ m := by
  exact holevo_werner_improved_linear_bound
    (HolevoWernerCodeData.of_diamondOp_bound_card_eq hcard hbound herror)

/-- Improved logarithmic Holevo-Werner converse from the ordinary `diamondOp` middle-map
bound when the message type has the same cardinality as the physical input type. -/
theorem holevo_werner_improved_bound_of_diamondOp_bound_card_eq
    {phys msg : Type u}
    [Fintype phys] [DecidableEq phys] [Nonempty phys]
    [Fintype msg] [DecidableEq msg] [Nonempty msg]
    {scheme : QuantumCodingScheme phys msg}
    {T : Channel phys} {m : ℕ} {ε : ℝ}
    (hcard : Fintype.card msg = Fintype.card phys)
    (hbound :
      diamondOp ((transposeMap phys).comp scheme.tensorPower) ≤
        (diamondOp ((transposeMap phys).comp T)) ^ m)
    (herror : ε = (1 / 2 : ℝ) * diamondOp (idMinus scheme.effective))
    (hm : 0 < m) (hε : ε < 1 / Real.sqrt 2) :
    Real.logb 2 (Fintype.card msg : ℝ) / (m : ℝ) ≤
      Real.logb 2 (diamondOp ((transposeMap phys).comp T)) +
        (1 / (m : ℝ)) * Real.logb 2 (1 / (1 - Real.sqrt 2 * ε)) := by
  exact holevo_werner_improved_bound
    (HolevoWernerCodeData.of_diamondOp_bound_card_eq hcard hbound herror) hm hε

/-- Paper-facing improved converse from the post-encoder pointwise middle-map bound. -/
theorem paper_holevo_werner_improved_converse_of_post_encoder_reduction
    {phys msg : Type u}
    [Fintype phys] [DecidableEq phys]
    [Fintype msg] [DecidableEq msg] [Nonempty msg]
    {scheme : QuantumCodingScheme phys msg}
    {T : Channel phys} {m : ℕ} {ε : ℝ}
    (hpost : PostEncoderTransposeCodeBoundData scheme T m)
    (herror : ε = (1 / 2 : ℝ) * diamondOp (idMinus scheme.effective))
    (hm : 0 < m) (hε : ε < 1 / Real.sqrt 2) :
    Real.logb 2 (Fintype.card msg : ℝ) / (m : ℝ) ≤
      Real.logb 2 (diamondOp ((transposeMap phys).comp T)) +
        (1 / (m : ℝ)) * Real.logb 2 (1 / (1 - Real.sqrt 2 * ε)) := by
  exact holevo_werner_improved_bound_of_post_encoder_reduction hpost herror hm hε

/-- Paper-facing improved converse from the pure-state post-encoder middle-map bound. -/
theorem paper_holevo_werner_improved_converse_of_pure_state_bound
    {phys msg : Type u}
    [Fintype phys] [DecidableEq phys]
    [Fintype msg] [DecidableEq msg] [Nonempty msg]
    {scheme : QuantumCodingScheme phys msg}
    {T : Channel phys} {m : ℕ} {ε : ℝ}
    (hpure : PostEncoderPureTransposeCodeBoundData scheme T m)
    (herror : ε = (1 / 2 : ℝ) * diamondOp (idMinus scheme.effective))
    (hm : 0 < m) (hε : ε < 1 / Real.sqrt 2) :
    Real.logb 2 (Fintype.card msg : ℝ) / (m : ℝ) ≤
      Real.logb 2 (diamondOp ((transposeMap phys).comp T)) +
        (1 / (m : ℝ)) * Real.logb 2 (1 / (1 - Real.sqrt 2 * ε)) := by
  exact holevo_werner_improved_bound_of_pure_state_bound hpure herror hm hε

/-- Paper-facing improved converse from the ordinary `diamondOp` middle-map bound when the
message ancilla dimension is at least the physical input dimension. -/
theorem paper_holevo_werner_improved_converse_of_diamondOp_bound_card_le
    {phys msg : Type u}
    [Fintype phys] [DecidableEq phys] [Nonempty phys]
    [Fintype msg] [DecidableEq msg] [Nonempty msg]
    {scheme : QuantumCodingScheme phys msg}
    {T : Channel phys} {m : ℕ} {ε : ℝ}
    (hcard : Fintype.card phys ≤ Fintype.card msg)
    (hbound :
      diamondOp ((transposeMap phys).comp scheme.tensorPower) ≤
        (diamondOp ((transposeMap phys).comp T)) ^ m)
    (herror : ε = (1 / 2 : ℝ) * diamondOp (idMinus scheme.effective))
    (hm : 0 < m) (hε : ε < 1 / Real.sqrt 2) :
    Real.logb 2 (Fintype.card msg : ℝ) / (m : ℝ) ≤
      Real.logb 2 (diamondOp ((transposeMap phys).comp T)) +
        (1 / (m : ℝ)) * Real.logb 2 (1 / (1 - Real.sqrt 2 * ε)) := by
  exact holevo_werner_improved_bound_of_diamondOp_bound_card_le hcard hbound herror hm hε

/-- Paper-facing improved converse from the ordinary `diamondOp` middle-map bound when the
message ancilla dimension is at most the physical input dimension. -/
theorem paper_holevo_werner_improved_converse_of_diamondOp_bound_card_ge
    {phys msg : Type u}
    [Fintype phys] [DecidableEq phys] [Nonempty phys]
    [Fintype msg] [DecidableEq msg] [Nonempty msg]
    {scheme : QuantumCodingScheme phys msg}
    {T : Channel phys} {m : ℕ} {ε : ℝ}
    (hcard : Fintype.card msg ≤ Fintype.card phys)
    (hbound :
      diamondOp ((transposeMap phys).comp scheme.tensorPower) ≤
        (diamondOp ((transposeMap phys).comp T)) ^ m)
    (herror : ε = (1 / 2 : ℝ) * diamondOp (idMinus scheme.effective))
    (hm : 0 < m) (hε : ε < 1 / Real.sqrt 2) :
    Real.logb 2 (Fintype.card msg : ℝ) / (m : ℝ) ≤
      Real.logb 2 (diamondOp ((transposeMap phys).comp T)) +
        (1 / (m : ℝ)) * Real.logb 2 (1 / (1 - Real.sqrt 2 * ε)) := by
  exact holevo_werner_improved_bound_of_diamondOp_bound_card_ge hcard hbound herror hm hε

/-- Paper-facing improved converse from the ordinary `diamondOp` middle-map bound, with no
extra cardinality assumptions. -/
theorem paper_holevo_werner_improved_converse_of_diamondOp_bound
    {phys msg : Type u}
    [Fintype phys] [DecidableEq phys] [Nonempty phys]
    [Fintype msg] [DecidableEq msg] [Nonempty msg]
    {scheme : QuantumCodingScheme phys msg}
    {T : Channel phys} {m : ℕ} {ε : ℝ}
    (hbound :
      diamondOp ((transposeMap phys).comp scheme.tensorPower) ≤
        (diamondOp ((transposeMap phys).comp T)) ^ m)
    (herror : ε = (1 / 2 : ℝ) * diamondOp (idMinus scheme.effective))
    (hm : 0 < m) (hε : ε < 1 / Real.sqrt 2) :
    Real.logb 2 (Fintype.card msg : ℝ) / (m : ℝ) ≤
      Real.logb 2 (diamondOp ((transposeMap phys).comp T)) +
        (1 / (m : ℝ)) * Real.logb 2 (1 / (1 - Real.sqrt 2 * ε)) := by
  exact holevo_werner_improved_bound_of_diamondOp_bound hbound herror hm hε

/-- Paper-facing improved converse from the fixed-ancilla `diamondNormAt` middle-map bound. -/
theorem paper_holevo_werner_improved_converse_of_diamondAt_bound
    {phys msg : Type u}
    [Fintype phys] [DecidableEq phys]
    [Fintype msg] [DecidableEq msg] [Nonempty msg]
    {scheme : QuantumCodingScheme phys msg}
    {T : Channel phys} {m : ℕ} {ε : ℝ}
    (hbound : PostEncoderDiamondAtBoundData scheme T m)
    (herror : ε = (1 / 2 : ℝ) * diamondOp (idMinus scheme.effective))
    (hm : 0 < m) (hε : ε < 1 / Real.sqrt 2) :
    Real.logb 2 (Fintype.card msg : ℝ) / (m : ℝ) ≤
      Real.logb 2 (diamondOp ((transposeMap phys).comp T)) +
        (1 / (m : ℝ)) * Real.logb 2 (1 / (1 - Real.sqrt 2 * ε)) := by
  exact holevo_werner_improved_bound_of_diamondAt_bound hbound herror hm hε

/-- Paper-facing improved converse from the ordinary `diamondOp` middle-map bound in the
literal same-type case `msg = phys`. -/
theorem paper_holevo_werner_improved_converse_of_diamondOp_bound_same_type
    {phys : Type u}
    [Fintype phys] [DecidableEq phys] [Nonempty phys]
    {scheme : QuantumCodingScheme phys phys}
    {T : Channel phys} {m : ℕ} {ε : ℝ}
    (hbound :
      diamondOp ((transposeMap phys).comp scheme.tensorPower) ≤
        (diamondOp ((transposeMap phys).comp T)) ^ m)
    (herror : ε = (1 / 2 : ℝ) * diamondOp (idMinus scheme.effective))
    (hm : 0 < m) (hε : ε < 1 / Real.sqrt 2) :
    Real.logb 2 (Fintype.card phys : ℝ) / (m : ℝ) ≤
      Real.logb 2 (diamondOp ((transposeMap phys).comp T)) +
        (1 / (m : ℝ)) * Real.logb 2 (1 / (1 - Real.sqrt 2 * ε)) := by
  exact holevo_werner_improved_bound_of_diamondOp_bound_same_type hbound herror hm hε

/-- Paper-facing improved converse from the ordinary `diamondOp` middle-map bound when the
message type has the same cardinality as the physical input type. -/
theorem paper_holevo_werner_improved_converse_of_diamondOp_bound_card_eq
    {phys msg : Type u}
    [Fintype phys] [DecidableEq phys] [Nonempty phys]
    [Fintype msg] [DecidableEq msg] [Nonempty msg]
    {scheme : QuantumCodingScheme phys msg}
    {T : Channel phys} {m : ℕ} {ε : ℝ}
    (hcard : Fintype.card msg = Fintype.card phys)
    (hbound :
      diamondOp ((transposeMap phys).comp scheme.tensorPower) ≤
        (diamondOp ((transposeMap phys).comp T)) ^ m)
    (herror : ε = (1 / 2 : ℝ) * diamondOp (idMinus scheme.effective))
    (hm : 0 < m) (hε : ε < 1 / Real.sqrt 2) :
    Real.logb 2 (Fintype.card msg : ℝ) / (m : ℝ) ≤
      Real.logb 2 (diamondOp ((transposeMap phys).comp T)) +
        (1 / (m : ℝ)) * Real.logb 2 (1 / (1 - Real.sqrt 2 * ε)) := by
  exact holevo_werner_improved_bound_of_diamondOp_bound_card_eq hcard hbound herror hm hε

/-- Paper-facing alias for the original finite-error Holevo-Werner converse. -/
theorem paper_holevo_werner_original_converse
    {phys msg : Type u}
    [Fintype phys] [DecidableEq phys]
    [Fintype msg] [DecidableEq msg] [Nonempty msg]
    {effective : Channel msg}
    {T : Channel phys} {m : ℕ} {ε : ℝ}
    (hdata : OriginalHolevoWernerEffectiveData effective T m ε)
    (hm : 0 < m) (hε : ε < 1 / 2) :
    Real.logb 2 (Fintype.card msg : ℝ) / (m : ℝ) ≤
      Real.logb 2 (diamondOp ((transposeMap phys).comp T)) +
        (1 / (m : ℝ)) * Real.logb 2 (1 / (1 - 2 * ε)) :=
  holevo_werner_original_bound_effective hdata hm hε

/-- Paper-facing alias for the replacement step: any improved bound on the transposed
error term drops into the same Holevo-Werner proof. -/
theorem paper_holevo_werner_replacement_argument
    {phys msg : Type u}
    [Fintype phys] [DecidableEq phys]
    [Fintype msg] [DecidableEq msg] [Nonempty msg]
    {effective : Channel msg}
    (T : Channel phys) (m : ℕ) (ε c : ℝ)
    (hdata : HolevoWernerEffectiveData effective T m ε)
    (herror_term :
      diamondOp ((transposeMap msg).comp (idMinus effective)) ≤
        c * (Fintype.card msg : ℝ) * ε)
    (hm : 0 < m) (hε : ε < 1 / c) (hc : 0 < c) :
    Real.logb 2 (Fintype.card msg : ℝ) / (m : ℝ) ≤
      Real.logb 2 (diamondOp ((transposeMap phys).comp T)) +
        (1 / (m : ℝ)) * Real.logb 2 (1 / (1 - c * ε)) :=
  holevo_werner_bound_of_replacement_argument_effective T m ε c hdata herror_term hm hε hc

/-- Paper-facing alias for the improved finite-error Holevo-Werner converse obtained by
plugging Remark 1 into the replacement argument. -/
theorem paper_holevo_werner_improved_converse
    {phys msg : Type u}
    [Fintype phys] [DecidableEq phys]
    [Fintype msg] [DecidableEq msg] [Nonempty msg]
    {effective : Channel msg}
    {T : Channel phys} {m : ℕ} {ε : ℝ}
    (hdata : HolevoWernerEffectiveData effective T m ε)
    (hm : 0 < m) (hε : ε < 1 / Real.sqrt 2) :
    Real.logb 2 (Fintype.card msg : ℝ) / (m : ℝ) ≤
      Real.logb 2 (diamondOp ((transposeMap phys).comp T)) +
        (1 / (m : ℝ)) * Real.logb 2 (1 / (1 - Real.sqrt 2 * ε)) :=
  holevo_werner_improved_bound_effective hdata hm hε

end
end Diamond
