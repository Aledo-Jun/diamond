import Diamond.HolevoWerner.Basic

open scoped BigOperators
open scoped ComplexOrder
open scoped Kronecker
open scoped MatrixOrder
open scoped Matrix.Norms.Frobenius
open Matrix

namespace Diamond

universe u

noncomputable section

/-- Right-associated block space for `m` uses of a physical system. -/
def TensorPowerType (phys : Type u) : ℕ → Type u
  | 0 => PUnit
  | n + 1 => TensorPowerType phys n × phys

instance tensorPowerTypeFintype
    {phys : Type u} [Fintype phys] :
    ∀ m : ℕ, Fintype (TensorPowerType phys m)
  | 0 => by
      dsimp [TensorPowerType]
      infer_instance
  | n + 1 => by
      dsimp [TensorPowerType]
      letI := tensorPowerTypeFintype (phys := phys) n
      infer_instance

instance tensorPowerTypeDecidableEq
    {phys : Type u} [DecidableEq phys] :
    ∀ m : ℕ, DecidableEq (TensorPowerType phys m)
  | 0 => by
      dsimp [TensorPowerType]
      infer_instance
  | n + 1 => by
      dsimp [TensorPowerType]
      letI := tensorPowerTypeDecidableEq (phys := phys) n
      infer_instance

instance tensorPowerTypeNonempty
    {phys : Type u} [Nonempty phys] :
    ∀ m : ℕ, Nonempty (TensorPowerType phys m)
  | 0 => by
      dsimp [TensorPowerType]
      infer_instance
  | n + 1 => by
      dsimp [TensorPowerType]
      letI := tensorPowerTypeNonempty (phys := phys) n
      infer_instance

/-- Cardinality of the recursive block space. -/
theorem fintype_card_tensorPowerType
    {phys : Type u} [Fintype phys] :
    ∀ m : ℕ, Fintype.card (TensorPowerType phys m) = (Fintype.card phys) ^ m
  | 0 => by
      simp [TensorPowerType]
  | n + 1 => by
      change Fintype.card (TensorPowerType phys n × phys) =
        (Fintype.card phys) ^ (n + 1)
      rw [Fintype.card_prod]
      rw [fintype_card_tensorPowerType (phys := phys) n]
      simpa [Nat.pow_succ, Nat.mul_comm]

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

/-- Identity channel is quantum. -/
theorem idChannel_isQuantumChannel
    {d : Type u} [Fintype d] [DecidableEq d] :
    IsQuantumChannel (LinearMap.id : Channel d) := by
  refine
    { trace_preserving := ?_
      hermiticity_preserving := ?_
      kraus := ?_ }
  · intro X
    rfl
  · intro X
    rfl
  · refine ⟨1, (fun _ => (1 : Matrix d d ℂ)), ?_, ?_⟩
    · intro X
      simp
    · simp

private theorem tensorWithIdentity_punit_id_eq
    {k : Type u} [Fintype k] [DecidableEq k] :
    tensorWithIdentity PUnit k (LinearMap.id : Channel PUnit) = LinearMap.id := by
  ext X i j
  rcases i with ⟨⟨⟩, a⟩
  rcases j with ⟨⟨⟩, b⟩
  rfl

/-- Apply a channel on the right tensor factor. -/
def identityTensorChannel
    (d k : Type u)
    [Fintype d] [DecidableEq d]
    [Fintype k] [DecidableEq k]
    (Φ : Channel k) : Channel (d × k) where
  toFun := fun X i j =>
    Φ (fun p q : k => X (i.1, p) (j.1, q)) i.2 j.2
  map_add' := by
    intro X Y
    ext i j
    let X' : Operator k := fun p q => X (i.1, p) (j.1, q)
    let Y' : Operator k := fun p q => Y (i.1, p) (j.1, q)
    change (Φ (X' + Y')) i.2 j.2 = (Φ X' + Φ Y') i.2 j.2
    rw [map_add]
  map_smul' := by
    intro c X
    ext i j
    let X' : Operator k := fun p q => X (i.1, p) (j.1, q)
    change (Φ (c • X')) i.2 j.2 = (c • Φ X') i.2 j.2
    rw [map_smul]

/-- Right-factor analogue of the single-Kraus Kronecker formula. -/
private theorem identityTensorChannel_singleKraus_eq_kronecker
    {d k : Type u}
    [Fintype d] [DecidableEq d]
    [Fintype k] [DecidableEq k]
    (E : Matrix k k ℂ) (X : Matrix (d × k) (d × k) ℂ) :
    identityTensorChannel d k (singleKrausSuperoperator E) X =
      ((1 : Matrix d d ℂ) ⊗ₖ E) * X * (((1 : Matrix d d ℂ) ⊗ₖ E)ᴴ) := by
  ext i j
  rcases i with ⟨a, b⟩
  rcases j with ⟨c, e⟩
  calc
    identityTensorChannel d k (singleKrausSuperoperator E) X (a, b) (c, e)
        = ∑ x : k, ∑ y : k, E b x * X (a, x) (c, y) * star (E e y) := by
            calc
              identityTensorChannel d k (singleKrausSuperoperator E) X (a, b) (c, e)
                  = ∑ x, E b x * (∑ y, X (a, x) (c, y) * star (E e y)) := by
                      simp [identityTensorChannel, singleKrausSuperoperator, Matrix.mul_apply,
                        Matrix.conjTranspose_apply, Matrix.mul_assoc]
              _ = ∑ x : k, ∑ y : k, E b x * X (a, x) (c, y) * star (E e y) := by
                    simp_rw [Finset.mul_sum, mul_assoc]
    _ = ((((1 : Matrix d d ℂ) ⊗ₖ E) * X) * (((1 : Matrix d d ℂ) ⊗ₖ E)ᴴ)) (a, b) (c, e) := by
          have hleft :
              ∀ y : k, (((1 : Matrix d d ℂ) ⊗ₖ E) * X) (a, b) (c, y) =
                ∑ x : k, E b x * X (a, x) (c, y) := by
            intro y
            rw [Matrix.mul_apply, Fintype.sum_prod_type]
            rw [Finset.sum_eq_single a]
            · simp [Matrix.kroneckerMap_apply]
            · intro z _ hza
              have hza' : a ≠ z := by
                exact fun h => hza h.symm
              simp [Matrix.kroneckerMap_apply, Matrix.one_apply, hza']
            · simp
          have hright :
              ((((1 : Matrix d d ℂ) ⊗ₖ E) * X) * (((1 : Matrix d d ℂ) ⊗ₖ E)ᴴ)) (a, b) (c, e) =
                ∑ y : k, (((1 : Matrix d d ℂ) ⊗ₖ E) * X) (a, b) (c, y) * star (E e y) := by
            rw [Matrix.mul_apply, Fintype.sum_prod_type]
            rw [Finset.sum_eq_single c]
            · simp [Matrix.conjTranspose_apply, Matrix.kroneckerMap_apply]
            · intro z _ hzc
              have hzc' : c ≠ z := by
                exact fun h => hzc h.symm
              simp [Matrix.conjTranspose_apply, Matrix.kroneckerMap_apply, Matrix.one_apply, hzc']
            · simp
          rw [hright]
          rw [Finset.sum_comm]
          refine Finset.sum_congr rfl ?_
          intro y _
          rw [hleft]
          rw [Finset.sum_mul]

/-- Right-factor tensoring preserves quantumness of a channel. -/
theorem identityTensorChannel_isQuantumChannel
    {d k : Type u}
    [Fintype d] [DecidableEq d]
    [Fintype k] [DecidableEq k]
    {Φ : Channel k} (hΦ : IsQuantumChannel Φ) :
    IsQuantumChannel (identityTensorChannel d k Φ) := by
  rcases hΦ.kraus with ⟨r, E, hE, hsumE⟩
  refine
    { trace_preserving := ?_
      hermiticity_preserving := ?_
      kraus := ?_ }
  · intro X
    calc
      Matrix.trace (identityTensorChannel d k Φ X)
          = ∑ t : d, Matrix.trace (Φ (fun p q : k => X (t, p) (t, q))) := by
              rw [Matrix.trace, Fintype.sum_prod_type]
              simp [identityTensorChannel, Matrix.trace]
      _ = ∑ t : d, Matrix.trace (fun p q : k => X (t, p) (t, q)) := by
            apply Fintype.sum_congr
            intro t
            exact hΦ.trace_preserving (fun p q : k => X (t, p) (t, q))
      _ = Matrix.trace X := by
            rw [Matrix.trace, Fintype.sum_prod_type]
            simp [Matrix.trace]
  · intro X
    ext i j
    rcases i with ⟨a, b⟩
    rcases j with ⟨c, e⟩
    let Y : Matrix k k ℂ := fun p q => X (c, p) (a, q)
    have hY :
        Φ Yᴴ b e = ((Φ Y)ᴴ) b e := by
      exact congrArg (fun M : Matrix k k ℂ => M b e) (hΦ.hermiticity_preserving Y)
    simpa [Y, identityTensorChannel, Matrix.conjTranspose_apply] using hY
  · refine ⟨r, (fun i => (1 : Matrix d d ℂ) ⊗ₖ E i), ?_, ?_⟩
    · intro X
      ext i j
      rcases i with ⟨a, b⟩
      rcases j with ⟨c, e⟩
      let Xac : Matrix k k ℂ := fun p q => X (a, p) (c, q)
      calc
        identityTensorChannel d k Φ X (a, b) (c, e)
            = Φ Xac b e := by
                rfl
        _ = (∑ i : Fin r, E i * Xac * (E i)ᴴ) b e := by
              rw [hE Xac]
        _ = ∑ i : Fin r,
              identityTensorChannel d k
                (singleKrausSuperoperator (E i)) X (a, b) (c, e) := by
              rw [matrix_sum_apply (f := fun i : Fin r => E i * Xac * (E i)ᴴ) (a := b) (b := e)]
              simp [identityTensorChannel, singleKrausSuperoperator, Xac]
        _ = ∑ i : Fin r, ((((1 : Matrix d d ℂ) ⊗ₖ E i) * X) *
              (((1 : Matrix d d ℂ) ⊗ₖ E i)ᴴ)) (a, b) (c, e) := by
              apply Fintype.sum_congr
              intro i
              simpa using congrArg
                (fun M : Matrix (d × k) (d × k) ℂ => M (a, b) (c, e))
                (identityTensorChannel_singleKraus_eq_kronecker
                  (d := d) (k := k) (E := E i) (X := X))
        _ = (∑ i : Fin r, (((1 : Matrix d d ℂ) ⊗ₖ E i) * X) *
              (((1 : Matrix d d ℂ) ⊗ₖ E i)ᴴ)) (a, b) (c, e) := by
              rw [matrix_sum_apply
                (f := fun i : Fin r => (((1 : Matrix d d ℂ) ⊗ₖ E i) * X) *
                  (((1 : Matrix d d ℂ) ⊗ₖ E i)ᴴ))
                (a := (a, b)) (b := (c, e))]
    · calc
        ∑ i : Fin r, (((1 : Matrix d d ℂ) ⊗ₖ E i)ᴴ) * ((1 : Matrix d d ℂ) ⊗ₖ E i)
            = ∑ i : Fin r, (1 : Matrix d d ℂ) ⊗ₖ ((E i)ᴴ * E i) := by
                apply Fintype.sum_congr
                intro i
                calc
                  (((1 : Matrix d d ℂ) ⊗ₖ E i)ᴴ) * ((1 : Matrix d d ℂ) ⊗ₖ E i)
                      = (((1 : Matrix d d ℂ)ᴴ) ⊗ₖ (E i)ᴴ) * ((1 : Matrix d d ℂ) ⊗ₖ E i) := by
                          rw [Matrix.conjTranspose_kronecker]
                  _ = ((1 : Matrix d d ℂ)ᴴ * (1 : Matrix d d ℂ)) ⊗ₖ ((E i)ᴴ * E i) := by
                        rw [Matrix.mul_kronecker_mul]
                  _ = (1 : Matrix d d ℂ) ⊗ₖ ((E i)ᴴ * E i) := by
                        simp
        _ = (1 : Matrix d d ℂ) ⊗ₖ (∑ i : Fin r, (E i)ᴴ * E i) := by
              ext u v
              rcases u with ⟨a, b⟩
              rcases v with ⟨c, e⟩
              by_cases hac : a = c
              · rw [matrix_sum_apply (f := fun i : Fin r =>
                    kroneckerMap (fun x1 x2 => x1 * x2) (1 : Matrix d d ℂ) ((E i)ᴴ * E i))
                    (a := (a, b)) (b := (c, e))]
                simp [Matrix.kroneckerMap_apply, hac]
                rw [← matrix_sum_apply (f := fun i : Fin r => (E i)ᴴ * E i) (a := b) (b := e)]
              · rw [matrix_sum_apply (f := fun i : Fin r =>
                    kroneckerMap (fun x1 x2 => x1 * x2) (1 : Matrix d d ℂ) ((E i)ᴴ * E i))
                    (a := (a, b)) (b := (c, e))]
                simp [Matrix.kroneckerMap_apply, hac]
        _ = (1 : Matrix d d ℂ) ⊗ₖ (1 : Matrix k k ℂ) := by
              rw [hsumE]
        _ = 1 := by
              simpa using (Matrix.one_kronecker_one (α := ℂ) (m := d) (n := k))

/-- The recursive `m`-use channel obtained from a single-use physical channel. -/
def tensorPowerChannel
    {phys : Type u}
    [Fintype phys] [DecidableEq phys]
    (T : Channel phys) : (m : ℕ) → Channel (TensorPowerType phys m)
  | 0 => LinearMap.id
  | n + 1 =>
      (identityTensorChannel (TensorPowerType phys n) phys T).comp
        (tensorWithIdentity (TensorPowerType phys n) phys (tensorPowerChannel T n))

theorem tensorPowerChannel_succ_eq
    {phys : Type u}
    [Fintype phys] [DecidableEq phys]
    (T : Channel phys) (n : ℕ) :
    tensorPowerChannel T (n + 1) =
      (identityTensorChannel (TensorPowerType phys n) phys T).comp
        (tensorWithIdentity (TensorPowerType phys n) phys (tensorPowerChannel T n)) := by
  rfl

theorem tensorPowerChannel_zero_eq
    {phys : Type u}
    [Fintype phys] [DecidableEq phys]
    (T : Channel phys) :
    tensorPowerChannel T 0 = (LinearMap.id : Channel (TensorPowerType phys 0)) := rfl

theorem tensorPowerChannel_one_eq
    {phys : Type u}
    [Fintype phys] [DecidableEq phys]
    (T : Channel phys) :
    tensorPowerChannel T 1 =
      identityTensorChannel (TensorPowerType phys 0) phys T := by
  ext X i j
  rcases i with ⟨⟨⟩, a⟩
  rcases j with ⟨⟨⟩, b⟩
  rfl

/-- On the trivial left factor `PUnit`, right-factor extension does not change the diamond norm. -/
theorem diamondOp_identityTensorChannel_punit_eq
    {phys : Type u}
    [Fintype phys] [DecidableEq phys]
    [Nonempty phys]
    (Φ : Channel phys) :
    diamondOp (identityTensorChannel PUnit phys Φ) = diamondOp Φ := by
  unfold diamondOp diamondNorm diamondNormAt
  apply le_antisymm
  · refine csSup_le ?_ ?_
    · let i0 : (PUnit × phys) × (PUnit × phys) :=
        ((PUnit.unit, Classical.choice ‹Nonempty phys›), (PUnit.unit, Classical.choice ‹Nonempty phys›))
      let ψ : (PUnit × phys) × (PUnit × phys) → ℂ := Pi.single i0 1
      let ρ0 : Matrix ((PUnit × phys) × (PUnit × phys)) ((PUnit × phys) × (PUnit × phys)) ℂ :=
        Matrix.vecMulVec ψ (star ψ)
      have hρ0 : IsDensityState ρ0 := by
        refine ⟨?_, ?_⟩
        · simpa [ρ0, ψ] using Matrix.posSemidef_vecMulVec_self_star ψ
        · simp [ρ0, ψ, Matrix.trace_vecMulVec]
      exact ⟨traceNormOp (tensorWithIdentity (PUnit × phys) (PUnit × phys)
        (identityTensorChannel PUnit phys Φ) ρ0), ⟨⟨ρ0, hρ0⟩, rfl⟩⟩
    · intro r hr
      rcases hr with ⟨ρ, rfl⟩
      let e : PUnit × phys ≃ phys := Equiv.punitProd phys
      let ρ' : DensityState (phys × phys) := ⟨Matrix.reindex (Equiv.prodCongr e e) (Equiv.prodCongr e e) ρ.1,
        isDensityState_reindex (Equiv.prodCongr e e) ρ.2⟩
      calc
        traceNormOp
            (tensorWithIdentity (PUnit × phys) (PUnit × phys)
              (identityTensorChannel PUnit phys Φ) ρ.1)
            =
          traceNormOp
            (Matrix.reindex (Equiv.prodCongr e e) (Equiv.prodCongr e e)
              (tensorWithIdentity (PUnit × phys) (PUnit × phys)
                (identityTensorChannel PUnit phys Φ) ρ.1)) := by
                  symm
                  exact traceNormOp_reindex (Equiv.prodCongr e e)
                    (tensorWithIdentity (PUnit × phys) (PUnit × phys)
                      (identityTensorChannel PUnit phys Φ) ρ.1)
        _ =
          traceNormOp (tensorWithIdentity phys phys Φ ρ'.1) := by
            have hmat :
                Matrix.reindex (Equiv.prodCongr e e) (Equiv.prodCongr e e)
                  (tensorWithIdentity (PUnit × phys) (PUnit × phys)
                    (identityTensorChannel PUnit phys Φ) ρ.1) =
                  tensorWithIdentity phys phys Φ ρ'.1 := by
              ext i j
              rcases i with ⟨a, b⟩
              rcases j with ⟨c, d⟩
              rfl
            rw [hmat]
        _ ≤ diamondOp Φ := traceNorm_apply_le_diamond Φ ρ'
  · refine csSup_le ?_ ?_
    · let i0 : phys × phys :=
        (Classical.choice ‹Nonempty phys›, Classical.choice ‹Nonempty phys›)
      let ψ : phys × phys → ℂ := Pi.single i0 1
      let ρ0 : Matrix (phys × phys) (phys × phys) ℂ := Matrix.vecMulVec ψ (star ψ)
      have hρ0 : IsDensityState ρ0 := by
        refine ⟨?_, ?_⟩
        · simpa [ρ0, ψ] using Matrix.posSemidef_vecMulVec_self_star ψ
        · simp [ρ0, ψ, Matrix.trace_vecMulVec]
      exact ⟨traceNormOp (tensorWithIdentity phys phys Φ ρ0), ⟨⟨ρ0, hρ0⟩, rfl⟩⟩
    · intro r hr
      rcases hr with ⟨ρ, rfl⟩
      let e : PUnit × phys ≃ phys := Equiv.punitProd phys
      let ρ' : DensityState ((PUnit × phys) × (PUnit × phys)) :=
        ⟨Matrix.reindex (Equiv.prodCongr e.symm e.symm) (Equiv.prodCongr e.symm e.symm) ρ.1,
          isDensityState_reindex (Equiv.prodCongr e.symm e.symm) ρ.2⟩
      calc
        traceNormOp (tensorWithIdentity phys phys Φ ρ.1)
            =
          traceNormOp
            (Matrix.reindex (Equiv.prodCongr e.symm e.symm) (Equiv.prodCongr e.symm e.symm)
              (tensorWithIdentity phys phys Φ ρ.1)) := by
                symm
                exact traceNormOp_reindex (Equiv.prodCongr e.symm e.symm)
                  (tensorWithIdentity phys phys Φ ρ.1)
        _ =
          traceNormOp
            (tensorWithIdentity (PUnit × phys) (PUnit × phys)
              (identityTensorChannel PUnit phys Φ) ρ'.1) := by
            have hmat :
                Matrix.reindex (Equiv.prodCongr e.symm e.symm) (Equiv.prodCongr e.symm e.symm)
                  (tensorWithIdentity phys phys Φ ρ.1) =
                tensorWithIdentity (PUnit × phys) (PUnit × phys)
                  (identityTensorChannel PUnit phys Φ) ρ'.1 := by
              ext i j
              rcases i with ⟨⟨⟨⟩, a⟩, b⟩
              rcases j with ⟨⟨⟨⟩, c⟩, d⟩
              rfl
            rw [hmat]
        _ ≤ diamondOp (identityTensorChannel PUnit phys Φ) :=
            traceNorm_apply_le_diamond (identityTensorChannel PUnit phys Φ) ρ'

/-- The transposed one-use recursive tensor-power channel is exactly the ordinary
transposed base channel. -/
theorem diamondOp_transpose_tensorPowerChannel_one_eq
    {phys : Type u}
    [Fintype phys] [DecidableEq phys] [Nonempty phys]
    (T : Channel phys) :
    diamondOp ((transposeMap (TensorPowerType phys 1)).comp (tensorPowerChannel T 1)) =
      diamondOp ((transposeMap phys).comp T) := by
  simpa [TensorPowerType, tensorPowerChannel_one_eq] using
    diamondOp_identityTensorChannel_punit_eq ((transposeMap phys).comp T)

/-- Partial transpose on the right tensor factor. -/
def partialTransposeRightMap
    (d k : Type u)
    [Fintype d] [DecidableEq d]
    [Fintype k] [DecidableEq k] : Channel (d × k) where
  toFun := fun X i j => X (i.1, j.2) (j.1, i.2)
  map_add' := by
    intro X Y
    ext i j
    simp
  map_smul' := by
    intro c X
    ext i j
    simp

/-- Right-factor analogue of `tensorWithIdentity_comp_transpose`. -/
theorem identityTensorChannel_comp_transpose
    {d k : Type u}
    [Fintype d] [DecidableEq d]
    [Fintype k] [DecidableEq k]
    (Φ : Channel k) :
    identityTensorChannel d k ((transposeMap k).comp Φ) =
      (partialTransposeRightMap d k).comp (identityTensorChannel d k Φ) := by
  ext X i j
  simp [identityTensorChannel, partialTransposeRightMap, LinearMap.comp_apply, transposeMap]

/-- Full transposition on a product space is the composition of left and right partial
transpositions. -/
theorem transpose_prod_eq_partialLeft_comp_partialRight
    {d k : Type u}
    [Fintype d] [DecidableEq d]
    [Fintype k] [DecidableEq k] :
    transposeMap (d × k) =
      (partialTransposeMap d k).comp (partialTransposeRightMap d k) := by
  ext X i j
  simp [partialTransposeMap, partialTransposeRightMap, LinearMap.comp_apply, transposeMap]

/-- Recursive decomposition of the transposed tensor-power channel. This is the exact
induction form needed for proving multiplicative bounds on
`diamondOp ((transposeMap _).comp (tensorPowerChannel T m))`. -/
theorem transpose_tensorPowerChannel_succ_eq
    {phys : Type u}
    [Fintype phys] [DecidableEq phys]
    (T : Channel phys) (n : ℕ) :
    (transposeMap (TensorPowerType phys (n + 1))).comp (tensorPowerChannel T (n + 1)) =
      (identityTensorChannel (TensorPowerType phys n) phys ((transposeMap phys).comp T)).comp
        (tensorWithIdentity (TensorPowerType phys n) phys
          ((transposeMap (TensorPowerType phys n)).comp (tensorPowerChannel T n))) := by
  rfl

/-- The recursive `m`-use channel is quantum whenever the base channel is. -/
theorem tensorPowerChannel_isQuantumChannel
    {phys : Type u}
    [Fintype phys] [DecidableEq phys]
    {T : Channel phys} (hT : IsQuantumChannel T) :
    ∀ m : ℕ, IsQuantumChannel (tensorPowerChannel T m)
  | 0 => idChannel_isQuantumChannel
  | n + 1 => by
      have hprev : IsQuantumChannel (tensorPowerChannel T n) :=
        tensorPowerChannel_isQuantumChannel (hT := hT) n
      have hleftSuper :
          IsQuantumSuperoperator
            (tensorWithIdentity (TensorPowerType phys n) phys (tensorPowerChannel T n)) := by
              simpa [superoperatorWithIdentity_eq_tensorWithIdentity] using
                (superoperatorWithIdentity_isQuantumSuperoperator
                  (din := TensorPowerType phys n)
                  (dout := TensorPowerType phys n)
                  (k := phys)
                  (Φ := tensorPowerChannel T n)
                  (hΦ := IsQuantumChannel.toQuantumSuperoperator hprev))
      have hleft :
          IsQuantumChannel
            (tensorWithIdentity (TensorPowerType phys n) phys (tensorPowerChannel T n)) :=
        IsQuantumSuperoperator.toQuantumChannel hleftSuper
      have hright :
          IsQuantumChannel (identityTensorChannel (TensorPowerType phys n) phys T) :=
        identityTensorChannel_isQuantumChannel hT
      have hcompSuper :
          IsQuantumSuperoperator
            ((identityTensorChannel (TensorPowerType phys n) phys T).comp
              (tensorWithIdentity (TensorPowerType phys n) phys (tensorPowerChannel T n))) :=
        (IsQuantumChannel.toQuantumSuperoperator hright).comp
          (IsQuantumChannel.toQuantumSuperoperator hleft)
      exact IsQuantumSuperoperator.toQuantumChannel hcompSuper

end
end Diamond
