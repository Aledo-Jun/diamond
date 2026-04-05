import Diamond.HolevoWerner.Common

open scoped BigOperators
open scoped ComplexOrder
open scoped Kronecker
open scoped MatrixOrder
open scoped Matrix.Norms.Frobenius
open Matrix

namespace Diamond

/- Shared coding definitions live in `Diamond.HolevoWerner.Common`; the rest of the
Holevo-Werner development builds on top of them. -/

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

/-- A rectangular completely positive trace-preserving map, represented through a finite
Kraus family. This is the natural notion for encoder and decoder maps whose input and
output dimensions may differ. -/
structure IsQuantumSuperoperator
    {din dout : Type u}
    [Fintype din] [DecidableEq din]
    [Fintype dout] [DecidableEq dout]
    (Φ : Superoperator din dout) : Prop where
  trace_preserving : ∀ X, Matrix.trace (Φ X) = Matrix.trace X
  hermiticity_preserving : ∀ X, Φ Xᴴ = (Φ X)ᴴ
  kraus :
    ∃ (ι : Type u), ∃ (_ : Fintype ι), ∃ (_ : DecidableEq ι),
      ∃ E : ι → Matrix dout din ℂ,
        (∀ X, Φ X = ∑ i, E i * X * (E i)ᴴ) ∧
        (∑ i, (E i)ᴴ * E i = 1)

/-- Ordinary square quantum channels are rectangular quantum superoperators. -/
theorem IsQuantumChannel.toQuantumSuperoperator
    {d : Type u}
    [Fintype d] [DecidableEq d]
    {T : Channel d} (hT : IsQuantumChannel T) :
    IsQuantumSuperoperator T := by
  rcases hT.kraus with ⟨r, E, hE, hsumE⟩
  let e : Fin r ≃ ULift.{u} (Fin r) := Equiv.ulift.symm
  let E' : ULift.{u} (Fin r) → Matrix d d ℂ := fun i => E i.down
  refine
    { trace_preserving := hT.trace_preserving
      hermiticity_preserving := hT.hermiticity_preserving
      kraus := ?_ }
  refine ⟨ULift.{u} (Fin r), inferInstance, inferInstance, E', ?_, ?_⟩
  · intro X
    calc
      T X = ∑ i : Fin r, E i * X * (E i)ᴴ := hE X
      _ = ∑ j : ULift.{u} (Fin r), E' j * X * (E' j)ᴴ := by
            exact
              Fintype.sum_equiv e
                (fun i : Fin r => E i * X * (E i)ᴴ)
                (fun j : ULift.{u} (Fin r) => E' j * X * (E' j)ᴴ)
                (fun i => by simp [e, E'])
  · calc
      ∑ j : ULift.{u} (Fin r), (E' j)ᴴ * E' j = ∑ i : Fin r, (E i)ᴴ * E i := by
        exact
          (Fintype.sum_equiv e
            (fun i : Fin r => (E i)ᴴ * E i)
            (fun j : ULift.{u} (Fin r) => (E' j)ᴴ * E' j)
            (fun i => by simp [e, E'])).symm
      _ = 1 := hsumE

/-- A square quantum superoperator can be repackaged as an ordinary quantum channel. -/
theorem IsQuantumSuperoperator.toQuantumChannel
    {d : Type u}
    [Fintype d] [DecidableEq d]
    {T : Channel d} (hT : IsQuantumSuperoperator T) :
    IsQuantumChannel T := by
  rcases hT.kraus with ⟨ι, hι, hdecι, E, hE, hsumE⟩
  letI := hι
  letI := hdecι
  let e : ι ≃ Fin (Fintype.card ι) := Fintype.equivFin ι
  let E' : Fin (Fintype.card ι) → Matrix d d ℂ := fun i => E (e.symm i)
  refine
    { trace_preserving := hT.trace_preserving
      hermiticity_preserving := hT.hermiticity_preserving
      kraus := ?_ }
  refine ⟨Fintype.card ι, E', ?_, ?_⟩
  · intro X
    calc
      T X = ∑ i : ι, E i * X * (E i)ᴴ := hE X
      _ = ∑ j : Fin (Fintype.card ι), E (e.symm j) * X * (E (e.symm j))ᴴ := by
            exact
              (Fintype.sum_equiv e
                (fun i : ι => E i * X * (E i)ᴴ)
                (fun j : Fin (Fintype.card ι) => E (e.symm j) * X * (E (e.symm j))ᴴ)
                (fun i => by simp [e]))
  · calc
      ∑ j : Fin (Fintype.card ι), (E' j)ᴴ * E' j
          = ∑ i : ι, (E i)ᴴ * E i := by
              exact
                (Fintype.sum_equiv e
                  (fun i : ι => (E i)ᴴ * E i)
                  (fun j : Fin (Fintype.card ι) => (E (e.symm j))ᴴ * E (e.symm j))
                  (fun i => by simp [e])).symm
      _ = 1 := hsumE

/-- Composition of rectangular quantum superoperators is again a rectangular quantum
superoperator. -/
theorem IsQuantumSuperoperator.comp
    {a b c : Type u}
    [Fintype a] [DecidableEq a]
    [Fintype b] [DecidableEq b]
    [Fintype c] [DecidableEq c]
    {Φ : Superoperator a b} {Ψ : Superoperator b c}
    (hΨ : IsQuantumSuperoperator Ψ) (hΦ : IsQuantumSuperoperator Φ) :
    IsQuantumSuperoperator (Ψ.comp Φ) := by
  rcases hΦ.kraus with ⟨ι, hι, hdecι, E, hE, hsumE⟩
  rcases hΨ.kraus with ⟨κ, hκ, hdecκ, F, hF, hsumF⟩
  letI := hι
  letI := hdecι
  letI := hκ
  letI := hdecκ
  let K : ι × κ → Matrix c a ℂ := fun p => F p.2 * E p.1
  refine
    { trace_preserving := ?_
      hermiticity_preserving := ?_
      kraus := ?_ }
  · intro X
    calc
      Matrix.trace ((Ψ.comp Φ) X) = Matrix.trace (Ψ (Φ X)) := by rfl
      _ = Matrix.trace (Φ X) := hΨ.trace_preserving (Φ X)
      _ = Matrix.trace X := hΦ.trace_preserving X
  · intro X
    simp [LinearMap.comp_apply, hΨ.hermiticity_preserving, hΦ.hermiticity_preserving]
  · refine ⟨ι × κ, inferInstance, inferInstance, K, ?_, ?_⟩
    · intro X
      calc
        (Ψ.comp Φ) X = Ψ (Φ X) := rfl
        _ = Ψ (∑ i : ι, E i * X * (E i)ᴴ) := by rw [hE]
        _ = ∑ i : ι, Ψ (E i * X * (E i)ᴴ) := by rw [map_sum]
        _ = ∑ i : ι, ∑ j : κ, F j * (E i * X * (E i)ᴴ) * (F j)ᴴ := by
              apply Fintype.sum_congr
              intro i
              rw [hF]
        _ = ∑ i : ι, ∑ j : κ, K (i, j) * X * (K (i, j))ᴴ := by
              apply Fintype.sum_congr
              intro i
              apply Fintype.sum_congr
              intro j
              simp [K, Matrix.conjTranspose_mul, Matrix.mul_assoc]
        _ = ∑ p : ι × κ, K p * X * (K p)ᴴ := by
              simpa [K] using
                (Fintype.sum_prod_type' (fun i j => K (i, j) * X * (K (i, j))ᴴ)).symm
    · calc
        ∑ p : ι × κ, (K p)ᴴ * K p
            = ∑ p : ι × κ, (E p.1)ᴴ * ((F p.2)ᴴ * (F p.2 * E p.1)) := by
                apply Fintype.sum_congr
                intro p
                simp [K, Matrix.conjTranspose_mul, Matrix.mul_assoc]
        _ = ∑ i : ι, ∑ j : κ, (E i)ᴴ * ((F j)ᴴ * (F j * E i)) := by
              simpa using
                Fintype.sum_prod_type' (fun i j => (E i)ᴴ * ((F j)ᴴ * (F j * E i)))
        _ = ∑ i : ι, ∑ j : κ, (E i)ᴴ * ((F j)ᴴ * F j) * E i := by
              apply Fintype.sum_congr
              intro i
              apply Fintype.sum_congr
              intro j
              simp [Matrix.mul_assoc]
        _ = ∑ i : ι, (E i)ᴴ * (∑ j : κ, (F j)ᴴ * F j) * E i := by
              apply Fintype.sum_congr
              intro i
              symm
              rw [Matrix.mul_sum, Matrix.sum_mul]
        _ = ∑ i : ι, (E i)ᴴ * E i := by
              rw [hsumF]
              simp
        _ = 1 := hsumE

/-- The effective message-space channel induced by quantum encoder, channel uses,
and quantum decoder is itself a quantum superoperator. -/
theorem effectiveChannel_isQuantumSuperoperator
    {phys msg : Type u}
    [Fintype phys] [DecidableEq phys]
    [Fintype msg] [DecidableEq msg]
    {encoder : Superoperator msg phys}
    {decoder : Superoperator phys msg}
    {tensorPower : Channel phys}
    (hencoder : IsQuantumSuperoperator encoder)
    (htensorPower : IsQuantumChannel tensorPower)
    (hdecoder : IsQuantumSuperoperator decoder) :
    IsQuantumSuperoperator (effectiveChannel encoder decoder tensorPower) := by
  simpa [effectiveChannel] using
    hdecoder.comp ((IsQuantumChannel.toQuantumSuperoperator htensorPower).comp hencoder)

/-- The effective message-space channel induced by quantum encoder, channel uses,
and quantum decoder is an ordinary quantum channel. -/
theorem effectiveChannel_isQuantumChannel
    {phys msg : Type u}
    [Fintype phys] [DecidableEq phys]
    [Fintype msg] [DecidableEq msg]
    {encoder : Superoperator msg phys}
    {decoder : Superoperator phys msg}
    {tensorPower : Channel phys}
    (hencoder : IsQuantumSuperoperator encoder)
    (htensorPower : IsQuantumChannel tensorPower)
    (hdecoder : IsQuantumSuperoperator decoder) :
    IsQuantumChannel (effectiveChannel encoder decoder tensorPower) := by
  exact
    (effectiveChannel_isQuantumSuperoperator hencoder htensorPower hdecoder).toQuantumChannel

/-- Rectangular quantum superoperators preserve positive semidefiniteness. -/
theorem quantumSuperoperator_maps_posSemidef
    {din dout : Type u}
    [Fintype din] [DecidableEq din]
    [Fintype dout] [DecidableEq dout]
    (Φ : Superoperator din dout) (hΦ : IsQuantumSuperoperator Φ)
    {A : Matrix din din ℂ} (hA : A.PosSemidef) :
    (Φ A).PosSemidef := by
  rcases hΦ.kraus with ⟨ι, hι, hdecι, E, hE, hsumE⟩
  letI := hι
  letI := hdecι
  have hsum :
      (∑ i : ι, E i * A * (E i)ᴴ).PosSemidef := by
    have hsum_nonneg :
        0 ≤ ∑ i : ι, E i * A * (E i)ᴴ := by
      exact Finset.sum_nonneg (fun i _ => (hA.mul_mul_conjTranspose_same (E i)).nonneg)
    exact hsum_nonneg.posSemidef
  rw [hE]
  exact hsum

/-- Rectangular quantum superoperators send density states to density states. -/
theorem quantumSuperoperator_maps_densityState
    {din dout : Type u}
    [Fintype din] [DecidableEq din]
    [Fintype dout] [DecidableEq dout]
    (Φ : Superoperator din dout) (hΦ : IsQuantumSuperoperator Φ)
    {ρ : Matrix din din ℂ} (hρ : IsDensityState ρ) :
    IsDensityState (Φ ρ) := by
  refine ⟨quantumSuperoperator_maps_posSemidef Φ hΦ hρ.1, ?_⟩
  rw [hΦ.trace_preserving]
  exact hρ.2

/-- Rectangular quantum superoperators contract the concrete trace norm on Hermitian
inputs. -/
theorem traceNormOp_quantumSuperoperator_le_of_hermitian
    {din dout : Type u}
    [Fintype din] [DecidableEq din]
    [Fintype dout] [DecidableEq dout]
    (Φ : Superoperator din dout) (hΦ : IsQuantumSuperoperator Φ)
    {X : Matrix din din ℂ} (hX : Matrix.IsHermitian X) :
    traceNormOp (Φ X) ≤ traceNormOp X := by
  let U : Matrix din din ℂ := hX.eigenvectorUnitary
  let Ustar : Matrix din din ℂ := star hX.eigenvectorUnitary
  let D : Matrix din din ℂ := Matrix.diagonal (fun i => ((hX.eigenvalues i : ℝ) : ℂ))
  let Dpos : Matrix din din ℂ :=
    Matrix.diagonal (fun i => ((if 0 ≤ hX.eigenvalues i then hX.eigenvalues i else 0 : ℝ) : ℂ))
  let Dneg : Matrix din din ℂ :=
    Matrix.diagonal (fun i => ((if 0 ≤ hX.eigenvalues i then 0 else -hX.eigenvalues i : ℝ) : ℂ))
  let P : Matrix din din ℂ := U * Dpos * Ustar
  let Q : Matrix din din ℂ := U * Dneg * Ustar
  have hU_right : U * Ustar = 1 := by
    simpa [U, Ustar] using (Matrix.mem_unitaryGroup_iff).1 hX.eigenvectorUnitary.property
  have hU_left : Ustar * U = 1 := by
    simpa [U, Ustar] using (Matrix.mem_unitaryGroup_iff').1 hX.eigenvectorUnitary.property
  have hDpos_pos : Dpos.PosSemidef := by
    refine Matrix.PosSemidef.diagonal ?_
    intro i
    by_cases h : 0 ≤ hX.eigenvalues i
    · simp [h]
    · simp [h]
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
  have hdiag_split : D = Dpos - Dneg := by
    ext i j
    by_cases hij : i = j
    · subst hij
      by_cases h : 0 ≤ hX.eigenvalues i
      · simp [D, Dpos, Dneg, h]
      · have hlt : hX.eigenvalues i < 0 := lt_of_not_ge h
        simp [D, Dpos, Dneg, h]
    · simp [D, Dpos, Dneg, hij]
  have hdecomp : X = P - Q := by
    calc
      X = U * D * Ustar := by
            simpa [U, Ustar, D, Matrix.mul_assoc, Unitary.conjStarAlgAut_apply] using
              hX.spectral_theorem
      _ = U * (Dpos - Dneg) * Ustar := by rw [hdiag_split]
      _ = P - Q := by
            simp [P, Q, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_assoc]
  have htraceP :
      Complex.re (Matrix.trace P) =
        ∑ i, (if 0 ≤ hX.eigenvalues i then hX.eigenvalues i else 0) := by
    have htraceP_eq : Matrix.trace P = Matrix.trace Dpos := by
      calc
        Matrix.trace P = Matrix.trace (U * Dpos * Ustar) := by rfl
        _ = Matrix.trace (Ustar * U * Dpos) := by
              simpa [Matrix.mul_assoc] using Matrix.trace_mul_cycle U Dpos Ustar
        _ = Matrix.trace Dpos := by simp [hU_left]
    rw [htraceP_eq]
    simp [Dpos, Matrix.trace]
  have htraceQ :
      Complex.re (Matrix.trace Q) =
        ∑ i, (if 0 ≤ hX.eigenvalues i then 0 else -hX.eigenvalues i) := by
    have htraceQ_eq : Matrix.trace Q = Matrix.trace Dneg := by
      calc
        Matrix.trace Q = Matrix.trace (U * Dneg * Ustar) := by rfl
        _ = Matrix.trace (Ustar * U * Dneg) := by
              simpa [Matrix.mul_assoc] using Matrix.trace_mul_cycle U Dneg Ustar
        _ = Matrix.trace Dneg := by simp [hU_left]
    rw [htraceQ_eq]
    simp [Dneg, Matrix.trace]
  have htraceNormX :
      traceNormOp X = Complex.re (Matrix.trace P) + Complex.re (Matrix.trace Q) := by
    calc
      traceNormOp X = ∑ i, |hX.eigenvalues i| := by
            simpa using traceNormOp_hermitian_eq_sum_abs_eigenvalues hX
      _ = ∑ i,
            ((if 0 ≤ hX.eigenvalues i then hX.eigenvalues i else 0) +
              (if 0 ≤ hX.eigenvalues i then 0 else -hX.eigenvalues i)) := by
            refine Finset.sum_congr rfl ?_
            intro i hi
            by_cases h : 0 ≤ hX.eigenvalues i
            · simp [h, abs_of_nonneg h]
            · have hlt : hX.eigenvalues i < 0 := lt_of_not_ge h
              simp [h, abs_of_neg hlt]
      _ = ∑ i, (if 0 ≤ hX.eigenvalues i then hX.eigenvalues i else 0) +
            ∑ i, (if 0 ≤ hX.eigenvalues i then 0 else -hX.eigenvalues i) := by
            rw [Finset.sum_add_distrib]
      _ = Complex.re (Matrix.trace P) + Complex.re (Matrix.trace Q) := by
            rw [htraceP, htraceQ]
  have hΦX_decomp : Φ X = Φ P - Φ Q := by rw [hdecomp, map_sub]
  have hΦP_pos : (Φ P).PosSemidef := quantumSuperoperator_maps_posSemidef Φ hΦ hP_pos
  have hΦQ_pos : (Φ Q).PosSemidef := quantumSuperoperator_maps_posSemidef Φ hΦ hQ_pos
  have htri :
      traceNormOp (Φ X) ≤ traceNormOp (Φ P) + traceNormOp (Φ Q) := by
    rw [hΦX_decomp, sub_eq_add_neg]
    have hΦP_herm : Matrix.IsHermitian (Φ P) := hΦP_pos.isHermitian
    have hneg_herm : Matrix.IsHermitian (- (Φ Q)) := hΦQ_pos.isHermitian.neg
    simpa [traceNormOp_neg] using traceNormOp_add_le_of_hermitian hΦP_herm hneg_herm
  calc
    traceNormOp (Φ X) ≤ traceNormOp (Φ P) + traceNormOp (Φ Q) := htri
    _ = Complex.re (Matrix.trace (Φ P)) + Complex.re (Matrix.trace (Φ Q)) := by
          rw [traceNormOp_posSemidef_eq_trace hΦP_pos, traceNormOp_posSemidef_eq_trace hΦQ_pos]
    _ = Complex.re (Matrix.trace P) + Complex.re (Matrix.trace Q) := by
          rw [hΦ.trace_preserving P, hΦ.trace_preserving Q]
    _ = traceNormOp X := htraceNormX.symm

/-- Conjugation of a rectangular superoperator by transposition on input and output. -/
def transposeConjugateSuperoperator
    {din dout : Type u}
    [Fintype din] [DecidableEq din]
    [Fintype dout] [DecidableEq dout]
    (Φ : Superoperator din dout) : Superoperator din dout :=
  ((transposeMap dout).comp Φ).comp (transposeMap din)

/-- Transpose-conjugation preserves the rectangular CPTP structure. -/
theorem transposeConjugateSuperoperator_isQuantumSuperoperator
    {din dout : Type u}
    [Fintype din] [DecidableEq din]
    [Fintype dout] [DecidableEq dout]
    {Φ : Superoperator din dout}
    (hΦ : IsQuantumSuperoperator Φ) :
    IsQuantumSuperoperator (transposeConjugateSuperoperator Φ) := by
  rcases hΦ.kraus with ⟨ι, hι, hdecι, E, hE, hsumE⟩
  letI := hι
  letI := hdecι
  let F : ι → Matrix dout din ℂ := fun i => (E i).map star
  refine
    { trace_preserving := ?_
      hermiticity_preserving := ?_
      kraus := ?_ }
  · intro X
    calc
      Matrix.trace ((transposeConjugateSuperoperator Φ) X)
          = Matrix.trace (Φ X.transpose) := by
              rw [transposeConjugateSuperoperator]
              simp [LinearMap.comp_apply, transposeMap, Matrix.trace_transpose]
      _ = Matrix.trace X.transpose := hΦ.trace_preserving X.transpose
      _ = Matrix.trace X := Matrix.trace_transpose X
  · intro X
    have hherm :
        Φ (X.map star) = (Φ X.transpose)ᴴ := by
      simpa [Matrix.transpose_conjTranspose] using hΦ.hermiticity_preserving X.transpose
    have hleft :
        transposeConjugateSuperoperator Φ Xᴴ = (Φ (X.map star)).transpose := by
      rw [transposeConjugateSuperoperator]
      simp [LinearMap.comp_apply, transposeMap, Matrix.conjTranspose_transpose]
    have hright :
        (transposeConjugateSuperoperator Φ X)ᴴ = (Φ X.transpose).map star := by
      rw [transposeConjugateSuperoperator]
      simp [LinearMap.comp_apply, transposeMap, Matrix.transpose_conjTranspose]
    calc
      transposeConjugateSuperoperator Φ Xᴴ
          = (Φ (X.map star)).transpose := hleft
      _ = ((Φ X.transpose)ᴴ).transpose := by rw [hherm]
      _ = (Φ X.transpose).map star := by rw [Matrix.conjTranspose_transpose]
      _ = (transposeConjugateSuperoperator Φ X)ᴴ := by rw [hright]
  · refine ⟨ι, inferInstance, inferInstance, F, ?_, ?_⟩
    · intro X
      calc
        transposeConjugateSuperoperator Φ X
            = (∑ i : ι, E i * X.transpose * (E i)ᴴ).transpose := by
                rw [transposeConjugateSuperoperator, LinearMap.comp_apply, LinearMap.comp_apply, hE]
                rfl
        _ = ∑ i : ι, ((E i) * X.transpose * (E i)ᴴ).transpose := by
              rw [Matrix.transpose_sum]
        _ = ∑ i : ι, F i * X * (F i)ᴴ := by
              apply Fintype.sum_congr
              intro i
              have hFi : F i = (E i).transposeᴴ := by
                simpa [F] using (Matrix.transpose_conjTranspose (E i))
              have hleft : ((E i)ᴴ).transpose = F i := by
                simpa [F] using (Matrix.conjTranspose_transpose (E i))
              have hright : (E i).transpose = (F i)ᴴ := by
                rw [hFi]
                simp
              calc
                ((E i) * X.transpose * (E i)ᴴ).transpose
                    = ((E i)ᴴ).transpose * X * (E i).transpose := by
                        rw [Matrix.transpose_mul, Matrix.transpose_mul]
                        simp [Matrix.mul_assoc]
                _ = F i * X * (F i)ᴴ := by
                      rw [hleft, hright]
    · calc
        ∑ i : ι, (F i)ᴴ * F i = ∑ i : ι, ((E i)ᴴ * E i).transpose := by
          apply Fintype.sum_congr
          intro i
          have hFi : F i = (E i).transposeᴴ := by
            simpa [F] using (Matrix.transpose_conjTranspose (E i))
          have hleft : (F i)ᴴ = (E i).transpose := by
            rw [hFi]
            simp
          calc
            (F i)ᴴ * F i = (E i).transpose * (E i).transposeᴴ := by
              rw [hleft, hFi]
          _ = ((E i)ᴴ * E i).transpose := by
              rw [Matrix.transpose_mul]
              rw [Matrix.conjTranspose_transpose, Matrix.transpose_conjTranspose]
        _ = (∑ i : ι, (E i)ᴴ * E i).transpose := by
              rw [Matrix.transpose_sum]
        _ = 1 := by
              rw [hsumE]
              simp

/-- The transpose-conjugated rectangular superoperator contracts trace norm on Hermitian
inputs. -/
theorem traceNormOp_transposeConjugateSuperoperator_le_of_hermitian
    {din dout : Type u}
    [Fintype din] [DecidableEq din]
    [Fintype dout] [DecidableEq dout]
    {Φ : Superoperator din dout}
    (hΦ : IsQuantumSuperoperator Φ)
    {X : Matrix din din ℂ} (hX : Matrix.IsHermitian X) :
    traceNormOp (transposeConjugateSuperoperator Φ X) ≤ traceNormOp X := by
  exact
    traceNormOp_quantumSuperoperator_le_of_hermitian
      (transposeConjugateSuperoperator Φ)
      (transposeConjugateSuperoperator_isQuantumSuperoperator hΦ) hX

/-- The transpose map is Hermiticity-preserving. -/
theorem transposeMap_hermiticityPreserving
    {d : Type u}
    [Fintype d] [DecidableEq d]
    (X : Matrix d d ℂ) :
    transposeMap d Xᴴ = (transposeMap d X)ᴴ := by
  ext i j
  simp [transposeMap, Matrix.conjTranspose_apply]

/-- Composition preserves Hermiticity-preservation for rectangular superoperators. -/
theorem hermiticityPreserving_comp
    {a b c : Type u}
    [Fintype a] [DecidableEq a]
    [Fintype b] [DecidableEq b]
    [Fintype c] [DecidableEq c]
    {Φ : Superoperator a b} {Ψ : Superoperator b c}
    (hΨ : ∀ X, Ψ Xᴴ = (Ψ X)ᴴ)
    (hΦ : ∀ X, Φ Xᴴ = (Φ X)ᴴ) :
    ∀ X, (Ψ.comp Φ) Xᴴ = ((Ψ.comp Φ) X)ᴴ := by
  intro X
  simp [LinearMap.comp_apply, hΦ, hΨ]

/-- Tensor a rectangular superoperator on the left factor with the identity on the right
ancilla factor. This is the rectangular analogue of `tensorWithIdentity`. -/
def superoperatorWithIdentity
    (din dout k : Type u)
    [Fintype din] [DecidableEq din]
    [Fintype dout] [DecidableEq dout]
    [Fintype k] [DecidableEq k]
    (Φ : Superoperator din dout) :
    Matrix (din × k) (din × k) ℂ →ₗ[ℂ] Matrix (dout × k) (dout × k) ℂ where
  toFun := fun X i j =>
    Φ (fun p q : din => X (p, i.2) (q, j.2)) i.1 j.1
  map_add' := by
    intro X Y
    ext i j
    let X' : Matrix din din ℂ := fun p q => X (p, i.2) (q, j.2)
    let Y' : Matrix din din ℂ := fun p q => Y (p, i.2) (q, j.2)
    change (Φ (X' + Y')) i.1 j.1 = (Φ X' + Φ Y') i.1 j.1
    rw [map_add]
  map_smul' := by
    intro c X
    ext i j
    let X' : Matrix din din ℂ := fun p q => X (p, i.2) (q, j.2)
    change (Φ (c • X')) i.1 j.1 = (c • Φ X') i.1 j.1
    rw [map_smul]

/-- On square channels, the rectangular ancilla extension agrees with `tensorWithIdentity`. -/
theorem superoperatorWithIdentity_eq_tensorWithIdentity
    {d k : Type u}
    [Fintype d] [DecidableEq d]
    [Fintype k] [DecidableEq k]
    (Φ : Channel d) :
    superoperatorWithIdentity d d k Φ = tensorWithIdentity d k Φ := by
  rfl

/-- Ancilla extension respects composition of rectangular superoperators. -/
theorem superoperatorWithIdentity_comp
    {a b c k : Type u}
    [Fintype a] [DecidableEq a]
    [Fintype b] [DecidableEq b]
    [Fintype c] [DecidableEq c]
    [Fintype k] [DecidableEq k]
    (Φ : Superoperator a b) (Ψ : Superoperator b c) :
    (superoperatorWithIdentity b c k Ψ).comp (superoperatorWithIdentity a b k Φ) =
      superoperatorWithIdentity a c k (Ψ.comp Φ) := by
  ext X i j
  rfl

/-- Ancilla extension preserves Hermiticity-preservation. -/
theorem superoperatorWithIdentity_hermiticityPreserving
    {din dout k : Type u}
    [Fintype din] [DecidableEq din]
    [Fintype dout] [DecidableEq dout]
    [Fintype k] [DecidableEq k]
    {Φ : Superoperator din dout}
    (hΦ : ∀ X, Φ Xᴴ = (Φ X)ᴴ) :
    ∀ X, superoperatorWithIdentity din dout k Φ Xᴴ =
      (superoperatorWithIdentity din dout k Φ X)ᴴ := by
  intro X
  ext i j
  rcases i with ⟨a, b⟩
  rcases j with ⟨c, e⟩
  let Y : Matrix din din ℂ := fun p q => X (p, e) (q, b)
  have hY :
      Φ Yᴴ a c = ((Φ Y)ᴴ) a c := by
    exact congrArg (fun M : Matrix dout dout ℂ => M a c) (hΦ Y)
  simpa [Y, superoperatorWithIdentity, Matrix.conjTranspose_apply] using hY

/-- The rectangular superoperator associated to a single Kraus matrix. -/
def singleKrausSuperoperator
    {din dout : Type u}
    [Fintype din] [DecidableEq din]
    [Fintype dout] [DecidableEq dout]
    (E : Matrix dout din ℂ) : Superoperator din dout where
  toFun := fun X => E * X * Eᴴ
  map_add' := by
    intro X Y
    simp [Matrix.mul_add, Matrix.add_mul, Matrix.mul_assoc]
  map_smul' := by
    intro c X
    simp [Matrix.smul_mul, Matrix.mul_smul, Matrix.mul_assoc]

/-- A single rectangular Kraus operator with `Eᴴ * E = 1` defines a rectangular CPTP map. -/
theorem singleKrausSuperoperator_isQuantumSuperoperator
    {din dout : Type u}
    [Fintype din] [DecidableEq din]
    [Fintype dout] [DecidableEq dout]
    {E : Matrix dout din ℂ}
    (hE : Eᴴ * E = 1) :
    IsQuantumSuperoperator (singleKrausSuperoperator E) := by
  refine
    { trace_preserving := ?_
      hermiticity_preserving := ?_
      kraus := ?_ }
  · intro X
    calc
      Matrix.trace (singleKrausSuperoperator E X) = Matrix.trace (E * X * Eᴴ) := by
            rfl
      _ = Matrix.trace ((Eᴴ * E) * X) := by
            simpa [Matrix.mul_assoc] using Matrix.trace_mul_cycle E X Eᴴ
      _ = Matrix.trace X := by
            simp [hE]
  · intro X
    simpa [singleKrausSuperoperator, Matrix.conjTranspose_mul, Matrix.mul_assoc]
  · refine ⟨PUnit, inferInstance, inferInstance, (fun _ => E), ?_, ?_⟩
    · intro X
      simp [singleKrausSuperoperator]
    · simpa using hE

/-- Ancilla extension of a single rectangular Kraus map is conjugation by the corresponding
Kronecker Kraus matrix. -/
private theorem superoperatorWithIdentity_singleKraus_eq_kronecker
    {din dout k : Type u}
    [Fintype din] [DecidableEq din]
    [Fintype dout] [DecidableEq dout]
    [Fintype k] [DecidableEq k]
    (E : Matrix dout din ℂ) (X : Matrix (din × k) (din × k) ℂ) :
    superoperatorWithIdentity din dout k (singleKrausSuperoperator E) X =
      (E ⊗ₖ (1 : Matrix k k ℂ)) * X * (E ⊗ₖ (1 : Matrix k k ℂ))ᴴ := by
  ext i j
  rcases i with ⟨a, b⟩
  rcases j with ⟨c, e⟩
  calc
    superoperatorWithIdentity din dout k (singleKrausSuperoperator E) X (a, b) (c, e)
      = ∑ x : din, ∑ y : din, E a x * X (x, b) (y, e) * star (E c y) := by
          calc
            superoperatorWithIdentity din dout k (singleKrausSuperoperator E) X (a, b) (c, e)
                = ∑ x, E a x * (∑ y, X (x, b) (y, e) * star (E c y)) := by
                    simp [superoperatorWithIdentity, singleKrausSuperoperator, Matrix.mul_apply,
                      Matrix.conjTranspose_apply, Matrix.mul_assoc]
            _ = ∑ x : din, ∑ y : din, E a x * X (x, b) (y, e) * star (E c y) := by
                  simp_rw [Finset.mul_sum, mul_assoc]
    _ = (((E ⊗ₖ (1 : Matrix k k ℂ)) * X) * (E ⊗ₖ (1 : Matrix k k ℂ))ᴴ) (a, b) (c, e) := by
          have hleft :
              ∀ y : din, ((E ⊗ₖ (1 : Matrix k k ℂ)) * X) (a, b) (y, e) =
                ∑ x : din, E a x * X (x, b) (y, e) := by
            intro y
            rw [Matrix.mul_apply, Fintype.sum_prod_type]
            refine Finset.sum_congr rfl ?_
            intro x hx
            rw [Finset.sum_eq_single b]
            · simp
            · intro z hz hzb
              have hbz' : b ≠ z := by
                exact fun h => hzb h.symm
              have hbz : (1 : Matrix k k ℂ) b z = 0 := by
                simp [hbz']
              simp [hbz]
            · simp
          have hright :
              (((E ⊗ₖ (1 : Matrix k k ℂ)) * X) * (E ⊗ₖ (1 : Matrix k k ℂ))ᴴ) (a, b) (c, e) =
                ∑ y : din, ((E ⊗ₖ (1 : Matrix k k ℂ)) * X) (a, b) (y, e) * star (E c y) := by
            rw [Matrix.mul_apply, Fintype.sum_prod_type]
            refine Finset.sum_congr rfl ?_
            intro y hy
            rw [Finset.sum_eq_single e]
            · simp [Matrix.conjTranspose_apply]
            · intro z hz hze
              have hez' : e ≠ z := by
                exact fun h => hze h.symm
              have hez : (1 : Matrix k k ℂ) e z = 0 := by
                simp [hez']
              simp [Matrix.conjTranspose_apply, hez]
            · simp
          rw [hright]
          rw [Finset.sum_comm]
          refine Finset.sum_congr rfl ?_
          intro y hy
          rw [hleft]
          rw [Finset.sum_mul]

/-- Ancilla extension preserves the rectangular CPTP structure. -/
theorem superoperatorWithIdentity_isQuantumSuperoperator
    {din dout k : Type u}
    [Fintype din] [DecidableEq din]
    [Fintype dout] [DecidableEq dout]
    [Fintype k] [DecidableEq k]
    {Φ : Superoperator din dout}
    (hΦ : IsQuantumSuperoperator Φ) :
    IsQuantumSuperoperator (superoperatorWithIdentity din dout k Φ) := by
  rcases hΦ.kraus with ⟨ι, hι, hdecι, E, hE, hsumE⟩
  letI := hι
  letI := hdecι
  let F : ι → Matrix (dout × k) (din × k) ℂ := fun i => E i ⊗ₖ (1 : Matrix k k ℂ)
  refine
    { trace_preserving := ?_
      hermiticity_preserving := ?_
      kraus := ?_ }
  · intro X
    calc
      Matrix.trace (superoperatorWithIdentity din dout k Φ X)
          = ∑ t : k, Matrix.trace (Φ (fun p q : din => X (p, t) (q, t))) := by
              rw [Matrix.trace, Fintype.sum_prod_type, Finset.sum_comm]
              simp [superoperatorWithIdentity, Matrix.trace]
      _ = ∑ t : k, Matrix.trace (fun p q : din => X (p, t) (q, t)) := by
            apply Fintype.sum_congr
            intro t
            exact hΦ.trace_preserving (fun p q : din => X (p, t) (q, t))
      _ = Matrix.trace X := by
            rw [Matrix.trace, Fintype.sum_prod_type, Finset.sum_comm]
            simp [Matrix.trace]
  · intro X
    ext i j
    rcases i with ⟨a, b⟩
    rcases j with ⟨c, e⟩
    let Y : Matrix din din ℂ := fun p q => X (p, e) (q, b)
    have hY :
        Φ Yᴴ a c = ((Φ Y)ᴴ) a c := by
      exact congrArg (fun M : Matrix dout dout ℂ => M a c) (hΦ.hermiticity_preserving Y)
    simpa [Y, superoperatorWithIdentity, Matrix.conjTranspose_apply] using hY
  · refine ⟨ι, inferInstance, inferInstance, F, ?_, ?_⟩
    · intro X
      ext i j
      rcases i with ⟨a, b⟩
      rcases j with ⟨c, e⟩
      let Xbe : Matrix din din ℂ := fun p q => X (p, b) (q, e)
      calc
        superoperatorWithIdentity din dout k Φ X (a, b) (c, e)
            = Φ Xbe a c := by rfl
        _ = (∑ i : ι, E i * Xbe * (E i)ᴴ) a c := by rw [hE Xbe]
        _ = ∑ i : ι,
              superoperatorWithIdentity din dout k
                (singleKrausSuperoperator (E i)) X (a, b) (c, e) := by
              rw [matrix_sum_apply (f := fun i : ι => E i * Xbe * (E i)ᴴ) (a := a) (b := c)]
              simp [singleKrausSuperoperator, superoperatorWithIdentity, Xbe]
        _ = ∑ i : ι, ((F i) * X * (F i)ᴴ) (a, b) (c, e) := by
              apply Fintype.sum_congr
              intro i
              simpa [F] using
                congrArg
                  (fun M : Matrix (dout × k) (dout × k) ℂ => M (a, b) (c, e))
                  (superoperatorWithIdentity_singleKraus_eq_kronecker
                    (din := din) (dout := dout) (k := k) (E := E i) (X := X))
        _ = (∑ i : ι, (F i) * X * (F i)ᴴ) (a, b) (c, e) := by
              rw [matrix_sum_apply
                (f := fun i : ι => (F i) * X * (F i)ᴴ)
                (a := (a, b)) (b := (c, e))]
    · calc
        ∑ i : ι, (F i)ᴴ * F i = ∑ i : ι, ((E i)ᴴ * E i) ⊗ₖ (1 : Matrix k k ℂ) := by
          apply Fintype.sum_congr
          intro i
          calc
            (F i)ᴴ * F i
                = (((E i) ⊗ₖ (1 : Matrix k k ℂ))ᴴ) * ((E i) ⊗ₖ (1 : Matrix k k ℂ)) := by
                    rfl
            _ = (((E i)ᴴ) ⊗ₖ (1 : Matrix k k ℂ)) * ((E i) ⊗ₖ (1 : Matrix k k ℂ)) := by
                  simp [Matrix.conjTranspose_kronecker]
            _ = ((E i)ᴴ * E i) ⊗ₖ ((1 : Matrix k k ℂ) * 1) := by
                  rw [Matrix.mul_kronecker_mul]
            _ = ((E i)ᴴ * E i) ⊗ₖ (1 : Matrix k k ℂ) := by simp
        _ = (∑ i : ι, (E i)ᴴ * E i) ⊗ₖ (1 : Matrix k k ℂ) := by
              ext u v
              rcases u with ⟨a, b⟩
              rcases v with ⟨c, e⟩
              by_cases hbe : b = e
              · rw [matrix_sum_apply
                  (f := fun i : ι => kroneckerMap (fun x1 x2 ↦ x1 * x2) ((E i)ᴴ * E i) 1)
                  (a := (a, b)) (b := (c, e))]
                simp [hbe]
                rw [← matrix_sum_apply (f := fun i : ι => (E i)ᴴ * E i) (a := a) (b := c)]
              · rw [matrix_sum_apply
                  (f := fun i : ι => kroneckerMap (fun x1 x2 ↦ x1 * x2) ((E i)ᴴ * E i) 1)
                  (a := (a, b)) (b := (c, e))]
                simp [hbe]
        _ = (1 : Matrix din din ℂ) ⊗ₖ (1 : Matrix k k ℂ) := by rw [hsumE]
        _ = 1 := by
              simpa using (Matrix.one_kronecker_one (α := ℂ) (m := din) (n := k))

/-- Ancilla extension of the transposed effective coded channel factors through the
transpose-conjugated decoder and the ancilla extension of the transposed middle map. -/
theorem tensorWithIdentity_transpose_effective_eq_conjugated_decoder
    {phys msg : Type u}
    [Fintype phys] [DecidableEq phys]
    [Fintype msg] [DecidableEq msg]
    (encoder : Superoperator msg phys)
    (decoder : Superoperator phys msg)
    (tensorPower : Channel phys) :
    tensorWithIdentity msg msg
        ((transposeMap msg).comp (effectiveChannel encoder decoder tensorPower)) =
      (superoperatorWithIdentity phys msg msg (transposeConjugateSuperoperator decoder)).comp
        (superoperatorWithIdentity msg phys msg
          (((transposeMap phys).comp tensorPower).comp encoder)) := by
  rfl

/-- Pointwise version of the decoder-side ancilla-factorization for density-state witnesses. -/
theorem traceNorm_transpose_effective_eq_conjugated_decoder
    {phys msg : Type u}
    [Fintype phys] [DecidableEq phys]
    [Fintype msg] [DecidableEq msg]
    (encoder : Superoperator msg phys)
    (decoder : Superoperator phys msg)
    (tensorPower : Channel phys)
    (ρ : DensityState (msg × msg)) :
    traceNormOp
        (tensorWithIdentity msg msg
          ((transposeMap msg).comp (effectiveChannel encoder decoder tensorPower)) ρ.1) =
      traceNormOp
        ((superoperatorWithIdentity phys msg msg (transposeConjugateSuperoperator decoder)).comp
          (superoperatorWithIdentity msg phys msg
            (((transposeMap phys).comp tensorPower).comp encoder)) ρ.1) := by
  simpa [LinearMap.comp_apply] using
    congrArg (fun F : Channel (msg × msg) => traceNormOp (F ρ.1))
      (tensorWithIdentity_transpose_effective_eq_conjugated_decoder
        encoder decoder tensorPower)

/-- `Θ ∘ Φ = Φ̄ ∘ Θ` for the transpose-conjugated rectangular superoperator. -/
theorem transpose_comp_eq_transposeConjugate_comp_transpose
    {din dout : Type u}
    [Fintype din] [DecidableEq din]
    [Fintype dout] [DecidableEq dout]
    (Φ : Superoperator din dout) :
    (transposeMap dout).comp Φ =
      (transposeConjugateSuperoperator Φ).comp (transposeMap din) := by
  rfl

/-- Decoder-side transpose reduction for a square channel on the decoder input space. -/
theorem transpose_comp_postprocessing_eq_conjugated_postprocessing
    {phys msg : Type u}
    [Fintype phys] [DecidableEq phys]
    [Fintype msg] [DecidableEq msg]
    (decoder : Superoperator phys msg) (Φ : Channel phys) :
    (transposeMap msg).comp (decoder.comp Φ) =
      (transposeConjugateSuperoperator decoder).comp ((transposeMap phys).comp Φ) := by
  rfl

/-- The transposed effective coded channel factors through the transpose-conjugated decoder
and the transposed physical middle map. This is the standard decoder-side algebraic step in
the Holevo-Werner proof. -/
theorem transpose_comp_effectiveChannel_eq_conjugated_decoder
    {phys msg : Type u}
    [Fintype phys] [DecidableEq phys]
    [Fintype msg] [DecidableEq msg]
    (encoder : Superoperator msg phys)
    (decoder : Superoperator phys msg)
    (tensorPower : Channel phys) :
    (transposeMap msg).comp (effectiveChannel encoder decoder tensorPower) =
      (transposeConjugateSuperoperator decoder).comp
        (((transposeMap phys).comp tensorPower).comp encoder) := by
  rfl
end
end Diamond
