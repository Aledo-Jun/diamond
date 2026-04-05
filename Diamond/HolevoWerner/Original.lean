import Diamond.HolevoWerner.Theorem

open scoped BigOperators
open scoped ComplexOrder
open scoped Kronecker
open scoped MatrixOrder
open scoped Matrix.Norms.Frobenius
open Matrix

namespace Diamond

universe u

noncomputable section

/-- Legacy compatibility layer. The source of truth for the finite-error Holevo-Werner
proof is now `Diamond.HolevoWerner.Theorem`; this file only re-exposes a handful of the
older theorem names in terms of the new theorem/data structures. -/
theorem holevo_werner_linear_bound_of_quantum_effective
    {phys msg : Type u}
    [Fintype phys] [DecidableEq phys]
    [Fintype msg] [DecidableEq msg] [Nonempty msg]
    (T : Channel phys) (m : ℕ)
    (encoder : Superoperator msg phys)
    (decoder : Superoperator phys msg)
    (tensorPower : Channel phys)
    (ε : ℝ)
    (heffective :
      IsQuantumChannel (effectiveChannel encoder decoder tensorPower))
    (htranspose_code_bound :
      diamondOp
          ((transposeMap msg).comp (effectiveChannel encoder decoder tensorPower)) ≤
        (diamondOp ((transposeMap phys).comp T)) ^ m)
    (hsubmult :
      diamondOp
          ((transposeMap msg).comp
            (idMinus (effectiveChannel encoder decoder tensorPower))) ≤
        diamondOp (transposeMap msg) *
          diamondOp (idMinus (effectiveChannel encoder decoder tensorPower)))
    (herror :
      ε =
        (1 / 2 : ℝ) *
          diamondOp (idMinus (effectiveChannel encoder decoder tensorPower))) :
    (1 - 2 * ε) * (Fintype.card msg : ℝ) ≤
      (diamondOp ((transposeMap phys).comp T)) ^ m := by
  let hdata : OriginalHolevoWernerEffectiveData
      (effectiveChannel encoder decoder tensorPower) T m ε :=
    { toHolevoWernerEffectiveData :=
        { heffective := heffective
          htranspose_code_bound := htranspose_code_bound
          herror := herror }
      hsubmult := hsubmult }
  exact holevo_werner_original_linear_bound_effective hdata

theorem holevo_werner_bound_of_quantum_effective
    {phys msg : Type u}
    [Fintype phys] [DecidableEq phys]
    [Fintype msg] [DecidableEq msg] [Nonempty msg]
    (T : Channel phys) (m : ℕ)
    (encoder : Superoperator msg phys)
    (decoder : Superoperator phys msg)
    (tensorPower : Channel phys)
    (ε : ℝ)
    (heffective :
      IsQuantumChannel (effectiveChannel encoder decoder tensorPower))
    (htranspose_code_bound :
      diamondOp
          ((transposeMap msg).comp (effectiveChannel encoder decoder tensorPower)) ≤
        (diamondOp ((transposeMap phys).comp T)) ^ m)
    (hsubmult :
      diamondOp
          ((transposeMap msg).comp
            (idMinus (effectiveChannel encoder decoder tensorPower))) ≤
        diamondOp (transposeMap msg) *
          diamondOp (idMinus (effectiveChannel encoder decoder tensorPower)))
    (herror :
      ε =
        (1 / 2 : ℝ) *
          diamondOp (idMinus (effectiveChannel encoder decoder tensorPower)))
    (hm : 0 < m) (hε : ε < 1 / 2) :
    Real.logb 2 (Fintype.card msg : ℝ) / (m : ℝ) ≤
      Real.logb 2 (diamondOp ((transposeMap phys).comp T)) +
        (1 / (m : ℝ)) * Real.logb 2 (1 / (1 - 2 * ε)) := by
  let hdata : OriginalHolevoWernerEffectiveData
      (effectiveChannel encoder decoder tensorPower) T m ε :=
    { toHolevoWernerEffectiveData :=
        { heffective := heffective
          htranspose_code_bound := htranspose_code_bound
          herror := herror }
      hsubmult := hsubmult }
  exact holevo_werner_original_bound_effective hdata hm hε

theorem improved_holevo_werner_linear_bound_of_quantum_effective
    {phys msg : Type u}
    [Fintype phys] [DecidableEq phys]
    [Fintype msg] [DecidableEq msg] [Nonempty msg]
    (T : Channel phys) (m : ℕ)
    (encoder : Superoperator msg phys)
    (decoder : Superoperator phys msg)
    (tensorPower : Channel phys)
    (ε : ℝ)
    (heffective :
      IsQuantumChannel (effectiveChannel encoder decoder tensorPower))
    (htranspose_code_bound :
      diamondOp
          ((transposeMap msg).comp (effectiveChannel encoder decoder tensorPower)) ≤
        (diamondOp ((transposeMap phys).comp T)) ^ m)
    (herror :
      ε =
        (1 / 2 : ℝ) *
          diamondOp (idMinus (effectiveChannel encoder decoder tensorPower))) :
    (1 - Real.sqrt 2 * ε) * (Fintype.card msg : ℝ) ≤
      (diamondOp ((transposeMap phys).comp T)) ^ m := by
  exact holevo_werner_improved_linear_bound_of_quantum_effective
    T m encoder decoder tensorPower ε heffective htranspose_code_bound herror

theorem improved_holevo_werner_bound_of_quantum_effective
    {phys msg : Type u}
    [Fintype phys] [DecidableEq phys]
    [Fintype msg] [DecidableEq msg] [Nonempty msg]
    (T : Channel phys) (m : ℕ)
    (encoder : Superoperator msg phys)
    (decoder : Superoperator phys msg)
    (tensorPower : Channel phys)
    (ε : ℝ)
    (heffective :
      IsQuantumChannel (effectiveChannel encoder decoder tensorPower))
    (htranspose_code_bound :
      diamondOp
          ((transposeMap msg).comp (effectiveChannel encoder decoder tensorPower)) ≤
        (diamondOp ((transposeMap phys).comp T)) ^ m)
    (herror :
      ε =
        (1 / 2 : ℝ) *
          diamondOp (idMinus (effectiveChannel encoder decoder tensorPower)))
    (hm : 0 < m) (hε : ε < 1 / Real.sqrt 2) :
    Real.logb 2 (Fintype.card msg : ℝ) / (m : ℝ) ≤
      Real.logb 2 (diamondOp ((transposeMap phys).comp T)) +
        (1 / (m : ℝ)) * Real.logb 2 (1 / (1 - Real.sqrt 2 * ε)) := by
  exact holevo_werner_improved_bound_of_quantum_effective
    T m encoder decoder tensorPower ε heffective htranspose_code_bound herror hm hε

theorem holevo_werner_linear_bound_of_coding_scheme
    {phys msg : Type u}
    [Fintype phys] [DecidableEq phys]
    [Fintype msg] [DecidableEq msg] [Nonempty msg]
    (T : Channel phys) (m : ℕ)
    (encoder : Superoperator msg phys)
    (decoder : Superoperator phys msg)
    (tensorPower : Channel phys)
    (ε : ℝ)
    (hencoder : IsQuantumSuperoperator encoder)
    (htensorPower : IsQuantumChannel tensorPower)
    (hdecoder : IsQuantumSuperoperator decoder)
    (htranspose_code_bound :
      diamondOp
          ((transposeMap msg).comp (effectiveChannel encoder decoder tensorPower)) ≤
        (diamondOp ((transposeMap phys).comp T)) ^ m)
    (hsubmult :
      diamondOp
          ((transposeMap msg).comp
            (idMinus (effectiveChannel encoder decoder tensorPower))) ≤
        diamondOp (transposeMap msg) *
          diamondOp (idMinus (effectiveChannel encoder decoder tensorPower)))
    (herror :
      ε =
        (1 / 2 : ℝ) *
          diamondOp (idMinus (effectiveChannel encoder decoder tensorPower))) :
    (1 - 2 * ε) * (Fintype.card msg : ℝ) ≤
      (diamondOp ((transposeMap phys).comp T)) ^ m := by
  let scheme : QuantumCodingScheme phys msg :=
    { encoder := encoder
      decoder := decoder
      tensorPower := tensorPower
      hencoder := hencoder
      hdecoder := hdecoder
      htensorPower := htensorPower }
  let hdata : OriginalHolevoWernerCodeData scheme T m ε :=
    { toHolevoWernerCodeData :=
        { htranspose_code_bound := by
            simpa [scheme, QuantumCodingScheme.effective, effectiveChannel] using
              htranspose_code_bound
          herror := by
            simpa [scheme, QuantumCodingScheme.effective, effectiveChannel] using herror }
      hsubmult := by
        simpa [scheme, QuantumCodingScheme.effective, effectiveChannel] using hsubmult }
  exact holevo_werner_original_linear_bound hdata

theorem holevo_werner_bound_of_coding_scheme
    {phys msg : Type u}
    [Fintype phys] [DecidableEq phys]
    [Fintype msg] [DecidableEq msg] [Nonempty msg]
    (T : Channel phys) (m : ℕ)
    (encoder : Superoperator msg phys)
    (decoder : Superoperator phys msg)
    (tensorPower : Channel phys)
    (ε : ℝ)
    (hencoder : IsQuantumSuperoperator encoder)
    (htensorPower : IsQuantumChannel tensorPower)
    (hdecoder : IsQuantumSuperoperator decoder)
    (htranspose_code_bound :
      diamondOp
          ((transposeMap msg).comp (effectiveChannel encoder decoder tensorPower)) ≤
        (diamondOp ((transposeMap phys).comp T)) ^ m)
    (hsubmult :
      diamondOp
          ((transposeMap msg).comp
            (idMinus (effectiveChannel encoder decoder tensorPower))) ≤
        diamondOp (transposeMap msg) *
          diamondOp (idMinus (effectiveChannel encoder decoder tensorPower)))
    (herror :
      ε =
        (1 / 2 : ℝ) *
          diamondOp (idMinus (effectiveChannel encoder decoder tensorPower)))
    (hm : 0 < m) (hε : ε < 1 / 2) :
    Real.logb 2 (Fintype.card msg : ℝ) / (m : ℝ) ≤
      Real.logb 2 (diamondOp ((transposeMap phys).comp T)) +
        (1 / (m : ℝ)) * Real.logb 2 (1 / (1 - 2 * ε)) := by
  let scheme : QuantumCodingScheme phys msg :=
    { encoder := encoder
      decoder := decoder
      tensorPower := tensorPower
      hencoder := hencoder
      hdecoder := hdecoder
      htensorPower := htensorPower }
  let hdata : OriginalHolevoWernerCodeData scheme T m ε :=
    { toHolevoWernerCodeData :=
        { htranspose_code_bound := by
            simpa [scheme, QuantumCodingScheme.effective, effectiveChannel] using
              htranspose_code_bound
          herror := by
            simpa [scheme, QuantumCodingScheme.effective, effectiveChannel] using herror }
      hsubmult := by
        simpa [scheme, QuantumCodingScheme.effective, effectiveChannel] using hsubmult }
  exact holevo_werner_original_bound hdata hm hε

theorem improved_holevo_werner_linear_bound_of_coding_scheme
    {phys msg : Type u}
    [Fintype phys] [DecidableEq phys]
    [Fintype msg] [DecidableEq msg] [Nonempty msg]
    (T : Channel phys) (m : ℕ)
    (encoder : Superoperator msg phys)
    (decoder : Superoperator phys msg)
    (tensorPower : Channel phys)
    (ε : ℝ)
    (hencoder : IsQuantumSuperoperator encoder)
    (htensorPower : IsQuantumChannel tensorPower)
    (hdecoder : IsQuantumSuperoperator decoder)
    (htranspose_code_bound :
      diamondOp
          ((transposeMap msg).comp (effectiveChannel encoder decoder tensorPower)) ≤
        (diamondOp ((transposeMap phys).comp T)) ^ m)
    (herror :
      ε =
        (1 / 2 : ℝ) *
          diamondOp (idMinus (effectiveChannel encoder decoder tensorPower))) :
    (1 - Real.sqrt 2 * ε) * (Fintype.card msg : ℝ) ≤
      (diamondOp ((transposeMap phys).comp T)) ^ m := by
  let scheme : QuantumCodingScheme phys msg :=
    { encoder := encoder
      decoder := decoder
      tensorPower := tensorPower
      hencoder := hencoder
      hdecoder := hdecoder
      htensorPower := htensorPower }
  let hdata : HolevoWernerCodeData scheme T m ε :=
    { htranspose_code_bound := by
        simpa [scheme, QuantumCodingScheme.effective, effectiveChannel] using
          htranspose_code_bound
      herror := by
        simpa [scheme, QuantumCodingScheme.effective, effectiveChannel] using herror }
  exact holevo_werner_improved_linear_bound hdata

theorem improved_holevo_werner_bound_of_coding_scheme
    {phys msg : Type u}
    [Fintype phys] [DecidableEq phys]
    [Fintype msg] [DecidableEq msg] [Nonempty msg]
    (T : Channel phys) (m : ℕ)
    (encoder : Superoperator msg phys)
    (decoder : Superoperator phys msg)
    (tensorPower : Channel phys)
    (ε : ℝ)
    (hencoder : IsQuantumSuperoperator encoder)
    (htensorPower : IsQuantumChannel tensorPower)
    (hdecoder : IsQuantumSuperoperator decoder)
    (htranspose_code_bound :
      diamondOp
          ((transposeMap msg).comp (effectiveChannel encoder decoder tensorPower)) ≤
        (diamondOp ((transposeMap phys).comp T)) ^ m)
    (herror :
      ε =
        (1 / 2 : ℝ) *
          diamondOp (idMinus (effectiveChannel encoder decoder tensorPower)))
    (hm : 0 < m) (hε : ε < 1 / Real.sqrt 2) :
    Real.logb 2 (Fintype.card msg : ℝ) / (m : ℝ) ≤
      Real.logb 2 (diamondOp ((transposeMap phys).comp T)) +
        (1 / (m : ℝ)) * Real.logb 2 (1 / (1 - Real.sqrt 2 * ε)) := by
  let scheme : QuantumCodingScheme phys msg :=
    { encoder := encoder
      decoder := decoder
      tensorPower := tensorPower
      hencoder := hencoder
      hdecoder := hdecoder
      htensorPower := htensorPower }
  let hdata : HolevoWernerCodeData scheme T m ε :=
    { htranspose_code_bound := by
        simpa [scheme, QuantumCodingScheme.effective, effectiveChannel] using
          htranspose_code_bound
      herror := by
        simpa [scheme, QuantumCodingScheme.effective, effectiveChannel] using herror }
  exact holevo_werner_improved_bound hdata hm hε

end
end Diamond
