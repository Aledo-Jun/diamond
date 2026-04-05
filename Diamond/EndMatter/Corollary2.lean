import Diamond.HolevoWerner.Theorem
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

/-- Paper Corollary 2 in packaged form: a quantum coding scheme with the finite-error
Holevo-Werner code data satisfies the improved transposition converse. This theorem
uses the explicit Holevo-Werner theorem/replacement chain from
`Diamond.HolevoWerner.Theorem`. -/
theorem corollary2_linear_bound_of_quantum_coding_scheme
    {phys msg : Type u}
    [Fintype phys] [DecidableEq phys]
    [Fintype msg] [DecidableEq msg] [Nonempty msg]
    {scheme : QuantumCodingScheme phys msg}
    {T : Channel phys} {m : ℕ} {ε : ℝ}
    (hdata : HolevoWernerCodeData scheme T m ε) :
    (1 - Real.sqrt 2 * ε) * (Fintype.card msg : ℝ) ≤
      (diamondOp ((transposeMap phys).comp T)) ^ m := by
  exact holevo_werner_improved_linear_bound hdata

/-- Packaged linear corollary from the decoder-reduced remaining assumption.
This is the cleanest corollary-level entry point currently available in the repo
for the final coding statement. -/
theorem corollary2_linear_bound_of_decoder_reduction
    {phys msg : Type u}
    [Fintype phys] [DecidableEq phys]
    [Fintype msg] [DecidableEq msg] [Nonempty msg]
    {scheme : QuantumCodingScheme phys msg}
    {T : Channel phys} {m : ℕ} {ε : ℝ}
    (hred : ReducedTransposeCodeBoundData scheme T m)
    (herror : ε = (1 / 2 : ℝ) * diamondOp (idMinus scheme.effective)) :
    (1 - Real.sqrt 2 * ε) * (Fintype.card msg : ℝ) ≤
      (diamondOp ((transposeMap phys).comp T)) ^ m := by
  exact corollary2_linear_bound_of_quantum_coding_scheme
    (HolevoWernerCodeData.of_decoder_reduction hred herror)

/-- Packaged linear corollary from the post-encoder pointwise bound for the
ancilla-extended transposed physical middle channel. -/
theorem corollary2_linear_bound_of_post_encoder_reduction
    {phys msg : Type u}
    [Fintype phys] [DecidableEq phys]
    [Fintype msg] [DecidableEq msg] [Nonempty msg]
    {scheme : QuantumCodingScheme phys msg}
    {T : Channel phys} {m : ℕ} {ε : ℝ}
    (hpost : PostEncoderTransposeCodeBoundData scheme T m)
    (herror : ε = (1 / 2 : ℝ) * diamondOp (idMinus scheme.effective)) :
    (1 - Real.sqrt 2 * ε) * (Fintype.card msg : ℝ) ≤
      (diamondOp ((transposeMap phys).comp T)) ^ m := by
  exact corollary2_linear_bound_of_quantum_coding_scheme
    (HolevoWernerCodeData.of_post_encoder_reduction hpost herror)

/-- Packaged linear corollary from the pure-state post-encoder pointwise bound for the
ancilla-extended transposed physical middle channel. -/
theorem corollary2_linear_bound_of_pure_state_bound
    {phys msg : Type u}
    [Fintype phys] [DecidableEq phys]
    [Fintype msg] [DecidableEq msg] [Nonempty msg]
    {scheme : QuantumCodingScheme phys msg}
    {T : Channel phys} {m : ℕ} {ε : ℝ}
    (hpure : PostEncoderPureTransposeCodeBoundData scheme T m)
    (herror : ε = (1 / 2 : ℝ) * diamondOp (idMinus scheme.effective)) :
    (1 - Real.sqrt 2 * ε) * (Fintype.card msg : ℝ) ≤
      (diamondOp ((transposeMap phys).comp T)) ^ m := by
  exact corollary2_linear_bound_of_quantum_coding_scheme
    (HolevoWernerCodeData.of_pure_state_bound hpure herror)

/-- Large-ancilla specialization: when `Fintype.card phys ≤ Fintype.card msg`, the corollary
already follows from the ordinary `diamondOp` bound on the transposed physical middle channel
by compressing pure witnesses down to ancilla `phys`. -/
theorem corollary2_linear_bound_of_diamondOp_bound_card_le
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
  exact corollary2_linear_bound_of_quantum_coding_scheme
    (HolevoWernerCodeData.of_diamondOp_bound_card_le hcard hbound herror)

/-- Small-ancilla specialization: when `Fintype.card msg ≤ Fintype.card phys`, the corollary
already follows from the ordinary `diamondOp` bound on the transposed physical middle channel
by expanding pure witnesses up to ancilla `phys`. -/
theorem corollary2_linear_bound_of_diamondOp_bound_card_ge
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
  exact corollary2_linear_bound_of_quantum_coding_scheme
    (HolevoWernerCodeData.of_diamondOp_bound_card_ge hcard hbound herror)

/-- Unconditional corollary-level reduction from the ordinary `diamondOp` bound on the
transposed physical middle channel. -/
theorem corollary2_linear_bound_of_diamondOp_bound
    {phys msg : Type u}
    [Fintype phys] [DecidableEq phys] [Nonempty phys]
    [Fintype msg] [DecidableEq msg] [Nonempty msg]
    {scheme : QuantumCodingScheme phys msg}
    {T : Channel phys} {m : ℕ} {ε : ℝ}
    (hbound :
      diamondOp ((transposeMap phys).comp scheme.tensorPower) ≤
        (diamondOp ((transposeMap phys).comp T)) ^ m)
    (herror : ε = (1 / 2 : ℝ) * diamondOp (idMinus scheme.effective)) :
    (1 - Real.sqrt 2 * ε) * (Fintype.card msg : ℝ) ≤
      (diamondOp ((transposeMap phys).comp T)) ^ m := by
  exact corollary2_linear_bound_of_quantum_coding_scheme
    (HolevoWernerCodeData.of_diamondOp_bound hbound herror)

/-- Packaged linear corollary from the fixed-ancilla `diamondNormAt` bound on the
transposed physical middle channel. -/
theorem corollary2_linear_bound_of_diamondAt_bound
    {phys msg : Type u}
    [Fintype phys] [DecidableEq phys]
    [Fintype msg] [DecidableEq msg] [Nonempty msg]
    {scheme : QuantumCodingScheme phys msg}
    {T : Channel phys} {m : ℕ} {ε : ℝ}
    (hbound : PostEncoderDiamondAtBoundData scheme T m)
    (herror : ε = (1 / 2 : ℝ) * diamondOp (idMinus scheme.effective)) :
    (1 - Real.sqrt 2 * ε) * (Fintype.card msg : ℝ) ≤
      (diamondOp ((transposeMap phys).comp T)) ^ m := by
  exact corollary2_linear_bound_of_quantum_coding_scheme
    (HolevoWernerCodeData.of_diamondAt_bound hbound herror)

/-- Same-dimension specialization: when the message type is literally the physical input
type, the remaining fixed-ancilla bound is just the ordinary `diamondOp` bound on the
transposed physical middle channel. -/
theorem corollary2_linear_bound_of_diamondOp_bound_same_type
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
  exact corollary2_linear_bound_of_diamondAt_bound
    (PostEncoderDiamondAtBoundData.of_diamondOp_bound_same_type hbound) herror

/-- Equal-cardinality specialization: when the message type has the same cardinality as
the physical input type, the remaining fixed-ancilla bound reduces to the ordinary
`diamondOp` bound on the transposed physical middle channel. -/
theorem corollary2_linear_bound_of_diamondOp_bound_card_eq
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
  exact corollary2_linear_bound_of_diamondAt_bound
    (Diamond.PostEncoderDiamondAtBoundData.of_diamondOp_bound_card_eq hcard hbound) herror

/-- Paper Corollary 2 in packaged form: a quantum coding scheme with the finite-error
Holevo-Werner code data satisfies the improved transposition converse. This theorem
uses the explicit Holevo-Werner theorem/replacement chain from
`Diamond.HolevoWerner.Theorem`. -/
theorem corollary2_of_quantum_coding_scheme
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
  exact holevo_werner_improved_bound hdata hm hε

/-- Packaged logarithmic corollary from the decoder-reduced remaining assumption.
This theorem exposes the exact reduced bound that still needs to be discharged for a
fully unconditional verification of Corollary 2. -/
theorem corollary2_of_decoder_reduction
    {phys msg : Type u}
    [Fintype phys] [DecidableEq phys]
    [Fintype msg] [DecidableEq msg] [Nonempty msg]
    {scheme : QuantumCodingScheme phys msg}
    {T : Channel phys} {m : ℕ} {ε : ℝ}
    (hred : ReducedTransposeCodeBoundData scheme T m)
    (herror : ε = (1 / 2 : ℝ) * diamondOp (idMinus scheme.effective))
    (hm : 0 < m) (hε : ε < 1 / Real.sqrt 2) :
    Real.logb 2 (Fintype.card msg : ℝ) / (m : ℝ) ≤
      Real.logb 2 (diamondOp ((transposeMap phys).comp T)) +
        (1 / (m : ℝ)) * Real.logb 2 (1 / (1 - Real.sqrt 2 * ε)) := by
  exact corollary2_of_quantum_coding_scheme
    (HolevoWernerCodeData.of_decoder_reduction hred herror) hm hε

/-- Packaged logarithmic corollary from the post-encoder pointwise bound for the
ancilla-extended transposed physical middle channel. -/
theorem corollary2_of_post_encoder_reduction
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
  exact corollary2_of_quantum_coding_scheme
    (HolevoWernerCodeData.of_post_encoder_reduction hpost herror) hm hε

/-- Packaged logarithmic corollary from the pure-state post-encoder pointwise bound for the
ancilla-extended transposed physical middle channel. -/
theorem corollary2_of_pure_state_bound
    {phys msg : Type u}
    [Fintype phys] [DecidableEq phys] [Nonempty msg]
    [Fintype msg] [DecidableEq msg]
    {scheme : QuantumCodingScheme phys msg}
    {T : Channel phys} {m : ℕ} {ε : ℝ}
    (hpure : PostEncoderPureTransposeCodeBoundData scheme T m)
    (herror : ε = (1 / 2 : ℝ) * diamondOp (idMinus scheme.effective))
    (hm : 0 < m) (hε : ε < 1 / Real.sqrt 2) :
    Real.logb 2 (Fintype.card msg : ℝ) / (m : ℝ) ≤
      Real.logb 2 (diamondOp ((transposeMap phys).comp T)) +
        (1 / (m : ℝ)) * Real.logb 2 (1 / (1 - Real.sqrt 2 * ε)) := by
  exact corollary2_of_quantum_coding_scheme
    (HolevoWernerCodeData.of_pure_state_bound hpure herror) hm hε

/-- Large-ancilla specialization of Corollary 2 from the ordinary `diamondOp` bound on the
transposed physical middle channel. -/
theorem corollary2_of_diamondOp_bound_card_le
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
  exact corollary2_of_quantum_coding_scheme
    (HolevoWernerCodeData.of_diamondOp_bound_card_le hcard hbound herror) hm hε

/-- Small-ancilla specialization of Corollary 2 from the ordinary `diamondOp` bound on the
transposed physical middle channel. -/
theorem corollary2_of_diamondOp_bound_card_ge
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
  exact corollary2_of_quantum_coding_scheme
    (HolevoWernerCodeData.of_diamondOp_bound_card_ge hcard hbound herror) hm hε

/-- Unconditional corollary-level reduction from the ordinary `diamondOp` bound on the
transposed physical middle channel. -/
theorem corollary2_of_diamondOp_bound
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
  exact corollary2_of_quantum_coding_scheme
    (HolevoWernerCodeData.of_diamondOp_bound hbound herror) hm hε

/-- Packaged logarithmic corollary from the fixed-ancilla `diamondNormAt` bound on the
transposed physical middle channel. -/
theorem corollary2_of_diamondAt_bound
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
  exact corollary2_of_quantum_coding_scheme
    (HolevoWernerCodeData.of_diamondAt_bound hbound herror) hm hε

/-- Same-dimension specialization of Corollary 2 from the ordinary `diamondOp` bound on the
transposed physical middle channel. -/
theorem corollary2_of_diamondOp_bound_same_type
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
  exact corollary2_of_diamondAt_bound
    (PostEncoderDiamondAtBoundData.of_diamondOp_bound_same_type hbound)
    herror hm hε

/-- Equal-cardinality specialization of Corollary 2 from the ordinary `diamondOp` bound
on the transposed physical middle channel. -/
theorem corollary2_of_diamondOp_bound_card_eq
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
  exact corollary2_of_diamondAt_bound
    (Diamond.PostEncoderDiamondAtBoundData.of_diamondOp_bound_card_eq hcard hbound)
    herror hm hε

/-- The linear estimate underlying the improved Holevo-Werner finite-error converse.
This endmatter wrapper now delegates to the explicit Holevo-Werner theorem chain. -/
theorem corollary2_linear_bound
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
  let hdata : HolevoWernerEffectiveData
      (effectiveChannel encoder decoder tensorPower) T m ε :=
    { heffective := heffective
      htranspose_code_bound := htranspose_code_bound
      herror := herror }
  exact holevo_werner_improved_linear_bound_effective hdata

/-- Corollary 2 from the ordinary `diamondOp` bound on the transposed `m`-use physical
middle channel, stated directly in terms of encoder, decoder, and `tensorPower`. This is
the sharp explicit wrapper closest to the paper's coding-scheme formulation currently in the
repo. -/
theorem corollary2_linear_bound_of_tensorPower_diamondOp_bound
    {phys msg : Type u}
    [Fintype phys] [DecidableEq phys] [Nonempty phys]
    [Fintype msg] [DecidableEq msg] [Nonempty msg]
    (T : Channel phys) (m : ℕ)
    (encoder : Superoperator msg phys)
    (decoder : Superoperator phys msg)
    (tensorPower : Channel phys)
    (ε : ℝ)
    (hencoder : IsQuantumSuperoperator encoder)
    (hdecoder : IsQuantumSuperoperator decoder)
    (htensorPower : IsQuantumChannel tensorPower)
    (hbound :
      diamondOp ((transposeMap phys).comp tensorPower) ≤
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
  exact corollary2_linear_bound_of_diamondOp_bound
    (scheme := scheme) (T := T) (m := m) (ε := ε) hbound herror

/-- Paper Corollary 2, stated directly in terms of encoder, decoder,
`m` channel uses, and the diamond-norm decoding error. This wrapper uses the
improved Holevo-Werner theorem proved via the explicit replacement argument. -/
theorem corollary2
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
  let hdata : HolevoWernerEffectiveData
      (effectiveChannel encoder decoder tensorPower) T m ε :=
    { heffective := heffective
      htranspose_code_bound := htranspose_code_bound
      herror := herror }
  exact holevo_werner_improved_bound_effective hdata hm hε

/-- Corollary 2 from the ordinary `diamondOp` bound on the transposed `m`-use physical
middle channel, stated directly in terms of encoder, decoder, and `tensorPower`. -/
theorem corollary2_of_tensorPower_diamondOp_bound
    {phys msg : Type u}
    [Fintype phys] [DecidableEq phys] [Nonempty phys]
    [Fintype msg] [DecidableEq msg] [Nonempty msg]
    (T : Channel phys) (m : ℕ)
    (encoder : Superoperator msg phys)
    (decoder : Superoperator phys msg)
    (tensorPower : Channel phys)
    (ε : ℝ)
    (hencoder : IsQuantumSuperoperator encoder)
    (hdecoder : IsQuantumSuperoperator decoder)
    (htensorPower : IsQuantumChannel tensorPower)
    (hbound :
      diamondOp ((transposeMap phys).comp tensorPower) ≤
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
  exact corollary2_of_diamondOp_bound
    (scheme := scheme) (T := T) (m := m) (ε := ε) hbound herror hm hε

/-- Paper-facing Corollary 2 wrapper for an arbitrary block coding space:
encoder/decoder and the `m`-use physical middle channel may act on a block space distinct from
the single-use channel space. The only remaining analytical input is the ordinary `diamondOp`
bound on that block channel in terms of the single-use channel `T`. -/
theorem corollary2_of_block_tensorPower_diamondOp_bound
    {base block msg : Type u}
    [Fintype base] [DecidableEq base]
    [Fintype block] [DecidableEq block]
    [Fintype msg] [DecidableEq msg] [Nonempty msg]
    (T : Channel base) (m : ℕ)
    (encoder : Superoperator msg block)
    (decoder : Superoperator block msg)
    (tensorPower : Channel block)
    (ε : ℝ)
    (heffective :
      IsQuantumChannel (effectiveChannel encoder decoder tensorPower))
    (htranspose_code_bound :
      diamondOp
          ((transposeMap msg).comp (effectiveChannel encoder decoder tensorPower)) ≤
        (diamondOp ((transposeMap base).comp T)) ^ m)
    (herror :
      ε =
        (1 / 2 : ℝ) *
          diamondOp (idMinus (effectiveChannel encoder decoder tensorPower)))
    (hm : 0 < m) (hε : ε < 1 / Real.sqrt 2) :
    Real.logb 2 (Fintype.card msg : ℝ) / (m : ℝ) ≤
      Real.logb 2 (diamondOp ((transposeMap base).comp T)) +
        (1 / (m : ℝ)) * Real.logb 2 (1 / (1 - Real.sqrt 2 * ε)) := by
  exact holevo_werner_improved_bound_of_block_tensorPower_diamondOp_bound
    T m encoder decoder tensorPower ε heffective htranspose_code_bound herror hm hε

/-- Stronger block-space Corollary 2 wrapper from the ordinary `diamondOp` bound on the
transposed block middle channel itself. -/
theorem corollary2_of_block_middle_diamondOp_bound
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

/-- Corollary 2 specialized to the concrete recursive `m`-use channel
`tensorPowerChannel T m`. This removes the abstract `tensorPower` placeholder from the
top-level statement, although it still uses the current paper-level coded transpose bound as
its remaining analytical input. -/
theorem corollary2_of_recursive_tensorPower_channel
    {phys msg : Type u}
    [Fintype phys] [DecidableEq phys]
    [Fintype msg] [DecidableEq msg] [Nonempty msg]
    (T : Channel phys) (hT : IsQuantumChannel T) (m : ℕ)
    (encoder : Superoperator msg (TensorPowerType phys m))
    (decoder : Superoperator (TensorPowerType phys m) msg)
    (hencoder : IsQuantumSuperoperator encoder)
    (hdecoder : IsQuantumSuperoperator decoder)
    (ε : ℝ)
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
  have heffective :
      IsQuantumChannel (effectiveChannel encoder decoder (tensorPowerChannel T m)) :=
    effectiveChannel_isQuantumChannel hencoder htensorPower hdecoder
  exact corollary2_of_block_tensorPower_diamondOp_bound
    T m encoder decoder (tensorPowerChannel T m) ε
    heffective htranspose_code_bound herror hm hε

/-- Stronger recursive-tensor-power Corollary 2 wrapper from the ordinary `diamondOp` bound
on the concrete `m`-use channel `tensorPowerChannel T m`. -/
theorem corollary2_of_recursive_tensorPower_diamondOp_bound
    {phys msg : Type u}
    [Fintype phys] [DecidableEq phys] [Nonempty phys]
    [Fintype msg] [DecidableEq msg] [Nonempty msg]
    (T : Channel phys) (hT : IsQuantumChannel T) (m : ℕ)
    (encoder : Superoperator msg (TensorPowerType phys m))
    (decoder : Superoperator (TensorPowerType phys m) msg)
    (hencoder : IsQuantumSuperoperator encoder)
    (hdecoder : IsQuantumSuperoperator decoder)
    (ε : ℝ)
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
  exact corollary2_of_block_middle_diamondOp_bound
    T m encoder decoder (tensorPowerChannel T m) ε
    hencoder hdecoder htensorPower hbound herror hm hε

/-- Corollary 2 on the concrete recursive `m`-use channel `tensorPowerChannel T m`, with the
required middle-channel `diamondOp` bound proved internally. -/
theorem corollary2_of_recursive_tensorPower
    {phys msg : Type u}
    [Fintype phys] [DecidableEq phys] [Nonempty phys]
    [Fintype msg] [DecidableEq msg] [Nonempty msg]
    (T : Channel phys) (hT : IsQuantumChannel T) (m : ℕ)
    (encoder : Superoperator msg (TensorPowerType phys m))
    (decoder : Superoperator (TensorPowerType phys m) msg)
    (hencoder : IsQuantumSuperoperator encoder)
    (hdecoder : IsQuantumSuperoperator decoder)
    (ε : ℝ)
    (herror :
      ε =
        (1 / 2 : ℝ) *
          diamondOp (idMinus (effectiveChannel encoder decoder (tensorPowerChannel T m))))
    (hm : 0 < m) (hε : ε < 1 / Real.sqrt 2) :
    Real.logb 2 (Fintype.card msg : ℝ) / (m : ℝ) ≤
      Real.logb 2 (diamondOp ((transposeMap phys).comp T)) +
        (1 / (m : ℝ)) * Real.logb 2 (1 / (1 - Real.sqrt 2 * ε)) := by
  exact corollary2_of_recursive_tensorPower_diamondOp_bound
    T hT m encoder decoder hencoder hdecoder ε
    (diamondOp_transpose_tensorPowerChannel_le_pow T hT m)
    herror hm hε

/-- Linear Corollary 2 on the concrete recursive `m`-use channel `tensorPowerChannel T m`,
with the required middle-channel `diamondOp` bound proved internally. -/
theorem corollary2_linear_bound_of_recursive_tensorPower
    {phys msg : Type u}
    [Fintype phys] [DecidableEq phys] [Nonempty phys]
    [Fintype msg] [DecidableEq msg] [Nonempty msg]
    (T : Channel phys) (hT : IsQuantumChannel T) (m : ℕ)
    (encoder : Superoperator msg (TensorPowerType phys m))
    (decoder : Superoperator (TensorPowerType phys m) msg)
    (hencoder : IsQuantumSuperoperator encoder)
    (hdecoder : IsQuantumSuperoperator decoder)
    (ε : ℝ)
    (herror :
      ε =
        (1 / 2 : ℝ) *
          diamondOp (idMinus (effectiveChannel encoder decoder (tensorPowerChannel T m))))
    :
    (1 - Real.sqrt 2 * ε) * (Fintype.card msg : ℝ) ≤
      (diamondOp ((transposeMap phys).comp T)) ^ m := by
  exact holevo_werner_improved_linear_bound_of_recursive_tensorPower
    T hT m encoder decoder ε hencoder hdecoder herror

/-- Paper-facing alias for the stronger recursive tensor-power wrapper. -/
theorem paper_corollary2_of_recursive_tensorPower_diamondOp_bound
    {phys msg : Type u}
    [Fintype phys] [DecidableEq phys] [Nonempty phys]
    [Fintype msg] [DecidableEq msg] [Nonempty msg]
    (T : Channel phys) (hT : IsQuantumChannel T) (m : ℕ)
    (encoder : Superoperator msg (TensorPowerType phys m))
    (decoder : Superoperator (TensorPowerType phys m) msg)
    (hencoder : IsQuantumSuperoperator encoder)
    (hdecoder : IsQuantumSuperoperator decoder)
    (ε : ℝ)
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
  exact corollary2_of_recursive_tensorPower_diamondOp_bound
    T hT m encoder decoder hencoder hdecoder ε hbound herror hm hε

/-- Paper-facing alias for the recursive tensor-power Corollary 2 statement with the
middle-channel `diamondOp` bound proved internally. -/
theorem paper_corollary2_of_recursive_tensorPower
    {phys msg : Type u}
    [Fintype phys] [DecidableEq phys] [Nonempty phys]
    [Fintype msg] [DecidableEq msg] [Nonempty msg]
    (T : Channel phys) (hT : IsQuantumChannel T) (m : ℕ)
    (encoder : Superoperator msg (TensorPowerType phys m))
    (decoder : Superoperator (TensorPowerType phys m) msg)
    (hencoder : IsQuantumSuperoperator encoder)
    (hdecoder : IsQuantumSuperoperator decoder)
    (ε : ℝ)
    (herror :
      ε =
        (1 / 2 : ℝ) *
          diamondOp (idMinus (effectiveChannel encoder decoder (tensorPowerChannel T m))))
    (hm : 0 < m) (hε : ε < 1 / Real.sqrt 2) :
    Real.logb 2 (Fintype.card msg : ℝ) / (m : ℝ) ≤
      Real.logb 2 (diamondOp ((transposeMap phys).comp T)) +
        (1 / (m : ℝ)) * Real.logb 2 (1 / (1 - Real.sqrt 2 * ε)) := by
  exact corollary2_of_recursive_tensorPower
    T hT m encoder decoder hencoder hdecoder ε herror hm hε

/-- Paper-facing linear alias for the recursive tensor-power Corollary 2 statement with the
middle-channel `diamondOp` bound proved internally. -/
theorem paper_corollary2_linear_bound_of_recursive_tensorPower
    {phys msg : Type u}
    [Fintype phys] [DecidableEq phys] [Nonempty phys]
    [Fintype msg] [DecidableEq msg] [Nonempty msg]
    (T : Channel phys) (hT : IsQuantumChannel T) (m : ℕ)
    (encoder : Superoperator msg (TensorPowerType phys m))
    (decoder : Superoperator (TensorPowerType phys m) msg)
    (hencoder : IsQuantumSuperoperator encoder)
    (hdecoder : IsQuantumSuperoperator decoder)
    (ε : ℝ)
    (herror :
      ε =
        (1 / 2 : ℝ) *
          diamondOp (idMinus (effectiveChannel encoder decoder (tensorPowerChannel T m))))
    :
    (1 - Real.sqrt 2 * ε) * (Fintype.card msg : ℝ) ≤
      (diamondOp ((transposeMap phys).comp T)) ^ m := by
  exact corollary2_linear_bound_of_recursive_tensorPower
    T hT m encoder decoder hencoder hdecoder ε herror

/-- Canonical paper-facing Corollary 2 alias. This is the exact recursive-tensor-power
wrapper corresponding to the statement in `docs/diamond.md`. -/
theorem paper_corollary2
    {phys msg : Type u}
    [Fintype phys] [DecidableEq phys] [Nonempty phys]
    [Fintype msg] [DecidableEq msg] [Nonempty msg]
    (T : Channel phys) (hT : IsQuantumChannel T) (m : ℕ)
    (encoder : Superoperator msg (TensorPowerType phys m))
    (decoder : Superoperator (TensorPowerType phys m) msg)
    (hencoder : IsQuantumSuperoperator encoder)
    (hdecoder : IsQuantumSuperoperator decoder)
    (ε : ℝ)
    (herror :
      ε =
        (1 / 2 : ℝ) *
          diamondOp (idMinus (effectiveChannel encoder decoder (tensorPowerChannel T m))))
    (hm : 0 < m) (hε : ε < 1 / Real.sqrt 2) :
    Real.logb 2 (Fintype.card msg : ℝ) / (m : ℝ) ≤
      Real.logb 2 (diamondOp ((transposeMap phys).comp T)) +
        (1 / (m : ℝ)) * Real.logb 2 (1 / (1 - Real.sqrt 2 * ε)) := by
  exact paper_corollary2_of_recursive_tensorPower
    T hT m encoder decoder hencoder hdecoder ε herror hm hε

/-- Paper-facing alias for Corollary 2 on the concrete recursive `m`-use channel
`tensorPowerChannel T m`. -/
theorem paper_corollary2_of_recursive_tensorPower_channel
    {phys msg : Type u}
    [Fintype phys] [DecidableEq phys]
    [Fintype msg] [DecidableEq msg] [Nonempty msg]
    (T : Channel phys) (hT : IsQuantumChannel T) (m : ℕ)
    (encoder : Superoperator msg (TensorPowerType phys m))
    (decoder : Superoperator (TensorPowerType phys m) msg)
    (hencoder : IsQuantumSuperoperator encoder)
    (hdecoder : IsQuantumSuperoperator decoder)
    (ε : ℝ)
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
  exact corollary2_of_recursive_tensorPower_channel
    T hT m encoder decoder hencoder hdecoder ε htranspose_code_bound herror hm hε

/-- Paper-facing alias for the unconditional ordinary-`diamondOp` corollary wrapper on a
single physical space. -/
theorem paper_corollary2_of_tensorPower_diamondOp_bound
    {phys msg : Type u}
    [Fintype phys] [DecidableEq phys] [Nonempty phys]
    [Fintype msg] [DecidableEq msg] [Nonempty msg]
    (T : Channel phys) (m : ℕ)
    (encoder : Superoperator msg phys)
    (decoder : Superoperator phys msg)
    (tensorPower : Channel phys)
    (ε : ℝ)
    (hencoder : IsQuantumSuperoperator encoder)
    (hdecoder : IsQuantumSuperoperator decoder)
    (htensorPower : IsQuantumChannel tensorPower)
    (hbound :
      diamondOp ((transposeMap phys).comp tensorPower) ≤
        (diamondOp ((transposeMap phys).comp T)) ^ m)
    (herror :
      ε =
        (1 / 2 : ℝ) *
          diamondOp (idMinus (effectiveChannel encoder decoder tensorPower)))
    (hm : 0 < m) (hε : ε < 1 / Real.sqrt 2) :
    Real.logb 2 (Fintype.card msg : ℝ) / (m : ℝ) ≤
      Real.logb 2 (diamondOp ((transposeMap phys).comp T)) +
        (1 / (m : ℝ)) * Real.logb 2 (1 / (1 - Real.sqrt 2 * ε)) := by
  exact corollary2_of_tensorPower_diamondOp_bound
    T m encoder decoder tensorPower ε hencoder hdecoder htensorPower hbound herror hm hε

/-- Paper-facing alias for the sharpest current block-space corollary wrapper. -/
theorem paper_corollary2_of_block_tensorPower_diamondOp_bound
    {base block msg : Type u}
    [Fintype base] [DecidableEq base]
    [Fintype block] [DecidableEq block]
    [Fintype msg] [DecidableEq msg] [Nonempty msg]
    (T : Channel base) (m : ℕ)
    (encoder : Superoperator msg block)
    (decoder : Superoperator block msg)
    (tensorPower : Channel block)
    (ε : ℝ)
    (heffective :
      IsQuantumChannel (effectiveChannel encoder decoder tensorPower))
    (htranspose_code_bound :
      diamondOp
          ((transposeMap msg).comp (effectiveChannel encoder decoder tensorPower)) ≤
        (diamondOp ((transposeMap base).comp T)) ^ m)
    (herror :
      ε =
        (1 / 2 : ℝ) *
          diamondOp (idMinus (effectiveChannel encoder decoder tensorPower)))
    (hm : 0 < m) (hε : ε < 1 / Real.sqrt 2) :
    Real.logb 2 (Fintype.card msg : ℝ) / (m : ℝ) ≤
      Real.logb 2 (diamondOp ((transposeMap base).comp T)) +
        (1 / (m : ℝ)) * Real.logb 2 (1 / (1 - Real.sqrt 2 * ε)) := by
  exact corollary2_of_block_tensorPower_diamondOp_bound
    T m encoder decoder tensorPower ε heffective htranspose_code_bound herror hm hε

/-- Paper-facing alias for the stronger block-space ordinary-`diamondOp` wrapper. -/
theorem paper_corollary2_of_block_middle_diamondOp_bound
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
  exact corollary2_of_block_middle_diamondOp_bound
    T m encoder decoder tensorPower ε hencoder hdecoder htensorPower hbound herror hm hε

end
end Diamond
