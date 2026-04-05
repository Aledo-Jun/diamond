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

/-- A quantum coding scheme for the Holevo-Werner converse: encoder, `m`-use channel,
and decoder, each with the quantum structure needed to show the effective map is itself
a quantum channel. -/
structure QuantumCodingScheme
    (phys msg : Type u)
    [Fintype phys] [DecidableEq phys]
    [Fintype msg] [DecidableEq msg] where
  encoder : Superoperator msg phys
  decoder : Superoperator phys msg
  tensorPower : Channel phys
  hencoder : IsQuantumSuperoperator encoder
  hdecoder : IsQuantumSuperoperator decoder
  htensorPower : IsQuantumChannel tensorPower

/-- The effective message-space channel induced by a coding scheme. -/
abbrev QuantumCodingScheme.effective
    {phys msg : Type u}
    [Fintype phys] [DecidableEq phys]
    [Fintype msg] [DecidableEq msg]
    (scheme : QuantumCodingScheme phys msg) : Channel msg :=
  effectiveChannel scheme.encoder scheme.decoder scheme.tensorPower

/-- The effective channel of a quantum coding scheme is a quantum superoperator. -/
theorem QuantumCodingScheme.effective_isQuantumSuperoperator
    {phys msg : Type u}
    [Fintype phys] [DecidableEq phys]
    [Fintype msg] [DecidableEq msg]
    (scheme : QuantumCodingScheme phys msg) :
    IsQuantumSuperoperator scheme.effective := by
  exact effectiveChannel_isQuantumSuperoperator
    scheme.hencoder scheme.htensorPower scheme.hdecoder

/-- The effective channel of a quantum coding scheme is a quantum channel. -/
theorem QuantumCodingScheme.effective_isQuantumChannel
    {phys msg : Type u}
    [Fintype phys] [DecidableEq phys]
    [Fintype msg] [DecidableEq msg]
    (scheme : QuantumCodingScheme phys msg) :
    IsQuantumChannel scheme.effective := by
  exact effectiveChannel_isQuantumChannel
    scheme.hencoder scheme.htensorPower scheme.hdecoder

/-- The common finite-error data needed to run the improved Holevo-Werner converse
for a fixed coding scheme. -/
structure HolevoWernerCodeData
    {phys msg : Type u}
    [Fintype phys] [DecidableEq phys]
    [Fintype msg] [DecidableEq msg]
    (scheme : QuantumCodingScheme phys msg)
    (T : Channel phys) (m : ℕ) (ε : ℝ) : Prop where
  htranspose_code_bound :
    diamondOp ((transposeMap msg).comp scheme.effective) ≤
      (diamondOp ((transposeMap phys).comp T)) ^ m
  herror :
    ε = (1 / 2 : ℝ) * diamondOp (idMinus scheme.effective)

/-- The additional submultiplicativity input used in the original Holevo-Werner proof. -/
structure OriginalHolevoWernerCodeData
    {phys msg : Type u}
    [Fintype phys] [DecidableEq phys]
    [Fintype msg] [DecidableEq msg]
    (scheme : QuantumCodingScheme phys msg)
    (T : Channel phys) (m : ℕ) (ε : ℝ) : Prop extends
    HolevoWernerCodeData scheme T m ε where
  hsubmult :
    diamondOp ((transposeMap msg).comp (idMinus scheme.effective)) ≤
      diamondOp (transposeMap msg) * diamondOp (idMinus scheme.effective)

/-- Decoder-reduced pointwise form of the remaining coding-side transpose bound.
This is the assumption obtained after factoring the transposed effective coded
channel through the transpose-conjugated decoder. -/
structure ReducedTransposeCodeBoundData
    {phys msg : Type u}
    [Fintype phys] [DecidableEq phys]
    [Fintype msg] [DecidableEq msg] [Nonempty msg]
    (scheme : QuantumCodingScheme phys msg)
    (T : Channel phys) (m : ℕ) : Prop where
  hpointwise :
    ∀ ρ : DensityState (msg × msg),
      traceNormOp
          ((superoperatorWithIdentity phys msg msg
              (transposeConjugateSuperoperator scheme.decoder)).comp
            (superoperatorWithIdentity msg phys msg
              (((transposeMap phys).comp scheme.tensorPower).comp scheme.encoder)) ρ.1) ≤
        (diamondOp ((transposeMap phys).comp T)) ^ m

/-- Post-encoder form of the remaining coding-side transpose bound. This is the statement
obtained after removing the decoder and encoder, leaving only the ancilla-extended
transposed physical middle channel. -/
structure PostEncoderTransposeCodeBoundData
    {phys msg : Type u}
    [Fintype phys] [DecidableEq phys]
    [Fintype msg] [DecidableEq msg] [Nonempty msg]
    (scheme : QuantumCodingScheme phys msg)
    (T : Channel phys) (m : ℕ) : Prop where
  hpointwise :
    ∀ σ : DensityState (phys × msg),
      traceNormOp
        (superoperatorWithIdentity phys phys msg
          ((transposeMap phys).comp scheme.tensorPower) σ.1) ≤
        (diamondOp ((transposeMap phys).comp T)) ^ m

/-- Pure-state form of the remaining post-encoder transpose bound. This is equivalent to the
density-state version for the Hermiticity-preserving middle map and is often the cleanest
entry point for ancilla-compression arguments. -/
structure PostEncoderPureTransposeCodeBoundData
    {phys msg : Type u}
    [Fintype phys] [DecidableEq phys]
    [Fintype msg] [DecidableEq msg] [Nonempty msg]
    (scheme : QuantumCodingScheme phys msg)
    (T : Channel phys) (m : ℕ) : Prop where
  hpointwise :
    ∀ ψ : (phys × msg) → ℂ, ψ ⬝ᵥ star ψ = 1 →
      traceNormOp
        (superoperatorWithIdentity phys phys msg
          ((transposeMap phys).comp scheme.tensorPower)
          (Matrix.vecMulVec ψ (star ψ))) ≤
        (diamondOp ((transposeMap phys).comp T)) ^ m

/-- Fixed-ancilla diamond-norm form of the remaining coding-side transpose bound, after
removing decoder and encoder. This packages the ancilla-`msg` stabilization of the
transposed physical middle channel. -/
structure PostEncoderDiamondAtBoundData
    {phys msg : Type u}
    [Fintype phys] [DecidableEq phys]
    [Fintype msg] [DecidableEq msg] [Nonempty msg]
    (scheme : QuantumCodingScheme phys msg)
    (T : Channel phys) (m : ℕ) : Prop where
  hbound :
    diamondNormAt (d := phys) (k := msg) ((transposeMap phys).comp scheme.tensorPower) ≤
      (diamondOp ((transposeMap phys).comp T)) ^ m

end
end Diamond
