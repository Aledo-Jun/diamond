import Diamond.Theorem.Remark1

open scoped BigOperators
open scoped ComplexOrder
open scoped Kronecker
open scoped MatrixOrder
open scoped Matrix.Norms.Frobenius
open Matrix

namespace Diamond

universe u

noncomputable section

/-- A finite-dimensional superoperator between possibly different input/output spaces. -/
abbrev Superoperator
    (din dout : Type u) [Fintype din] [DecidableEq din] [Fintype dout] [DecidableEq dout] :=
  Matrix din din ℂ →ₗ[ℂ] Matrix dout dout ℂ

/-- The effective message-space channel induced by encoder, `m` channel uses,
and decoder. -/
abbrev effectiveChannel
    {phys msg : Type u}
    [Fintype phys] [DecidableEq phys] [Fintype msg] [DecidableEq msg]
    (encoder : Superoperator msg phys)
    (decoder : Superoperator phys msg)
    (tensorPower : Channel phys) : Channel msg :=
  decoder.comp (tensorPower.comp encoder)

end
end Diamond
