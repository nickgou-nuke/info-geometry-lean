import Mathlib.Algebra.Module.Basic
import Mathlib.Algebra.Module.LinearMap.Basic
import InfoGeometry.Canonical.ThreeColorIntegralCliffordEmbedding

namespace InfoGeometry.Canonical

/-- Tensor of structural constants of the Split Octonions over ℤ -/
def basisMulCoeff : IntegralSplitBasis → IntegralSplitBasis → IntegralSplitBasis → ℤ
  | .one, .one, .one => 1
  | .one, .l, .l => 1
  | .one, .i, .i => 1
  | .one, .il, .il => 1
  | .one, .j, .j => 1
  | .one, .jl, .jl => 1
  | .one, .k, .k => 1
  | .one, .kl, .kl => 1
  | .l, .one, .l => 1
  | .l, .l, .one => 1
  | .l, .i, .il => -1
  | .l, .il, .i => -1
  | .l, .j, .jl => -1
  | .l, .jl, .j => -1
  | .l, .k, .kl => -1
  | .l, .kl, .k => -1
  | .i, .one, .i => 1
  | .i, .l, .il => 1
  | .i, .i, .one => -1
  | .i, .il, .l => -1
  | .i, .j, .k => 1
  | .i, .jl, .kl => -1
  | .i, .k, .j => -1
  | .i, .kl, .jl => 1
  | .il, .one, .il => 1
  | .il, .l, .i => 1
  | .il, .i, .l => 1
  | .il, .il, .one => 1
  | .il, .j, .kl => -1
  | .il, .jl, .k => 1
  | .il, .k, .jl => 1
  | .il, .kl, .j => -1
  | .j, .one, .j => 1
  | .j, .l, .jl => 1
  | .j, .i, .k => -1
  | .j, .il, .kl => 1
  | .j, .j, .one => -1
  | .j, .jl, .l => -1
  | .j, .k, .i => 1
  | .j, .kl, .il => -1
  | .jl, .one, .jl => 1
  | .jl, .l, .j => 1
  | .jl, .i, .kl => 1
  | .jl, .il, .k => -1
  | .jl, .j, .l => 1
  | .jl, .jl, .one => 1
  | .jl, .k, .il => -1
  | .jl, .kl, .i => 1
  | .k, .one, .k => 1
  | .k, .l, .kl => 1
  | .k, .i, .j => 1
  | .k, .il, .jl => -1
  | .k, .j, .i => -1
  | .k, .jl, .il => 1
  | .k, .k, .one => -1
  | .k, .kl, .l => -1
  | .kl, .one, .kl => 1
  | .kl, .l, .k => 1
  | .kl, .i, .jl => -1
  | .kl, .il, .j => 1
  | .kl, .j, .il => 1
  | .kl, .jl, .i => -1
  | .kl, .k, .l => 1
  | .kl, .kl, .one => 1
  | _, _, _ => 0

open Finset

/-- Bilinear Multiplication of Integral Split Octonions -/
def splitOctonionMul (x y : StandardIntegralSplitOctonion) : StandardIntegralSplitOctonion :=
  fun r => ∑ p : IntegralSplitBasis, ∑ q : IntegralSplitBasis, x p * y q * basisMulCoeff p q r

theorem red_mul_green_eq_blue :
    splitOctonionMul (Pi.single .i 1) (Pi.single .j 1) = Pi.single .k 1 := by
  ext r
  fin_cases r <;> rfl

end InfoGeometry.Canonical
