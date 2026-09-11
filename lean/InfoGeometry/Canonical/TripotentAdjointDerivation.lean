import InfoGeometry.Physics.TripotentAdjointDerivation
import InfoGeometry.Algebra.FiniteSpinAlgebra

/-!
# Canonical wrapper for tripotent adjoint derivation calculus

This file re-exports the already-verified derivation API under the canonical
owner tree.
-/

namespace InfoGeometry.Canonical.TripotentAdjointDerivation

export InfoGeometry.Physics.Algebra (
  IsTripotent
  adOp
  adOp_mul
  leftMulLinear
  rightMulLinear
  adLinear
  adLinear_apply
  adGrade
  mem_adGrade_iff
  mul_mem_adGrade_add
  commutator_mem_adGrade_add
)

end InfoGeometry.Canonical.TripotentAdjointDerivation
