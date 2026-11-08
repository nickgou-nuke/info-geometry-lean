import Mathlib.Analysis.Normed.Operator.Bilinear
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.OperatorAlgebra.ComplexBoundedOperators.Basic

/-!
# AFP CBO `Extra_Operator_Norm` adapters

AFP's `Extra_Operator_Norm` develops the unbundled `onorm` API used later by
`cblinfun`.  Lean/mathlib already packages bounded operators as
`ContinuousLinearMap`, whose norm is the operator norm.  This file exposes the
corresponding theorem surface under CBO names.
-/

noncomputable section

namespace InfoGeometry.OperatorAlgebra.ComplexBoundedOperators
namespace ExtraOperatorNorm

open Basic

variable {E F G : Type*}
variable [NormedAddCommGroup E] [NormedSpace ℂ E]
variable [NormedAddCommGroup F] [NormedSpace ℂ F]
variable [NormedAddCommGroup G] [NormedSpace ℂ G]

/-- AFP `onorm`: application is bounded by the operator norm. -/
theorem norm_apply_le (T : CBO E F) (x : E) :
    ‖T x‖ ≤ ‖T‖ * ‖x‖ :=
  T.le_opNorm x

/-- AFP `onorm_bound`: a pointwise bound gives an operator-norm bound. -/
theorem norm_le_bound (T : CBO E F) {C : ℝ}
    (hC : 0 ≤ C)
    (hbound : ∀ x : E, ‖T x‖ ≤ C * ‖x‖) :
    ‖T‖ ≤ C :=
  ContinuousLinearMap.opNorm_le_bound T hC hbound

/-- Version of the operator-norm bound that only checks nonzero vectors. -/
theorem norm_le_bound_of_nonzero (T : CBO E F) {C : ℝ}
    (hC : 0 ≤ C)
    (hbound : ∀ x : E, ‖x‖ ≠ 0 → ‖T x‖ ≤ C * ‖x‖) :
    ‖T‖ ≤ C :=
  ContinuousLinearMap.opNorm_le_bound' T hC hbound

/-- AFP `norm_cblinfun_eqI`: upper bound plus one lower ratio identifies the norm. -/
theorem norm_eq_of_bound_and_ratio (T : CBO E F) {C : ℝ} {x : E}
    (hlower : C ≤ ‖T x‖ / ‖x‖)
    (hbound : ∀ y : E, ‖T y‖ ≤ C * ‖y‖)
    (hC : 0 ≤ C) :
    ‖T‖ = C := by
  exact le_antisymm
    (ContinuousLinearMap.opNorm_le_bound T hC hbound)
    (hlower.trans (T.ratio_le_opNorm x))

/-- Full mathlib operator-norm equality criterion. -/
theorem norm_eq_of_bounds (T : CBO E F) {C : ℝ}
    (hC : 0 ≤ C)
    (habove : ∀ x : E, ‖T x‖ ≤ C * ‖x‖)
    (hbelow : ∀ N ≥ 0, (∀ x : E, ‖T x‖ ≤ N * ‖x‖) → C ≤ N) :
    ‖T‖ = C :=
  ContinuousLinearMap.opNorm_eq_of_bounds hC habove hbelow

/-- Ratio form of the operator-norm bound. -/
theorem ratio_le_norm (T : CBO E F) (x : E) :
    ‖T x‖ / ‖x‖ ≤ ‖T‖ :=
  T.ratio_le_opNorm x

/-- Unit-ball form of the operator-norm bound. -/
theorem unit_le_norm (T : CBO E F) {x : E} (hx : ‖x‖ ≤ 1) :
    ‖T x‖ ≤ ‖T‖ :=
  T.unit_le_opNorm x hx

/-- Lipschitz form of the operator-norm bound. -/
theorem dist_apply_le (T : CBO E F) (x y : E) :
    dist (T x) (T y) ≤ ‖T‖ * dist x y :=
  T.dist_le_opNorm x y

@[simp]
theorem norm_zero_operator :
    ‖(0 : CBO E F)‖ = 0 :=
  ContinuousLinearMap.opNorm_zero

theorem norm_neg (T : CBO E F) :
    ‖-T‖ = ‖T‖ :=
  ContinuousLinearMap.opNorm_neg T

theorem norm_add_le (S T : CBO E F) :
    ‖S + T‖ ≤ ‖S‖ + ‖T‖ :=
  _root_.norm_add_le S T

theorem norm_smul_le (c : ℂ) (T : CBO E F) :
    ‖c • T‖ ≤ ‖c‖ * ‖T‖ :=
  ContinuousLinearMap.opNorm_smul_le c T

theorem norm_comp_le (S : CBO F G) (T : CBO E F) :
    ‖S.comp T‖ ≤ ‖S‖ * ‖T‖ :=
  S.opNorm_comp_le T

/-- Bilinear `onorm` application bound for curried bounded bilinear maps. -/
theorem norm_apply₂_le (B : E →L[ℂ] F →L[ℂ] G) (x : E) (y : F) :
    ‖B x y‖ ≤ ‖B‖ * ‖x‖ * ‖y‖ :=
  ContinuousLinearMap.le_opNorm₂ B x y

/-- Bilinear `onorm_bound` for curried bounded bilinear maps. -/
theorem norm₂_le_bound (B : E →L[ℂ] F →L[ℂ] G) {C : ℝ}
    (hC : 0 ≤ C)
    (hbound : ∀ x : E, ∀ y : F, ‖B x y‖ ≤ C * ‖x‖ * ‖y‖) :
    ‖B‖ ≤ C :=
  ContinuousLinearMap.opNorm_le_bound₂ B hC hbound

end ExtraOperatorNorm
end InfoGeometry.OperatorAlgebra.ComplexBoundedOperators
