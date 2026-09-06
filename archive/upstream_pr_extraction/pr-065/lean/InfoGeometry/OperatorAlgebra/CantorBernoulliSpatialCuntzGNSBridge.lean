import Mathlib.Tactic
import InfoGeometry.OperatorAlgebra.CantorBernoulliSpatialNativeStateBridge
import InfoGeometry.Algebra.CuntzNativeGNSBridge
import InfoGeometry.Physics.CStarCuntzTensorQuotient

/-!
# Concrete Cuntz-source pullback into the spatial native state

The Bernoulli boundary Cuntz family is indexed by `Bool`, while the native
algebraic Cuntz source uses `Fin n`.  This owner supplies the explicit `Fin 2`
transport and applies the existing positive-extension API.  It does not turn
the spatial state into the distinct gauge-invariant word state.
-/

noncomputable section

open scoped ComplexOrder

namespace InfoGeometry.OperatorAlgebra.CantorBernoulliSpatialCuntzGNSBridge

open InfoGeometry.Canonical.CantorBernoulliL2OperatorTransport
open InfoGeometry.OperatorAlgebra.CantorBernoulliCuntzCStarRealization
open InfoGeometry.OperatorAlgebra.CantorBernoulliSpatialNativeStateBridge
open InfoGeometry.Physics.CStarCuntzTensorQuotient
open InfoGeometry.Algebra.CuntzNativeGNSBridge

abbrev B := BoundedL2Operator

set_option maxHeartbeats 2000000 in
set_option synthInstance.maxHeartbeats 1000000 in
def finTwoCuntzFamily : CStarCuntzFamily B (Fin 2) where
  S i := if i = 0 then vLeft else vRight
  ortho := by
    intro i j
    fin_cases i <;> fin_cases j
    · simpa [vLeft] using vLeft_adjoint_comp_vLeft
    · simpa [vLeft, vRight] using vLeft_adjoint_comp_vRight
    · simpa [vLeft, vRight] using vRight_adjoint_comp_vLeft
    · simpa [vRight] using vRight_adjoint_comp_vRight
  partition := by
    rw [Fin.sum_univ_two]
    change vLeft.comp (normalizedPrependBitLpAdjoint false) +
      vRight.comp (normalizedPrependBitLpAdjoint true) =
        ContinuousLinearMap.id ℂ L2Boundary
    exact normalizedPrependBitLp_partition

def spatialCuntzPositiveExtension :
    ExplicitCStarFamily.PositiveExtension (A := B) 2 where
  family := finTwoCuntzFamily
  phi := spatialPositiveFunctional
  omega := ExplicitCStarFamily.pulledBackFunctional
    2 finTwoCuntzFamily spatialPositiveFunctional
  extension := by
    intro x
    rfl

theorem spatialCuntzGNS_expectation_recovery (A : B) :
    inner ℂ spatialGNSVacuum
      (spatialGNSRepresentation A spatialGNSVacuum) =
        spatialPositiveFunctional A := by
  exact InfoGeometry.OperatorAlgebra.PositiveLinearMapGNSVacuum.gns_state_expectation_recovery
    spatialPositiveFunctional A

theorem spatialCuntzPositiveExtension_omega (x :
    ExplicitCStarFamily.AlgebraicCuntzSource 2) :
    spatialCuntzPositiveExtension.omega x =
      spatialPositiveFunctional
        (ExplicitCStarFamily.representation 2 finTwoCuntzFamily x) := by
  exact ExplicitCStarFamily.positiveExtension_omega_eq_pullback
    2 finTwoCuntzFamily spatialPositiveFunctional x

theorem spatialCuntz_expectation_recovery (x :
    ExplicitCStarFamily.AlgebraicCuntzSource 2) :
      inner ℂ spatialGNSVacuum
      (spatialGNSRepresentation
        (ExplicitCStarFamily.representation 2 finTwoCuntzFamily x)
        spatialGNSVacuum) =
      spatialCuntzPositiveExtension.omega x := by
  calc
        inner ℂ spatialGNSVacuum
          (spatialGNSRepresentation
            (ExplicitCStarFamily.representation 2 finTwoCuntzFamily x)
            spatialGNSVacuum) =
        spatialPositiveFunctional
          (ExplicitCStarFamily.representation 2 finTwoCuntzFamily x) :=
      spatialCuntzGNS_expectation_recovery _
    _ = spatialCuntzPositiveExtension.omega x :=
      (spatialCuntzPositiveExtension_omega x).symm

end InfoGeometry.OperatorAlgebra.CantorBernoulliSpatialCuntzGNSBridge
