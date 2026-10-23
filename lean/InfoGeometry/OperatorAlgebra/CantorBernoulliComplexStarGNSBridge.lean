/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Physics.ComplexStarCuntzRedesign
import InfoGeometry.Algebra.CuntzComplexificationAlgEquiv
import InfoGeometry.OperatorAlgebra.CantorBernoulliCuntzStarRepresentationBridge
import InfoGeometry.OperatorAlgebra.CantorBernoulliSpatialNativeStateBridge

/-!
# Corrected complex-star Cuntz carrier to native Bernoulli GNS

This owner is deliberately only a composition/readback layer.  It uses the full
`ComplexStarCuntzAlg Bool` carrier, the concrete Bernoulli-boundary star lift,
the existing native spatial functional, and the existing native GNS
expectation.  It makes no KMS, gauge, scalar-carrier, or diagonal-carrier
claim.
-/

noncomputable section

namespace InfoGeometry.OperatorAlgebra.CantorBernoulliComplexStarGNSBridge

open InfoGeometry.Physics.ComplexStarCuntzRedesign
open InfoGeometry.Algebra.CuntzComplexification
open InfoGeometry.Topology.AlgebraicCuntzQuotient
open InfoGeometry.OperatorAlgebra.CantorBernoulliCuntzCStarRealization
open InfoGeometry.OperatorAlgebra.CantorBernoulliKMSStateBridge
open InfoGeometry.OperatorAlgebra.CantorBernoulliCuntzStarRepresentationBridge
open InfoGeometry.OperatorAlgebra.CantorBernoulliSpatialNativeStateBridge
open scoped ComplexOrder InnerProductSpace

abbrev Carrier := ComplexStarCuntzAlg Bool
abbrev B := BoundedL2Operator

/-- The concrete Bernoulli-boundary star representation of the corrected
complex-star Cuntz carrier. -/
abbrev representation : Carrier →⋆ₐ[ℂ] B := cantorBernoulliComplexStarLift

@[simp] theorem representation_S (b : Bool) :
    representation (Sℂ b) = cantorL2CuntzFamily.S b := by
  exact cantorBernoulliComplexStarLift_Sℂ b

@[simp] theorem representation_T (b : Bool) :
    representation (Tℂ b) = star (cantorL2CuntzFamily.S b) := by
  exact cantorBernoulliComplexStarLift_Tℂ b

@[simp] theorem complexification_readback_S (b : Bool) :
    complexificationAlgEquiv (Sℂ b) = S (R := ℂ) b := by
  exact complexificationAlgEquiv_S b

@[simp] theorem complexification_readback_T (b : Bool) :
    complexificationAlgEquiv (Tℂ b) = T (R := ℂ) b := by
  exact complexificationAlgEquiv_T b

/-- Pull the existing positive spatial functional back to the corrected
carrier along the concrete representation. -/
def spatialFunctionalOnCarrier : Carrier →ₗ[ℂ] ℂ :=
  spatialFunctional.comp representation.toAlgHom.toLinearMap

@[simp] theorem spatialFunctionalOnCarrier_apply (x : Carrier) :
    spatialFunctionalOnCarrier x = spatialFunctional (representation x) := rfl

@[simp] theorem spatialPositiveFunctionalOnCarrier_apply (x : Carrier) :
    spatialPositiveFunctional (representation x) = cantorVacuumState (representation x) := by
  exact spatialPositiveFunctional_apply (representation x)

set_option maxHeartbeats 2000000 in
set_option synthInstance.maxHeartbeats 1000000 in
theorem nativeGNS_expectation_on_carrier (x : Carrier) :
    ⟪spatialGNSVacuum,
      spatialGNSRepresentation (representation x) spatialGNSVacuum⟫_ℂ =
        spatialPositiveFunctional (representation x) := by
  exact spatialGNS_expectation_recovery (representation x)

end InfoGeometry.OperatorAlgebra.CantorBernoulliComplexStarGNSBridge
