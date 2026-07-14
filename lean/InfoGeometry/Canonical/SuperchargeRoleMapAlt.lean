import InfoGeometry.Canonical.SuperchargeCARCCRBridge
import InfoGeometry.Canonical.SuperchargeGapBridge
import InfoGeometry.Canonical.ModularHessian
import InfoGeometry.Meta.Architecture

open scoped InnerProductSpace

/-!
# InfoGeometry.Canonical.SuperchargeRoleMapAlt

Raw alternative role-map surface preserved under the dual-implementation policy.

This file is not the canonical owner for the supercharge lane. The stable
compiled bridge remains `SuperchargeRoleBridge`. This alternative keeps a more
direct role-naming presentation alive without displacing the canonical theorem
surface.
-/

namespace SuperchargeRoleMapAlt

open InfoGeometry.Krein
open InfoGeometry.Canonical.RelationalInformationCore
open InfoGeometry.Canonical.SuperchargeCARCCRBridge
open InfoGeometry.Canonical.SuperchargeGapBridge
open InfoGeometry.Canonical.ModularHessian
open InfoGeometry.Canonical.BogoliubovTransport

section Core

variable {E : Type 0}
variable [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

local notation "H₂" => DoubledSpace E
local notation "EndH" => H₂ →L[ℝ] H₂

/-- Alternative role name for the primitive odd mirror lane. -/
@[rep_depth transport]
noncomputable def primitiveOddSuperchargeJAlt : EndH :=
  paritySuperchargeOp (E := E)

/-- Alternative role name for the primitive odd orientation lane. -/
@[rep_depth transport]
noncomputable def primitiveOddSuperchargeEpsilonAlt : EndH :=
  modularSuperchargeOp (E := E)

/-- Alternative role name for the derived coupling/CPT lane. -/
@[rep_depth transport]
noncomputable def derivedCouplingSuperchargeKAlt : EndH :=
  cptSuperchargeOp (E := E)

/-- Alternative role name for the concrete split-`Cl(1,1)` creation ladder. -/
@[rep_depth transport]
noncomputable def carLadderPlusAlt : EndH :=
  concreteCARCreation (E := E)

/-- Alternative role name for the concrete split-`Cl(1,1)` annihilation ladder. -/
@[rep_depth transport]
noncomputable def carLadderMinusAlt : EndH :=
  concreteCARAnnihilation (E := E)

/-- Alternative role name for the first odd-odd transported deformation. -/
@[rep_depth transport]
noncomputable def gapSeedDeformationAlt
    (V : BogoliubovVielbein.BogoliubovVielbeinBundle (E := E)) : EndH :=
  transportedParityModularGapSeed (E := E) V

/-- Alternative role name for the operatorial curvature/Hessian readout. -/
@[rep_depth thermo]
noncomputable def curvatureChannelAlt
    (R : RelationalInformationDatum (E := E)) :
    LinearMap.BilinForm ℝ (PerturbationChannel E) :=
  modularHessian R

/-- The alternative mirror-lane name is definitionally the canonical parity supercharge. -/
@[rep_depth transport, simp] theorem primitiveOddSuperchargeJAlt_eq_paritySuperchargeOp :
    primitiveOddSuperchargeJAlt (E := E) = paritySuperchargeOp (E := E) := rfl

/-- Alternative mirror-lane name compared directly to the root owner packet. -/
@[rep_depth transport, simp] theorem primitiveOddSuperchargeJAlt_eq_modular_j :
    primitiveOddSuperchargeJAlt (E := E) = modular_j (E := E) := by
  rw [primitiveOddSuperchargeJAlt_eq_paritySuperchargeOp (E := E)]

/-- The alternative orientation-lane name is definitionally the canonical modular supercharge. -/
@[rep_depth transport, simp] theorem primitiveOddSuperchargeEpsilonAlt_eq_modularSuperchargeOp :
    primitiveOddSuperchargeEpsilonAlt (E := E) = modularSuperchargeOp (E := E) := rfl

/-- Alternative orientation-lane name compared directly to the root owner packet. -/
@[rep_depth transport, simp] theorem primitiveOddSuperchargeEpsilonAlt_eq_spectral_epsilon :
    primitiveOddSuperchargeEpsilonAlt (E := E) = spectral_epsilon (E := E) := by
  rw [primitiveOddSuperchargeEpsilonAlt_eq_modularSuperchargeOp (E := E)]

/-- The alternative coupling-lane name is definitionally the canonical CPT supercharge. -/
@[rep_depth transport, simp] theorem derivedCouplingSuperchargeKAlt_eq_cptSuperchargeOp :
    derivedCouplingSuperchargeKAlt (E := E) = cptSuperchargeOp (E := E) := rfl

/-- Alternative coupling-lane name compared directly to the root phase axis. -/
@[rep_depth transport, simp] theorem derivedCouplingSuperchargeKAlt_eq_complex_i :
    derivedCouplingSuperchargeKAlt (E := E) = complex_i (E := E) := by
  rw [derivedCouplingSuperchargeKAlt_eq_cptSuperchargeOp (E := E)]
  exact cptSuperchargeOp_eq_complex_i (E := E)

/-- The alternative creation-ladder name is definitionally the canonical concrete CAR creator. -/
@[rep_depth transport, simp] theorem carLadderPlusAlt_eq_concreteCARCreation :
    carLadderPlusAlt (E := E) = concreteCARCreation (E := E) := rfl

/-- The alternative annihilation-ladder name is definitionally the canonical concrete CAR annihilator. -/
@[rep_depth transport, simp] theorem carLadderMinusAlt_eq_concreteCARAnnihilation :
    carLadderMinusAlt (E := E) = concreteCARAnnihilation (E := E) := rfl

/-- The alternative deformation name is definitionally the canonical transported gap seed. -/
@[rep_depth transport, simp] theorem gapSeedDeformationAlt_eq_transportedParityModularGapSeed
    (V : BogoliubovVielbein.BogoliubovVielbeinBundle (E := E)) :
    gapSeedDeformationAlt (E := E) V = transportedParityModularGapSeed (E := E) V := rfl

/-- The alternative curvature-channel name is definitionally the canonical modular Hessian. -/
@[rep_depth transport, simp] theorem curvatureChannelAlt_eq_modularHessian
    (R : RelationalInformationDatum (E := E)) :
    curvatureChannelAlt (E := E) R = modularHessian R := rfl

end Core

end SuperchargeRoleMapAlt
