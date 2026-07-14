import InfoGeometry.SuperMetriplectic.Axioms
import InfoGeometry.Canonical.UnifiedSuperchargeOddOddBridge
import InfoGeometry.Meta.Architecture

open scoped InnerProductSpace

/-!
# SuperMetriplectic Unified Owner Closure Bridge

Bridge from the repo-owned Drazin odd-odd operator lane into the conservative
`SuperMetriplectic.SuperchargeClosure` interface.

This file does not add new analytic or spectral content. It only packages the
already-owned operator decomposition

`{Q_D, Q_D} = translation + central + residualDefect`

into the axiomatic supermetriplectic closure language, and records that the
residual defect vanishes on the current owner slice.
-/

namespace UnifiedOwnerClosureBridge

open InfoGeometry.Krein
open InfoGeometry.Canonical.AssociativeSuperBracket
open InfoGeometry.Canonical.UnifiedSuperchargeAlgebra
open InfoGeometry.Canonical.UnifiedSuperchargeOddOddBridge
open InfoGeometry.Canonical.SuperchargeOddOddDecomposition

section Core

variable {E : Type 0}
variable [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

local notation "H₂" => DoubledSpace E
local notation "EndH" => H₂ →L[ℝ] H₂

noncomputable local instance : NormedRing EndH := inferInstance
noncomputable local instance : NormedAlgebra ℝ EndH := inferInstance
noncomputable local instance : NormedAlgebra ℚ EndH :=
  NormedAlgebra.restrictScalars ℚ ℝ EndH
local instance : IsTopologicalRing EndH := inferInstance
local instance : CompleteSpace EndH := inferInstance
local instance : SMulCommClass ℝ EndH EndH := inferInstance
local instance : IsScalarTower ℝ EndH EndH := inferInstance

/-- Bundle the repo-owned Drazin odd-odd lane as a supermetriplectic closure bridge. -/
@[rep_depth transport]
structure UnifiedDrazinSuperchargeClosureBridge where
  U : UnifiedSuperchargePackage (E := E)

namespace UnifiedDrazinSuperchargeClosureBridge

variable (B : UnifiedDrazinSuperchargeClosureBridge (E := E))

local notation "ownerTranslation" =>
  InfoGeometry.Canonical.UnifiedSuperchargeOddOddBridge.UnifiedSuperchargePackage.ownerTranslationCandidate
local notation "ownerCentral" =>
  InfoGeometry.Canonical.UnifiedSuperchargeOddOddBridge.UnifiedSuperchargePackage.ownerCentralCandidate
local notation "ownerResidual" =>
  InfoGeometry.Canonical.UnifiedSuperchargeOddOddBridge.UnifiedSuperchargePackage.ownerDefectResidual
local notation "ownerResidualZero" =>
  InfoGeometry.Canonical.UnifiedSuperchargeOddOddBridge.UnifiedSuperchargePackage.ownerDefectResidual_eq_zero
local notation "ownerOddOddSplit" =>
  InfoGeometry.Canonical.UnifiedSuperchargeOddOddBridge.UnifiedSuperchargePackage.oddOddBracket_eq_translation_plus_central_plus_defectResidual
local notation "ownerOddOddData" =>
  InfoGeometry.Canonical.UnifiedSuperchargeOddOddBridge.UnifiedSuperchargePackage.toOddOddDecompositionData

/--
The repo-owned Drazin odd-odd closure viewed as a conservative
`SuperMetriplectic.SuperchargeClosure`.

The total defect lane is `central + residualDefect`; on the current owner
slice the residual part is zero.
-/
@[rep_depth transport]
noncomputable def toSuperchargeClosure :
    InfoGeometry.SuperMetriplectic.SuperchargeClosure EndH where
  Q₁ := B.U.QD
  Q₂ := B.U.QD
  P := ownerTranslation B.U
  Z := ownerCentral B.U + ownerResidual B.U
  gamma := 1
  oddOddClosure := by
    calc
      anticommutator B.U.QD B.U.QD
          = InfoGeometry.Canonical.SuperchargeHoppingBridge.oddOddBracket B.U.QD B.U.QD := by
              simp [InfoGeometry.Canonical.AssociativeSuperBracket.anticommutator,
                InfoGeometry.Canonical.AssociativeSuperBracket.superBracket,
                InfoGeometry.Canonical.SuperAnomaly.paritySign,
                InfoGeometry.Canonical.SuperchargeHoppingBridge.oddOddBracket,
                sub_eq_add_neg]
      _ = ownerTranslation B.U
            + ownerCentral B.U
            + ownerResidual B.U := by
            exact ownerOddOddSplit B.U
      _ = (1 : ℝ) • ownerTranslation B.U
            + (ownerCentral B.U + ownerResidual B.U) := by
            simp [one_smul, add_assoc]

@[rep_depth transport]
theorem toSuperchargeClosure_translationShadow_eq_ownerTranslationCandidate :
    B.toSuperchargeClosure.translationShadow = ownerTranslation B.U := by
  rfl

@[rep_depth transport]
theorem toSuperchargeClosure_defectShadow_eq_ownerCentral_plus_residual :
    B.toSuperchargeClosure.defectShadow =
      ownerCentral B.U + ownerResidual B.U := by
  rfl

@[rep_depth transport]
theorem toSuperchargeClosure_defectShadow_eq_ownerCentralCandidate :
    B.toSuperchargeClosure.defectShadow = ownerCentral B.U := by
  rw [toSuperchargeClosure_defectShadow_eq_ownerCentral_plus_residual]
  rw [ownerResidualZero B.U]
  simp

/-- The owner residual defect channel vanishes on this Drazin slice. -/
@[rep_depth transport]
theorem ownerResidualDefect_eq_zero :
    ownerResidual B.U = 0 :=
  ownerResidualZero B.U

/--
The supermetriplectic closure equation reduces to translation plus the owned
central channel because the residual defect vanishes on this owner slice.
-/
@[capstone, rep_depth transport]
theorem oddOddClosure_eq_translation_plus_ownerCentral :
    anticommutator B.U.QD B.U.QD
      = ownerTranslation B.U + ownerCentral B.U := by
  calc
    anticommutator B.U.QD B.U.QD
        = ownerTranslation B.U
            + ownerCentral B.U
            + ownerResidual B.U := by
              calc
                anticommutator B.U.QD B.U.QD
                    = InfoGeometry.Canonical.SuperchargeHoppingBridge.oddOddBracket B.U.QD B.U.QD := by
                        simp [InfoGeometry.Canonical.AssociativeSuperBracket.anticommutator,
                          InfoGeometry.Canonical.AssociativeSuperBracket.superBracket,
                          InfoGeometry.Canonical.SuperAnomaly.paritySign,
                          InfoGeometry.Canonical.SuperchargeHoppingBridge.oddOddBracket,
                          sub_eq_add_neg]
                _ = ownerTranslation B.U
                      + ownerCentral B.U
                      + ownerResidual B.U := by
                        exact ownerOddOddSplit B.U
    _ = ownerTranslation B.U + ownerCentral B.U := by
          rw [ownerResidualZero B.U]
          simp

/--
Re-export of the owner central-core entropy vanishing theorem in the
supermetriplectic bridge namespace.
-/
@[capstone, rep_depth transport]
theorem entropyProduction_vanishes_on_ownerCentralCore
    (ψ : H₂) (hψ : ψ ∈ (ownerOddOddData B.U).centralBPSCore) :
    entropyProductionShadow (ownerCentral B.U) ψ = 0 := by
  exact (ownerOddOddData B.U).entropyProduction_vanishes_on_centralCore ψ hψ

end UnifiedDrazinSuperchargeClosureBridge

end Core

end UnifiedOwnerClosureBridge
