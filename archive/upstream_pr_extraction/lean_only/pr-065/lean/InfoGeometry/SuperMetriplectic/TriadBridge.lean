import InfoGeometry.SuperMetriplectic.UnifiedOwnerClosureBridge
import InfoGeometry.Meta.Architecture

open scoped InnerProductSpace

/-!
# Native operator Schur/Drazin closure bridge

This owner replaces the former scalar triad packet.  The carrier is the
associative algebra of continuous operators on the doubled Krein space; the
Schur complement and Drazin defect are the operator-valued objects supplied by
`OperatorSchurDrazinBlock`.  No coordinate-plane or scalar diagonal model is
introduced here.
-/

namespace InfoGeometry.SuperMetriplectic.TriadBridge

open InfoGeometry.Krein
open InfoGeometry.SuperMetriplectic.UnifiedOwnerClosureBridge
open InfoGeometry.Canonical.UnifiedSuperchargeOddOddBridge
open InfoGeometry.Canonical.AssociativeSuperBracket

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

local notation "ownerTranslation" =>
  UnifiedSuperchargePackage.ownerTranslationCandidate
local notation "ownerCentral" =>
  UnifiedSuperchargePackage.ownerCentralCandidate

/--
An operator Schur/Drazin closure packet on the native doubled carrier.

The two compatibility equations are typed in `EndH`: the owner translation
and central channels are identified with the operator Schur and Drazin
channels, respectively.  The inverse proofs are fields of the block itself.
-/
@[rep_depth operator]
structure OperatorDrazinSchurClosure where
  owner : UnifiedDrazinSuperchargeClosureBridge (E := E)
  block : OperatorSchurDrazinBlock EndH
  gamma : ℝ
  ownerTranslation_eq_scaledSchur :
    ownerTranslation owner.U = gamma • block.effectiveSchur
  ownerCentral_eq_drazinDefect :
    ownerCentral owner.U = block.drazinDefectProjector

namespace OperatorDrazinSchurClosure

variable (C : OperatorDrazinSchurClosure (E := E))

@[rep_depth operator]
noncomputable def closure : SuperchargeClosure EndH where
  Q₁ := C.owner.U.QD
  Q₂ := C.owner.U.QD
  P := C.block.effectiveSchur
  Z := C.block.drazinDefectProjector
  gamma := C.gamma
  oddOddClosure := by
    calc
      anticommutator C.owner.U.QD C.owner.U.QD =
          ownerTranslation C.owner.U + ownerCentral C.owner.U := by
            exact C.owner.oddOddClosure_eq_translation_plus_ownerCentral
      _ = C.gamma • C.block.effectiveSchur +
          C.block.drazinDefectProjector := by
            rw [C.ownerTranslation_eq_scaledSchur,
              C.ownerCentral_eq_drazinDefect]

@[rep_depth operator]
theorem closure_oddOddClosure :
    anticommutator (C.closure.Q₁) (C.closure.Q₂) =
      C.closure.gamma • C.closure.P + C.closure.Z := by
  exact C.closure.oddOddClosure

@[rep_depth operator]
theorem effectiveSchur_is_operator :
    C.closure.P = C.block.effectiveSchur := by
  rfl

@[rep_depth operator]
theorem drazinDefect_is_operator :
    C.closure.Z = C.block.drazinDefectProjector := by
  rfl

@[rep_depth operator]
theorem drazinDefect_idempotent :
    C.closure.Z * C.closure.Z = C.closure.Z := by
  simpa [closure] using C.block.drazinDefectProjector_idempotent

@[rep_depth operator]
theorem penroseRange_idempotent :
    C.block.LΘΘ * C.block.penroseElement *
        (C.block.LΘΘ * C.block.penroseElement) =
      C.block.LΘΘ * C.block.penroseElement := by
  simpa using C.block.penroseRangeProjector_idempotent

end OperatorDrazinSchurClosure

end Core

end InfoGeometry.SuperMetriplectic.TriadBridge
