import InfoGeometry.SuperMetriplectic.TriadBridge
import InfoGeometry.Meta.Architecture

/-!
# Unified owner/operator compatibility

The former version of this file carried arbitrary maps from operators to
scalars.  The maintained interface is now the native operator packet from
`TriadBridge`: all compatibility equations live in `EndH` and are witnessed
by the Schur/Drazin block itself.
-/

namespace InfoGeometry.SuperMetriplectic.UnifiedOwnerTriadBridge

open InfoGeometry.SuperMetriplectic.TriadBridge

section Core

variable {E : Type 0}
variable [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

abbrev UnifiedOwnerTriadCompatibility :=
  OperatorDrazinSchurClosure (E := E)

namespace UnifiedOwnerTriadCompatibility

variable (C : UnifiedOwnerTriadCompatibility (E := E))

@[rep_depth operator]
theorem ownerTranslation_eq_scaledSchur :
    InfoGeometry.Canonical.UnifiedSuperchargeOddOddBridge.UnifiedSuperchargePackage.ownerTranslationCandidate
        C.owner.U = C.gamma • C.block.effectiveSchur :=
  OperatorDrazinSchurClosure.ownerTranslation_eq_scaledSchur C

@[rep_depth operator]
theorem ownerCentral_eq_drazinDefect :
    InfoGeometry.Canonical.UnifiedSuperchargeOddOddBridge.UnifiedSuperchargePackage.ownerCentralCandidate
        C.owner.U = C.block.drazinDefectProjector :=
  OperatorDrazinSchurClosure.ownerCentral_eq_drazinDefect C

@[rep_depth operator]
theorem operator_compatibility_packet :
    (InfoGeometry.Canonical.UnifiedSuperchargeOddOddBridge.UnifiedSuperchargePackage.ownerTranslationCandidate
        C.owner.U = C.gamma • C.block.effectiveSchur)
      ∧
    (InfoGeometry.Canonical.UnifiedSuperchargeOddOddBridge.UnifiedSuperchargePackage.ownerCentralCandidate
        C.owner.U = C.block.drazinDefectProjector)
      ∧
    (C.block.drazinDefectProjector * C.block.drazinDefectProjector =
      C.block.drazinDefectProjector) := by
  exact ⟨OperatorDrazinSchurClosure.ownerTranslation_eq_scaledSchur C,
    OperatorDrazinSchurClosure.ownerCentral_eq_drazinDefect C,
    C.block.drazinDefectProjector_idempotent⟩

end UnifiedOwnerTriadCompatibility

end Core

end InfoGeometry.SuperMetriplectic.UnifiedOwnerTriadBridge
