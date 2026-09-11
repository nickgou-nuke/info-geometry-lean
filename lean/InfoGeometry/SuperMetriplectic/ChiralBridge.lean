import InfoGeometry.SuperMetriplectic.Axioms
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Canonical.UnifiedSuperchargeAlgebra
import InfoGeometry.Canonical.AssociativeSuperBracket
import InfoGeometry.Meta.Architecture

open scoped InnerProductSpace

/-!
# SuperMetriplectic Chiral Bridge

Small theorem-backed bridge from the conservative scalar chiral closure packet
into the already owned Drazin/chiral supercharge lane.

This file does not derive new chiral or Drazin facts. It only re-expresses the
existing owner packet from `UnifiedSuperchargeAlgebra` in the axiomatic
`SuperMetriplectic.ChiralSuperchargeClosure` language.
-/

namespace InfoGeometry.SuperMetriplectic.ChiralBridge

open InfoGeometry.Canonical
open InfoGeometry.Canonical.UnifiedSuperchargeAlgebra
open InfoGeometry.Canonical.AssociativeSuperBracket
open InfoGeometry.Krein

section Core

variable {E : Type 0}
variable [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

local notation "H₂" => DoubledSpace E
local notation "EndH" => H₂ →L[ℝ] H₂

/--
Bridge object packaging the repo-owned Drazin chiral odd packet as a
`SuperMetriplectic.ChiralSuperchargeClosure`.
-/
@[rep_depth transport]
abbrev DrazinChiralSuperchargeClosureBridge :=
  UnifiedSuperchargePackage (E := E)

namespace DrazinChiralSuperchargeClosureBridge

abbrev U (B : DrazinChiralSuperchargeClosureBridge (E := E)) :
    UnifiedSuperchargePackage (E := E) := B

end DrazinChiralSuperchargeClosureBridge

namespace DrazinChiralSuperchargeClosureBridge

variable (B : DrazinChiralSuperchargeClosureBridge (E := E))

/--
The Drazin left/right chiral owner packet viewed inside the conservative
`SuperMetriplectic.ChiralSuperchargeClosure` interface.
-/
@[rep_depth transport]
noncomputable def toChiralSuperchargeClosure :
    InfoGeometry.SuperMetriplectic.ChiralSuperchargeClosure EndH where
  QL := B.U.QL
  QR := B.U.QR
  P := B.U.drazinTranslationCandidate
  Z := B.U.drazinCentralCandidate
  gamma := (2 : ℝ)
  netOddOddClosure := by
    calc
      anticommutator (B.U.QR - B.U.QL) (B.U.QR - B.U.QL)
          = anticommutator (B.U.QD) (B.U.QD) := by
              rw [B.U.projected_supercharge_eq_sub_chiral]
      _ = InfoGeometry.Canonical.DrazinSupercharge.anticommutatorK (B.U.QD) (B.U.QD) := by
            simp [InfoGeometry.Canonical.DrazinSupercharge.anticommutatorK,
              InfoGeometry.Canonical.DrazinSupercharge.anticommutator,
              InfoGeometry.Canonical.AssociativeSuperBracket.anticommutator,
              InfoGeometry.Canonical.AssociativeSuperBracket.superBracket,
              InfoGeometry.Canonical.SuperAnomaly.paritySign,
              sub_eq_add_neg]
      _ = (2 : ℝ) • B.U.drazinTranslationCandidate + B.U.drazinCentralCandidate := by
            exact B.U.projected_oddOdd_bracket_eq_two_smul_translation_plus_central

@[rep_depth transport]
theorem toChiralSuperchargeClosure_leftShadow_eq_QL :
    (toChiralSuperchargeClosure B).QL = B.U.QL := by
  rfl

@[rep_depth transport]
theorem toChiralSuperchargeClosure_rightShadow_eq_QR :
    (toChiralSuperchargeClosure B).QR = B.U.QR := by
  rfl

@[rep_depth transport]
theorem toChiralSuperchargeClosure_netOddShadow_eq_QD :
    (toChiralSuperchargeClosure B).netOddShadow = B.U.QD := by
  simpa [InfoGeometry.SuperMetriplectic.ChiralSuperchargeClosure.netOddShadow] using
    (B.U.projected_supercharge_eq_sub_chiral).symm

@[rep_depth transport]
theorem toChiralSuperchargeClosure_translationShadow_eq_drazinTranslationCandidate :
    (toChiralSuperchargeClosure B).translationShadow = B.U.drazinTranslationCandidate := by
  rfl

@[rep_depth transport]
theorem toChiralSuperchargeClosure_defectShadow_eq_drazinCentralCandidate :
    (toChiralSuperchargeClosure B).defectShadow = B.U.drazinCentralCandidate := by
  rfl

@[rep_depth transport]
theorem toChiralSuperchargeClosure_oddOddClosure :
    anticommutator
        (toChiralSuperchargeClosure B).netOddShadow
        (toChiralSuperchargeClosure B).netOddShadow
      =
    (toChiralSuperchargeClosure B).gamma • (toChiralSuperchargeClosure B).translationShadow
      + (toChiralSuperchargeClosure B).defectShadow := by
  exact (toChiralSuperchargeClosure B).anticommutator_netOddShadow_eq_translation_add_defect

end DrazinChiralSuperchargeClosureBridge

end Core

end InfoGeometry.SuperMetriplectic.ChiralBridge
