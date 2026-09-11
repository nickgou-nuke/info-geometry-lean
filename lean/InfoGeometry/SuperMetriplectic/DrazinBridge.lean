import InfoGeometry.SuperMetriplectic.Axioms
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Canonical.UnifiedSuperchargeAlgebra
import InfoGeometry.Canonical.AssociativeSuperBracket
import InfoGeometry.Meta.Architecture

open scoped InnerProductSpace

/-!
# SuperMetriplectic Drazin Bridge

Small theorem-backed bridge from the conservative supermetriplectic closure packet
into the already owned Drazin/chiral supercharge lane.

This file does not derive new Drazin facts. It only re-expresses the existing
owner packet from `UnifiedSuperchargeAlgebra` in the axiomatic
`SuperMetriplectic.SuperchargeClosure` language.
-/

namespace InfoGeometry.SuperMetriplectic.DrazinBridge

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
Bridge object packaging the repo-owned Drazin odd-odd closure packet as a
`SuperMetriplectic.SuperchargeClosure`.
-/
@[rep_depth transport]
abbrev DrazinSuperchargeClosureBridge :=
  UnifiedSuperchargePackage (E := E)

namespace DrazinSuperchargeClosureBridge

abbrev U (B : DrazinSuperchargeClosureBridge (E := E)) :
    UnifiedSuperchargePackage (E := E) := B

end DrazinSuperchargeClosureBridge

namespace DrazinSuperchargeClosureBridge

variable (B : DrazinSuperchargeClosureBridge (E := E))

/--
The Drazin odd-odd owner packet viewed inside the conservative
`SuperMetriplectic.SuperchargeClosure` interface.
-/
@[rep_depth transport]
noncomputable def toSuperchargeClosure :
    InfoGeometry.SuperMetriplectic.SuperchargeClosure EndH where
  Q₁ := B.U.QD
  Q₂ := B.U.QD
  P := B.U.drazinTranslationCandidate
  Z := B.U.drazinCentralCandidate
  gamma := (2 : ℝ)
  oddOddClosure := by
    simpa [InfoGeometry.SuperMetriplectic.SuperchargeClosure.translationShadow,
      InfoGeometry.SuperMetriplectic.SuperchargeClosure.defectShadow,
      InfoGeometry.SuperMetriplectic.SuperchargeClosure] using
      (B.U.projected_oddOdd_bracket_eq_two_smul_translation_plus_central)

@[rep_depth transport]
theorem toSuperchargeClosure_translationShadow_eq_drazinTranslationCandidate :
    (toSuperchargeClosure B).translationShadow = B.U.drazinTranslationCandidate := by
  rfl

@[rep_depth transport]
theorem toSuperchargeClosure_defectShadow_eq_drazinCentralCandidate :
    (toSuperchargeClosure B).defectShadow = B.U.drazinCentralCandidate := by
  rfl

@[rep_depth transport]
theorem toSuperchargeClosure_oddOddClosure :
    anticommutator (toSuperchargeClosure B).Q₁ (toSuperchargeClosure B).Q₂
      = (toSuperchargeClosure B).gamma • (toSuperchargeClosure B).translationShadow
          + (toSuperchargeClosure B).defectShadow := by
  exact (toSuperchargeClosure B).oddOddClosure

end DrazinSuperchargeClosureBridge

end Core

end InfoGeometry.SuperMetriplectic.DrazinBridge
