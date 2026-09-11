import InfoGeometry.GromovWittenErlangen.CP1DrazinModel
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.GromovWittenErlangen.ProjectiveCountProbabilityDrazinBridge

/-!
# Minimal CP1-style Drazin localization model with a nonzero residue sector

This file is a sibling smoke model to `CP1DrazinModel`.

It keeps the same two-fixed-point, one-edge localization graph, but changes the
localized coefficient algebra to a product algebra.  The first factor is the
regular support and the second factor is a square-zero residue sector:

```text
support = (1, 0)
residue = (0, 1)
regular inverse = (1, 0)
localized residue = (0, 2) in the `ZMod 4` factor
```

Thus the residue is visibly nonzero, square-zero, and still killed by the
regular inverse.  No geometric theorem about `CP¹` localization is asserted
here.
-/

noncomputable section

namespace InfoGeometry
namespace GromovWittenErlangen
namespace CP1DrazinNilpotentDefectModel

open InfoGeometry.OperatorAlgebra.DrazinProjectionLocalization

attribute [local instance] starRingOfComm

abbrev G := CP1DrazinModel.G
abbrev T := CP1DrazinModel.T
abbrev Target := CP1DrazinModel.Target
abbrev Coeff := CP1DrazinModel.Coeff
abbrev Algebra := ℤ × ZMod 4

/-- Reuse the minimal two-fixed-point, one-edge virtual localization packet. -/
def virtualLocalization : VirtualLocalizationOrbitPacket G T Target Coeff :=
  CP1DrazinModel.virtualLocalization

/-- Complementary support/residue projections for the product coefficient algebra. -/
def defectProjections : SelfAdjointIdempotentPair Algebra where
  support := (1, 0)
  residue := (0, 1)
  support_idem := by
    ext <;> norm_num
  residue_idem := by
    ext <;> norm_num
  support_residue_zero := by
    ext <;> norm_num
  residue_support_zero := by
    ext <;> norm_num
  support_add_residue := by
    ext <;> norm_num
  support_selfAdjoint := by
    ext <;> norm_num
  residue_selfAdjoint := by
    ext <;> norm_num

/--
One-edge Drazin decomposition with regular denominator in the first factor and
nonzero residue in the second factor.
-/
def defectEdgeDrazin : RelativeCoreNilpotentDecomposition Algebra where
  projections := defectProjections
  element := (1, 2)
  regularPart := (1, 0)
  coreInv := (1, 0)
  nilpotentPart := (0, 2)
  element_eq_regular_add_nilpotent := by
    ext <;> norm_num
  regular_supported_left := by
    ext <;> norm_num [defectProjections]
  regular_supported_right := by
    ext <;> norm_num [defectProjections]
  nilpotent_residue_supported_left := by
    ext <;> norm_num [defectProjections]
  nilpotent_residue_supported_right := by
    ext <;> norm_num [defectProjections]
  coreInv_supported_left := by
    ext <;> norm_num [defectProjections]
  coreInv_supported_right := by
    ext <;> norm_num [defectProjections]
  regular_mul_coreInv := by
    ext <;> norm_num [defectProjections]
  coreInv_mul_regular := by
    ext <;> norm_num [defectProjections]
  nilpotent_mul_coreInv := by
    ext <;> norm_num
  coreInv_mul_nilpotent := by
    ext <;> norm_num
  nilpotent_isNilpotent := by
    refine ⟨2, ?_⟩
    ext
    · norm_num
    · native_decide

/-- The residue is a genuine square-zero nilpotent in the `ZMod 4` factor. -/
theorem residue_square_zero :
    ((0, (2 : ZMod 4)) : Algebra) * ((0, (2 : ZMod 4)) : Algebra) = 0 := by
  ext
  · norm_num
  · native_decide

/-- The nonzero residue is killed by the localized regular inverse. -/
theorem edgeLocalizedDrazinResidue_mul_regularInverse_line :
    defectEdgeDrazin.localizedDrazinResidue *
        defectEdgeDrazin.localizedRegularInverse = 0 :=
  defectEdgeDrazin.residue_mul_regularInverse

/-- The regular inverse also kills the nonzero residue on the left. -/
theorem edgeRegularInverse_mul_localizedDrazinResidue_line :
    defectEdgeDrazin.localizedRegularInverse *
        defectEdgeDrazin.localizedDrazinResidue = 0 :=
  defectEdgeDrazin.regularInverse_mul_residue

end CP1DrazinNilpotentDefectModel
end GromovWittenErlangen
end InfoGeometry
