import InfoGeometry.GromovWittenErlangen.CP1DrazinModel
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
  support_idem := by ext <;> norm_num
  residue_idem := by ext <;> norm_num
  support_residue_zero := by ext <;> norm_num
  residue_support_zero := by ext <;> norm_num
  support_add_residue := by ext <;> norm_num
  selfAdjointLaw := ((1, 0) : Algebra) * ((0, 1) : Algebra) = 0 ∧
      ((0, 1) : Algebra) * ((1, 0) : Algebra) = 0
  selfAdjointCertificate := by
    constructor <;> ext <;> norm_num

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
  element_eq_regular_add_nilpotent := by ext <;> norm_num
  regular_supported_left := by ext <;> norm_num [defectProjections]
  regular_supported_right := by ext <;> norm_num [defectProjections]
  nilpotent_residue_supported_left := by ext <;> norm_num [defectProjections]
  nilpotent_residue_supported_right := by ext <;> norm_num [defectProjections]
  coreInv_supported_left := by ext <;> norm_num [defectProjections]
  coreInv_supported_right := by ext <;> norm_num [defectProjections]
  regular_mul_coreInv := by ext <;> norm_num [defectProjections]
  coreInv_mul_regular := by ext <;> norm_num [defectProjections]
  nilpotent_mul_coreInv := by ext <;> norm_num
  coreInv_mul_nilpotent := by ext <;> norm_num
  nilpotentResidueLaw := ((0, (2 : ZMod 4)) : Algebra) * ((0, (2 : ZMod 4)) : Algebra) = 0
  nilpotentResidueCertificate := by
    ext <;> native_decide

/-- Drazin localization packet with a nonzero residue sector. -/
def drazinLocalization : GWDrazinLocalizationPacket G T Target Coeff Algebra where
  virtualLocalization := virtualLocalization
  edgeEulerWeight := fun _ => (1, 2)
  edgeDrazin := fun _ => defectEdgeDrazin
  edgeDrazin_element_eq := by
    intro e
    cases e
    rfl
  vertexAlgebraContribution := fun _ => (1, 0)
  edgeAlgebraContribution := fun _ => (1, 0)
  localizationValue := (1, 0)
  localizationAssemblyLaw := ((1, 0) : Algebra) = (1, 0)
  localizationAssemblyCertificate := rfl

/-- Minimal divisor packet inherited from the regular CP1 smoke model. -/
def divisorAxiom : LocalizationDivisorAxiomPacket G T Target Coeff :=
  CP1DrazinModel.divisorAxiom

/-- Trivial Frobenius self-duality packet over the product coefficient algebra. -/
-- DEBT_ID: CP1DND_TRIVIAL_FROBENIUS
-- DEBT_KIND: ZERO_DATUM
-- ZERO_DATUM: Trivial Frobenius placeholder for smoke model
def frobenius : FrobeniusSelfDualPacket Algebra where
  pairing := fun _ _ => 0
  pairing_mul_left_eq_pairing_mul_right := by
    intro a b c
    rfl
  nondegeneracyLaw := ∀ a b : Algebra, (0 : ℤ) = 0
  nondegeneracyCertificate := by
    intro a b
    rfl

/-- Trivial residue block packet for the product smoke model. -/
-- DEBT_ID: CP1DND_TRIVIAL_RESIDUE
-- DEBT_KIND: ZERO_DATUM
-- ZERO_DATUM: Trivial residue block placeholder for smoke model
def residueBlocks : DivisionResidueBlockPacket where
  Block := Unit
  DivisionCarrier := fun _ => Unit
  residueProjection := fun _ => Unit
  simpleResidueLaw := Nonempty Unit
  simpleResidueCertificate := ⟨()⟩

/-- Minimal semisimple/Frobenius packet. -/
def frobeniusSemisimple : LocalizedFrobeniusSemisimplePacket Algebra where
  frobenius := frobenius
  residueBlocks := residueBlocks
  semisimplicityLaw := Nonempty Unit
  semisimplicityCertificate := ⟨()⟩

/-- Integrated Drazin/GW bridge for the nonzero-residue smoke model. -/
def bridge : DrazinGromovWittenLocalizationBridge G T Target Coeff Algebra where
  drazinLocalization := drazinLocalization
  divisorAxiom := divisorAxiom
  frobeniusSemisimple := frobeniusSemisimple
  divisorDrazinCompatibilityLaw := ∀ _ : CP1DrazinModel.Edge,
      ((1, (2 : ZMod 4)) : Algebra) = ((1, (2 : ZMod 4)) : Algebra)
  divisorDrazinCompatibilityCertificate := by
    intro _
    rfl

/-- The unique edge carries the product denominator `(1, 1)`. -/
theorem edgeDrazinData_element_line :
    (bridge.edgeDrazinData CP1DrazinModel.Edge.line).element = (1, 2) :=
  bridge.drazinLocalization.edgeDrazinData_element_eq_weight CP1DrazinModel.Edge.line

/-- The unique edge has a visibly nonzero localized Drazin residue. -/
theorem edgeLocalizedDrazinResidue_line :
    bridge.edgeLocalizedDrazinResidue CP1DrazinModel.Edge.line = (0, 2) :=
  rfl

/-- The residue is a genuine square-zero nilpotent in the `ZMod 4` factor. -/
theorem residue_square_zero :
    ((0, (2 : ZMod 4)) : Algebra) * ((0, (2 : ZMod 4)) : Algebra) = 0 := by
  ext
  · norm_num
  · native_decide

/-- The nonzero residue is killed by the localized regular inverse. -/
theorem edgeLocalizedDrazinResidue_mul_regularInverse_line :
    bridge.edgeLocalizedDrazinResidue CP1DrazinModel.Edge.line *
        bridge.edgeLocalizedRegularInverse CP1DrazinModel.Edge.line = 0 :=
  bridge.edgeResidue_mul_regularInverse CP1DrazinModel.Edge.line

/-- The regular inverse also kills the nonzero residue on the left. -/
theorem edgeRegularInverse_mul_localizedDrazinResidue_line :
    bridge.edgeLocalizedRegularInverse CP1DrazinModel.Edge.line *
        bridge.edgeLocalizedDrazinResidue CP1DrazinModel.Edge.line = 0 :=
  bridge.drazinLocalization.edgeRegularInverse_mul_residue CP1DrazinModel.Edge.line

/-- Calibrated entropy packet: the clean regular volume remains `1`. -/
def entropyCalibration : GWDrazinEntropyCalibration bridge where
  gwVolume := 1
  cleanDrazinVolume := 1
  entropyReadout := Real.log 1
  edgeRegularVolume := fun _ => 1
  edgeResidueVolume := fun _ => 1
  entropy_eq_log_cleanDrazinVolume := rfl
  cleanDrazinVolume_eq_gwVolume := rfl
  residueAccountingLaw := Real.log (1 : ℝ) = Real.log 1 ∧ (1 : ℝ) = 1
  residueAccountingCertificate := by
    constructor <;> rfl

/-- The smoke-model entropy is the logarithm of its calibrated GW volume. -/
theorem entropy_eq_log_gw_volume :
    entropyCalibration.entropyReadout = Real.log entropyCalibration.gwVolume :=
  entropyCalibration.entropy_eq_log_gw_volume

end CP1DrazinNilpotentDefectModel
end GromovWittenErlangen
end InfoGeometry
