import InfoGeometry.Meta.Architecture
import InfoGeometry.Canonical.SouriauThermalEvaluation

/-!
# InfoGeometry.Canonical.DeformationLayer

Quarantine module for Macdonald/q-character, Weyl-Kac, Borcherds, and
non-equilibrium Souriau deformation language.  It records that a deformation
parameter may be compared with thermal evaluation only through explicit property
data; no global identification `q = e^{-β}` is made here.
-/

namespace InfoGeometry.Canonical.DeformationLayer

/-- Bare deformation parameter surface retained for layer-facing callers. -/
@[rep_depth thermo]
def DeformationParameter :=
  {x : ℝ × Set ℝ // x.1 ∈ x.2}

namespace DeformationParameter

abbrev q (W : DeformationParameter) : ℝ := W.1.1

abbrev deformationDomain (W : DeformationParameter) : Set ℝ := W.1.2

def q_in_deformationDomain (W : DeformationParameter) :
    q W ∈ deformationDomain W := W.2

end DeformationParameter

/-- Explicit property connecting a deformation parameter to a chosen thermal map. -/
@[rep_depth thermo]
def DeformationParameterData :=
  {x : ℝ × (ℝ × Set ℝ) //
    x.1 = x.2.1 ∧ x.1 ∈ x.2.2 ∧ x.2.1 ∈ x.2.2}

namespace DeformationParameterData

abbrev q (W : DeformationParameterData) : ℝ := W.1.1

abbrev thermalParameter (W : DeformationParameterData) : ℝ := W.1.2.1

def q_eq_thermalParameter (W : DeformationParameterData) :
    q W = thermalParameter W := W.2.1

abbrev deformationDomain (W : DeformationParameterData) : Set ℝ := W.1.2.2

def q_in_deformationDomain (W : DeformationParameterData) :
    q W ∈ deformationDomain W := W.2.2.1

def thermalParameter_in_deformationDomain (W : DeformationParameterData) :
    thermalParameter W ∈ deformationDomain W := W.2.2.2

end DeformationParameterData

/-- Packet for a deformed character layer, gated by a deformation property. -/
@[rep_depth thermo]
def DeformedCharacterData :=
  {x : ℝ × (ℝ × DeformationParameterData) // x.1 = x.2.1}

namespace DeformedCharacterData

abbrev undeformedCharacter (W : DeformedCharacterData) : ℝ := W.1.1

abbrev deformedCharacter (W : DeformedCharacterData) : ℝ := W.1.2.1

abbrev deformation (W : DeformedCharacterData) : DeformationParameterData :=
  W.1.2.2

def deformationLaw (W : DeformedCharacterData) :
    deformedCharacter W = undeformedCharacter W := W.2.symm

end DeformedCharacterData

@[rep_depth thermo]
abbrev ThermalEvaluationMap : Type := ℝ

namespace ThermalEvaluationMap

def thermalParameter (thermal : ThermalEvaluationMap) : ℝ :=
  thermal

end ThermalEvaluationMap

/-- Identification of `q` with a thermal parameter is available only from property data. -/
@[rep_depth thermo]
theorem q_identification_from_property
    (W : DeformationParameterData) :
    W.q = W.thermalParameter :=
  W.q_eq_thermalParameter

@[rep_depth thermo]
theorem q_identified_with_thermal_parameter_from_property
    (W : DeformationParameterData) :
    W.q = W.thermalParameter :=
  W.q_eq_thermalParameter

end InfoGeometry.Canonical.DeformationLayer
