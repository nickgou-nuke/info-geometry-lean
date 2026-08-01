import InfoGeometry.Meta.Architecture
import InfoGeometry.Canonical.SouriauThermalEvaluation

/-!
# InfoGeometry.Canonical.DeformationLayer

Quarantine module for Macdonald/q-character, Weyl-Kac, Borcherds, and
non-equilibrium Souriau deformation language.  It records that a deformation
parameter may be compared with thermal evaluation only through explicit witness
data; no global identification `q = e^{-β}` is made here.
-/

namespace InfoGeometry.Canonical.DeformationLayer

/-- Bare deformation parameter surface retained for layer-facing callers. -/
@[rep_depth thermo]
def DeformationParameter :=
  {x : ℝ × Set ℝ // x.1 ∈ x.2}

namespace DeformationParameter

def q (W : DeformationParameter) : ℝ := W.1.1

def deformationDomain (W : DeformationParameter) : Set ℝ := W.1.2

def q_in_deformationDomain (W : DeformationParameter) :
    q W ∈ deformationDomain W := W.2

end DeformationParameter

/-- Explicit witness connecting a deformation parameter to a chosen thermal map. -/
@[rep_depth thermo]
def DeformationParameterWitness :=
  {x : ℝ × (ℝ × Set ℝ) //
    x.1 = x.2.1 ∧ x.1 ∈ x.2.2 ∧ x.2.1 ∈ x.2.2}

namespace DeformationParameterWitness

def q (W : DeformationParameterWitness) : ℝ := W.1.1

def thermalParameter (W : DeformationParameterWitness) : ℝ := W.1.2.1

def q_eq_thermalParameter (W : DeformationParameterWitness) :
    q W = thermalParameter W := W.2.1

def deformationDomain (W : DeformationParameterWitness) : Set ℝ := W.1.2.2

def q_in_deformationDomain (W : DeformationParameterWitness) :
    q W ∈ deformationDomain W := W.2.2.1

def thermalParameter_in_deformationDomain (W : DeformationParameterWitness) :
    thermalParameter W ∈ deformationDomain W := W.2.2.2

end DeformationParameterWitness

/-- Packet for a deformed character layer, gated by a deformation witness. -/
@[rep_depth thermo]
structure DeformedCharacterWitness where
  undeformedCharacter : ℝ
  deformedCharacter : ℝ
  deformation : DeformationParameterWitness
  deformationLaw : deformedCharacter = undeformedCharacter

@[rep_depth thermo]
abbrev ThermalEvaluationMap : Type := ℝ

namespace ThermalEvaluationMap

def thermalParameter (thermal : ThermalEvaluationMap) : ℝ :=
  thermal

end ThermalEvaluationMap

@[rep_depth thermo]
structure SeparatedDeformationWitness where
  deformation : DeformationParameter
  thermal : ThermalEvaluationMap
  separated : deformation.q = thermal.thermalParameter

/-- Identification of `q` with a thermal parameter is available only from witness data. -/
@[rep_depth thermo]
theorem q_identification_from_witness
    (W : DeformationParameterWitness) :
    W.q = W.thermalParameter :=
  W.q_eq_thermalParameter

@[rep_depth thermo]
theorem q_identified_with_thermal_parameter_from_witness
    (W : DeformationParameterWitness) :
    W.q = W.thermalParameter :=
  W.q_eq_thermalParameter

end InfoGeometry.Canonical.DeformationLayer
