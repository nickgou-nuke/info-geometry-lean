import InfoGeometry.Meta.Architecture
import InfoGeometry.Algebra.FiniteSpinAlgebra
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
structure DeformationParameter where
  q : ℝ
  deformationDomain : Set ℝ
  q_in_deformationDomain : q ∈ deformationDomain

/-- Explicit witness connecting a deformation parameter to a chosen thermal map. -/
@[rep_depth thermo]
structure DeformationParameterWitness where
  q : ℝ
  thermalParameter : ℝ
  q_eq_thermalParameter : q = thermalParameter
  deformationDomain : Set ℝ
  q_in_deformationDomain : q ∈ deformationDomain
  thermalParameter_in_deformationDomain : thermalParameter ∈ deformationDomain

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
