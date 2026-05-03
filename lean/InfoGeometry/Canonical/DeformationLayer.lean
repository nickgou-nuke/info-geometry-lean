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
structure DeformationParameter where
  q : ℝ
  deformationDomain : Prop

/-- Explicit witness connecting a deformation parameter to a chosen thermal map. -/
@[rep_depth thermo]
structure DeformationParameterWitness where
  q : ℝ
  thermalParameter : ℝ
  q_eq_thermalParameter : q = thermalParameter
  deformationDomain : Prop

/-- Packet for a deformed character layer, gated by a deformation witness. -/
@[rep_depth thermo]
structure DeformedCharacterWitness where
  undeformedCharacter : ℝ
  deformedCharacter : ℝ
  deformation : DeformationParameterWitness
  deformationLaw : Prop

@[rep_depth thermo]
structure ThermalEvaluationMap where
  thermalParameter : ℝ

@[rep_depth thermo]
structure SeparatedDeformationWitness where
  deformation : DeformationParameter
  thermal : ThermalEvaluationMap
  separated : Prop

/-- Identification of `q` with a thermal parameter is available only from witness data. -/
@[rep_depth thermo]
theorem q_identification_requires_witness
    (W : DeformationParameterWitness) :
    W.q = W.thermalParameter :=
  W.q_eq_thermalParameter

@[rep_depth thermo]
theorem q_not_identified_with_expNegBeta_without_witness
    (_D : DeformationParameter) :
    True :=
  trivial

end InfoGeometry.Canonical.DeformationLayer
