import Mathlib.Tactic
import InfoGeometry.GromovWittenErlangen.LieOrbitCurve
import InfoGeometry.OperatorAlgebra.DrazinProjectionLocalization

/-!
# InfoGeometry.GromovWittenErlangen.DrazinLocalization

Witness-gated bridge from Gromov-Witten fixed-sector localization data to the
Drazin regular/singular inverse pattern.

This module does not prove virtual localization, Dubrovin semisimplicity,
Wedderburn-Artin, or existence of quantum cohomology Frobenius manifolds.  It
records the finite algebraic data needed to interpret localization denominators
as Drazin-regular weights plus singular/nilpotent residues.
-/

noncomputable section

namespace InfoGeometry
namespace GromovWittenErlangen

open InfoGeometry.OperatorAlgebra.DrazinProjectionLocalization

/--
Drazin-localized fixed-sector packet for a GW/Erlangen localization graph.

`Algebra` is the finite localized coefficient algebra in which edge Euler
weights, inverse denominators, and residue terms live.  Each edge carries a
Drazin decomposition of its Euler denominator, representing the rule:

* invert the regular part;
* retain controlled nilpotent/singular residue data.
-/
structure GWDrazinLocalizationPacket
    (G T Target Coeff Algebra : Type*) [Ring Algebra] [StarRing Algebra] where
  /-- Existing fixed/edge-sector localization graph packet. -/
  virtualLocalization : VirtualLocalizationOrbitPacket G T Target Coeff

  /-- Euler or normal-weight denominator attached to each localization edge. -/
  edgeEulerWeight : virtualLocalization.graph.Edge → Algebra

  /-- Drazin regular/singular decomposition of every edge Euler denominator. -/
  edgeDrazin :
    ∀ _e : virtualLocalization.graph.Edge,
      RelativeCoreNilpotentDecomposition Algebra

  /-- The Drazin decomposition is attached to the corresponding Euler weight. -/
  edgeDrazin_element_eq :
    ∀ e : virtualLocalization.graph.Edge,
      (edgeDrazin e).element = edgeEulerWeight e

  /-- Vertex contribution after transport into the localized algebra. -/
  vertexAlgebraContribution : virtualLocalization.graph.Vertex → Algebra

  /-- Edge contribution after Drazin-regularized inversion/residue handling. -/
  edgeAlgebraContribution : virtualLocalization.graph.Edge → Algebra

  /-- Total localized readout. -/
  localizationValue : Algebra

namespace GWDrazinLocalizationPacket

variable {G T Target Coeff Algebra : Type*} [Ring Algebra] [StarRing Algebra]
variable (P : GWDrazinLocalizationPacket G T Target Coeff Algebra)

/-- Every localization edge supplies Drazin inverse data for its Euler weight. -/
def edgeDrazinData (e : P.virtualLocalization.graph.Edge) :
    DrazinInverseData Algebra :=
  (P.edgeDrazin e).toDrazinInverseData

/-- The edge Drazin inverse commutes with its edge Euler denominator. -/
theorem edgeDrazin_commutes (e : P.virtualLocalization.graph.Edge) :
    (P.edgeDrazinData e).element * (P.edgeDrazinData e).drazinInverse =
      (P.edgeDrazinData e).drazinInverse * (P.edgeDrazinData e).element :=
  (P.edgeDrazinData e).commutes

/-- The Drazin data element is the corresponding edge Euler denominator. -/
theorem edgeDrazinData_element_eq_weight
    (e : P.virtualLocalization.graph.Edge) :
    (P.edgeDrazinData e).element = P.edgeEulerWeight e :=
  P.edgeDrazin_element_eq e

/-- The localized Drazin residue carried by an edge denominator. -/
def edgeLocalizedDrazinResidue
    (e : P.virtualLocalization.graph.Edge) : Algebra :=
  (P.edgeDrazin e).localizedDrazinResidue

/-- The regular inverse carried by an edge denominator. -/
def edgeLocalizedRegularInverse
    (e : P.virtualLocalization.graph.Edge) : Algebra :=
  (P.edgeDrazin e).localizedRegularInverse

/-- Edge residues are left-supported by their residue projections. -/
theorem edgeResidue_supported_left
    (e : P.virtualLocalization.graph.Edge) :
    (P.edgeDrazin e).projections.residue *
        P.edgeLocalizedDrazinResidue e =
      P.edgeLocalizedDrazinResidue e :=
  (P.edgeDrazin e).residue_supported_left

/-- Edge residues are right-supported by their residue projections. -/
theorem edgeResidue_supported_right
    (e : P.virtualLocalization.graph.Edge) :
    P.edgeLocalizedDrazinResidue e *
        (P.edgeDrazin e).projections.residue =
      P.edgeLocalizedDrazinResidue e :=
  (P.edgeDrazin e).residue_supported_right

/-- Edge residues are killed on the right by the regular inverse. -/
theorem edgeResidue_mul_regularInverse
    (e : P.virtualLocalization.graph.Edge) :
    P.edgeLocalizedDrazinResidue e *
        P.edgeLocalizedRegularInverse e = 0 :=
  (P.edgeDrazin e).residue_mul_regularInverse

/-- Edge residues are killed on the left by the regular inverse. -/
theorem edgeRegularInverse_mul_residue
    (e : P.virtualLocalization.graph.Edge) :
    P.edgeLocalizedRegularInverse e *
        P.edgeLocalizedDrazinResidue e = 0 :=
  (P.edgeDrazin e).regularInverse_mul_residue

end GWDrazinLocalizationPacket

/--
Divisor-weight data for a localization graph.

This does not prove the GW divisor ax!om; it only stores finite edge/degree
weights that a model may use as input to a future theorem-facing divisor ax!om.
-/
structure LocalizationDivisorWeightData
    (G T Target Coeff : Type*) where
  virtualLocalization : VirtualLocalizationOrbitPacket G T Target Coeff
  DivisorClass : Type*
  divisorDegreeWeight :
    DivisorClass → virtualLocalization.graph.Edge → ℝ

/--
Semisimple/Frobenius calibration for a localized GW coefficient algebra.

In a commutative semisimple quantum cohomology model over an algebraically
closed field, the residue blocks specialize to field factors.  This packet keeps
that as supplied finite data, together with a Frobenius self-duality pairing.
-/
structure LocalizedFrobeniusSemisimplePacket (Algebra : Type*) [Ring Algebra] [StarRing Algebra] where
  frobenius : FrobeniusSelfDualPacket Algebra
  residueBlocks : DivisionResidueBlockPacket
  semisimple : IsSemisimpleRing Algebra

namespace LocalizedFrobeniusSemisimplePacket

variable {Algebra : Type*} [Ring Algebra] [StarRing Algebra]
variable (S : LocalizedFrobeniusSemisimplePacket Algebra)

/-- Frobenius compatibility of the localized pairing. -/
theorem pairing_mul_left_eq_pairing_mul_right
    (a b c : Algebra) :
    S.frobenius.pairing (a * b) c = S.frobenius.pairing a (b * c) :=
  S.frobenius.pairing_mul_left_eq_pairing_mul_right a b c

end LocalizedFrobeniusSemisimplePacket

/-- Integrated Drazin/GW localization doctrine packet. -/
structure DrazinGromovWittenLocalizationBridge
    (G T Target Coeff Algebra : Type*) [Ring Algebra] [StarRing Algebra] where
  drazinLocalization : GWDrazinLocalizationPacket G T Target Coeff Algebra
  divisorWeights : LocalizationDivisorWeightData G T Target Coeff
  frobeniusSemisimple : LocalizedFrobeniusSemisimplePacket Algebra

namespace DrazinGromovWittenLocalizationBridge

variable {G T Target Coeff Algebra : Type*} [Ring Algebra] [StarRing Algebra]
variable (B : DrazinGromovWittenLocalizationBridge G T Target Coeff Algebra)

/--
For every localization edge, the bridge provides algebraic Drazin inverse data
for the corresponding Euler denominator.
-/
def edgeDrazinData
    (e : B.drazinLocalization.virtualLocalization.graph.Edge) :
    DrazinInverseData Algebra :=
  B.drazinLocalization.edgeDrazinData e

/-- The bridge exposes the localized Drazin residue of an edge denominator. -/
def edgeLocalizedDrazinResidue
    (e : B.drazinLocalization.virtualLocalization.graph.Edge) : Algebra :=
  B.drazinLocalization.edgeLocalizedDrazinResidue e

/-- The bridge exposes the regular inverse of an edge denominator. -/
def edgeLocalizedRegularInverse
    (e : B.drazinLocalization.virtualLocalization.graph.Edge) : Algebra :=
  B.drazinLocalization.edgeLocalizedRegularInverse e

/-- Bridge-level edge residues are supported by the residue projection. -/
theorem edgeResidue_supported_left
    (e : B.drazinLocalization.virtualLocalization.graph.Edge) :
    (B.drazinLocalization.edgeDrazin e).projections.residue *
        B.edgeLocalizedDrazinResidue e =
      B.edgeLocalizedDrazinResidue e :=
  B.drazinLocalization.edgeResidue_supported_left e

/-- Bridge-level edge residues are killed by the regular inverse on the right. -/
theorem edgeResidue_mul_regularInverse
    (e : B.drazinLocalization.virtualLocalization.graph.Edge) :
    B.edgeLocalizedDrazinResidue e *
        B.edgeLocalizedRegularInverse e = 0 :=
  B.drazinLocalization.edgeResidue_mul_regularInverse e

end DrazinGromovWittenLocalizationBridge

/-! ## GW/Drazin volume-to-entropy calibration -/

/--
Calibrated entropy readout for a Drazin-localized GW packet.

This is intentionally a calibration layer:

* `gwVolume` is the supplied fixed-sector/virtual/localized volume readout;
* `cleanDrazinVolume` is the regular-core contribution after Drazin separation;
* `entropyReadout` is calibrated to `Real.log cleanDrazinVolume`;
* an explicit equality records when the clean Drazin volume agrees with the chosen GW
  volume readout.

No unconditional claim is made that every GW volume is positive, finite, or
equal to a state count.
-/
structure GWDrazinEntropyCalibration
    {G T Target Coeff Algebra : Type*} [Ring Algebra] [StarRing Algebra]
    (B : DrazinGromovWittenLocalizationBridge G T Target Coeff Algebra) where
  /-- Localized GW volume/readout supplied by the model. -/
  gwVolume : ℝ

  /-- Drazin-regular contribution treated as the clean finite volume. -/
  cleanDrazinVolume : ℝ

  /-- Entropy readout calibrated from the clean Drazin volume. -/
  entropyReadout : ℝ

  /-- Regular core contribution of each localization edge. -/
  edgeRegularVolume :
    B.drazinLocalization.virtualLocalization.graph.Edge → ℝ

  /-- Singular/residue contribution of each localization edge. -/
  edgeResidueVolume :
    B.drazinLocalization.virtualLocalization.graph.Edge → ℝ

  /-- The entropy is the logarithm of the clean Drazin volume. -/
  entropy_eq_log_cleanDrazinVolume :
    entropyReadout = Real.log cleanDrazinVolume

  /-- The clean Drazin volume is calibrated to the chosen GW volume. -/
  cleanDrazinVolume_eq_gwVolume :
    cleanDrazinVolume = gwVolume

namespace GWDrazinEntropyCalibration

variable {G T Target Coeff Algebra : Type*} [Ring Algebra] [StarRing Algebra]
variable {B : DrazinGromovWittenLocalizationBridge G T Target Coeff Algebra}
variable (C : GWDrazinEntropyCalibration B)

/-- The entropy is calibrated as the logarithm of the clean Drazin volume. -/
theorem entropy_eq_log_clean_volume :
    C.entropyReadout = Real.log C.cleanDrazinVolume :=
  C.entropy_eq_log_cleanDrazinVolume

/-- The clean Drazin volume is the selected GW volume readout. -/
theorem clean_volume_eq_gw_volume :
    C.cleanDrazinVolume = C.gwVolume :=
  C.cleanDrazinVolume_eq_gwVolume

/-- Entropy is also the logarithm of the calibrated GW volume. -/
theorem entropy_eq_log_gw_volume :
    C.entropyReadout = Real.log C.gwVolume := by
  rw [C.entropy_eq_log_cleanDrazinVolume, C.cleanDrazinVolume_eq_gwVolume]

/-- Each edge entropy packet still exposes the operator-level Drazin residue. -/
def edgeOperatorDrazinResidue
    (e : B.drazinLocalization.virtualLocalization.graph.Edge) : Algebra :=
  B.edgeLocalizedDrazinResidue e

/-- Each edge entropy packet still exposes the operator-level regular inverse. -/
def edgeOperatorRegularInverse
    (e : B.drazinLocalization.virtualLocalization.graph.Edge) : Algebra :=
  B.edgeLocalizedRegularInverse e

/--
The operator-level residue remains killed by the corresponding regular inverse.
-/
theorem edgeResidue_mul_regularInverse
    (e : B.drazinLocalization.virtualLocalization.graph.Edge) :
    B.edgeLocalizedDrazinResidue e *
        B.edgeLocalizedRegularInverse e = 0 :=
  B.edgeResidue_mul_regularInverse e

end GWDrazinEntropyCalibration

end GromovWittenErlangen
end InfoGeometry
