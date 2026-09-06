import InfoGeometry.GromovWittenErlangen.DrazinLocalization

/-!
# Minimal CP1-style Drazin localization model

This file instantiates the Drazin/GW localization bridge on the smallest
two-fixed-point, one-edge localization graph.  It is a smoke model for the
interface, not a proof of Atiyah-Bott localization for `CP^1`.
-/

noncomputable section

namespace InfoGeometry
namespace GromovWittenErlangen
namespace CP1DrazinModel

open InfoGeometry.OperatorAlgebra.DrazinProjectionLocalization

/-- Two fixed sectors of the minimal `CP^1`-style graph. -/
inductive Fixed where
  | zero
  | infinity
deriving DecidableEq, Repr

/-- A single root/degree label for the unique orbit curve. -/
inductive Root where
  | alpha
deriving DecidableEq, Repr

/-- A single effective curve-degree label. -/
inductive Degree where
  | line
deriving DecidableEq, Repr

/-- One oriented edge between the two fixed sectors. -/
inductive Edge where
  | line
deriving DecidableEq, Repr

abbrev G := Unit
abbrev T := Unit
abbrev Target := Fixed
abbrev Coeff := ℤ
abbrev Algebra := ℤ

/-- Minimal homogeneous root shadow for a two-fixed-point line. -/
def rootShadow : HomogeneousRootShadow G where
  FixedLabel := Fixed
  RootLabel := Root
  CurveDegree := Degree
  rootDegree := fun _ => Degree.line

/-- Minimal orbit-curve witness. -/
def orbitWitness : LieOrbitCurveWitness G T Target where
  rootShadow := rootShadow
  fixedSector := fun x => x
  OrbitCurve := fun x y =>
    match x, y with
    | Fixed.zero, Fixed.infinity => Unit
    | _, _ => Empty
  orbitRoot := by
    intro x y C
    cases x <;> cases y <;> cases C
    exact Root.alpha
  orbitDegree := by
    intro x y C
    cases x <;> cases y <;> cases C
    exact Degree.line
  orbitDegree_eq_rootDegree := by
    intro x y C
    cases x <;> cases y <;> cases C
    rfl

/-- Minimal localization graph: two vertices and one line edge. -/
def localizationGraph : LocalizationGraphWitness G T Target where
  orbitWitness := orbitWitness
  Vertex := Fixed
  vertexLabel := fun x => x
  Edge := Edge
  source := fun _ => Fixed.zero
  target := fun _ => Fixed.infinity
  edgeCurve := fun
    | Edge.line => ()
  edgeDegree := fun _ => Degree.line
  edgeDegree_eq := by
    intro e
    cases e
    rfl

/-- Minimal virtual localization packet with unit contributions. -/
def virtualLocalization : VirtualLocalizationOrbitPacket G T Target Coeff where
  graph := localizationGraph
  vertexContribution := fun _ => 1
  edgeContribution := fun _ => 1

/-- Complementary support/residue projections for the regular edge weight `1`. -/
def regularProjections : SelfAdjointIdempotentPair Algebra where
  support := 1
  residue := 0
  support_idem := by norm_num
  residue_idem := by norm_num
  support_residue_zero := by norm_num
  residue_support_zero := by norm_num
  support_add_residue := by norm_num
  selfAdjointLaw := True
  selfAdjointCertificate := trivial

/-- The regular edge denominator `1` has Drazin inverse `1` and zero residue. -/
def regularEdgeDrazin : RelativeCoreNilpotentDecomposition Algebra where
  projections := regularProjections
  element := 1
  regularPart := 1
  coreInv := 1
  nilpotentPart := 0
  element_eq_regular_add_nilpotent := by norm_num
  regular_supported_left := by rfl
  regular_supported_right := by rfl
  nilpotent_residue_supported_left := by norm_num
  nilpotent_residue_supported_right := by norm_num
  coreInv_supported_left := by rfl
  coreInv_supported_right := by rfl
  regular_mul_coreInv := by rfl
  coreInv_mul_regular := by rfl
  nilpotent_mul_coreInv := by norm_num
  coreInv_mul_nilpotent := by norm_num
  nilpotentResidueLaw := True
  nilpotentResidueCertificate := trivial

/-- Drazin localization packet for the minimal graph. -/
def drazinLocalization : GWDrazinLocalizationPacket G T Target Coeff Algebra where
  virtualLocalization := virtualLocalization
  edgeEulerWeight := fun _ => 1
  edgeDrazin := fun _ => regularEdgeDrazin
  edgeDrazin_element_eq := by
    intro e
    cases e
    rfl
  vertexAlgebraContribution := fun _ => 1
  edgeAlgebraContribution := fun _ => 1
  localizationValue := 1
  localizationAssemblyLaw := True
  localizationAssemblyCertificate := trivial

/-- Minimal divisor packet: one divisor class with unit line degree. -/
def divisorAxiom : LocalizationDivisorAxiomPacket G T Target Coeff where
  virtualLocalization := virtualLocalization
  DivisorClass := Unit
  divisorDegreeWeight := fun _ _ => 1
  divisorInsertionLaw := True
  divisorInsertionCertificate := trivial

/-- Trivial Frobenius self-duality packet over the integer coefficient algebra. -/
def frobenius : FrobeniusSelfDualPacket Algebra where
  pairing := fun a b => (a * b : ℤ)
  pairing_mul_left_eq_pairing_mul_right := by
    intro a b c
    norm_num [mul_assoc]
  nondegeneracyLaw := True
  nondegeneracyCertificate := trivial

/-- Trivial residue block packet for the regular one-edge model. -/
def residueBlocks : DivisionResidueBlockPacket where
  Block := Unit
  DivisionCarrier := fun _ => Unit
  residueProjection := fun _ => Unit
  simpleResidueLaw := True
  simpleResidueCertificate := trivial

/-- Minimal semisimple/Frobenius packet. -/
def frobeniusSemisimple : LocalizedFrobeniusSemisimplePacket Algebra where
  frobenius := frobenius
  residueBlocks := residueBlocks
  semisimplicityLaw := True
  semisimplicityCertificate := trivial

/-- Integrated Drazin/GW localization bridge for the minimal graph. -/
def bridge : DrazinGromovWittenLocalizationBridge G T Target Coeff Algebra where
  drazinLocalization := drazinLocalization
  divisorAxiom := divisorAxiom
  frobeniusSemisimple := frobeniusSemisimple
  divisorDrazinCompatibilityLaw := True
  divisorDrazinCompatibilityCertificate := trivial

/-- The unique edge carries the regular Drazin denominator `1`. -/
theorem edgeDrazinData_element_line :
    (bridge.edgeDrazinData Edge.line).element = 1 :=
  bridge.drazinLocalization.edgeDrazinData_element_eq_weight Edge.line

/-- The unique edge has zero localized Drazin residue. -/
theorem edgeLocalizedDrazinResidue_line :
    bridge.edgeLocalizedDrazinResidue Edge.line = 0 :=
  rfl

/-- Calibrated entropy packet: clean volume `1`, entropy `log 1`. -/
def entropyCalibration : GWDrazinEntropyCalibration bridge where
  gwVolume := 1
  cleanDrazinVolume := 1
  entropyReadout := Real.log 1
  edgeRegularVolume := fun _ => 1
  edgeResidueVolume := fun _ => 0
  entropy_eq_log_cleanDrazinVolume := rfl
  cleanDrazinVolume_eq_gwVolume := rfl
  residueAccountingLaw := True
  residueAccountingCertificate := trivial

/-- The minimal model entropy is the logarithm of its calibrated GW volume. -/
theorem entropy_eq_log_gw_volume :
    entropyCalibration.entropyReadout = Real.log entropyCalibration.gwVolume :=
  entropyCalibration.entropy_eq_log_gw_volume

end CP1DrazinModel
end GromovWittenErlangen
end InfoGeometry
