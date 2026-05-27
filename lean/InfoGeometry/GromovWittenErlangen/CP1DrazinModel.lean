import InfoGeometry.GromovWittenErlangen.DrazinLocalization

/-!
# Minimal CP1-style Drazin localization model

This file records the concrete two-fixed-point, one-edge localization graph and
the regular Drazin decomposition of its unit edge denominator. It is not a proof
of Atiyah-Bott localization for `CP^1`.
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
  support_selfAdjoint := by
    norm_num
  residue_selfAdjoint := by
    norm_num

/-- The regular edge denominator `1` has Drazin inverse `1` and zero residue. -/
def regularEdgeDrazin : RelativeCoreNilpotentDecomposition Algebra where
  projections := regularProjections
  element := 1
  regularPart := 1
  coreInv := 1
  nilpotentPart := 0
  element_eq_regular_add_nilpotent := by norm_num
  regular_supported_left := by norm_num [regularProjections]
  regular_supported_right := by norm_num [regularProjections]
  nilpotent_residue_supported_left := by norm_num
  nilpotent_residue_supported_right := by norm_num
  coreInv_supported_left := by norm_num [regularProjections]
  coreInv_supported_right := by norm_num [regularProjections]
  regular_mul_coreInv := by norm_num [regularProjections]
  coreInv_mul_regular := by norm_num [regularProjections]
  nilpotent_mul_coreInv := by norm_num
  coreInv_mul_nilpotent := by norm_num
  nilpotent_isNilpotent := by
    exact IsNilpotent.zero

/-- Trivial Frobenius self-duality packet over the integer coefficient algebra. -/
def frobenius : FrobeniusSelfDualPacket Algebra where
  pairing := fun a b => (a * b : ℤ)
  pairing_mul_left_eq_pairing_mul_right := by
    intro a b c
    norm_num [mul_assoc]
  nondegenerate := by
    intro a h
    have h1 : ((a * 1 : ℤ) : ℝ) = 0 := h 1
    norm_num at h1
    exact_mod_cast h1

/-- The unique edge carries the regular Drazin denominator `1`. -/
theorem edgeDrazinData_element_line :
    regularEdgeDrazin.element = 1 :=
  rfl

/-- The unique edge has zero localized Drazin residue. -/
theorem edgeLocalizedDrazinResidue_line :
    regularEdgeDrazin.localizedDrazinResidue = 0 :=
  rfl

end CP1DrazinModel
end GromovWittenErlangen
end InfoGeometry
