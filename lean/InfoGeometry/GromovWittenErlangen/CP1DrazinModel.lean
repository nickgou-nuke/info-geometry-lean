import InfoGeometry.GromovWittenErlangen.DrazinLocalization
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Algebra.Coalgebra.FrobeniusPairing

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

abbrev G := Fixed
abbrev T := Degree
abbrev Target := Fixed
abbrev Coeff := ℤ
abbrev Algebra := ℝ

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

/-- Frobenius self-duality over the real localized coefficient algebra. -/
def frobenius : FrobeniusSelfDualPacket Algebra where
  functional := AddMonoidHom.id ℝ
  nondegenerate := by
    intro a h
    have h1 := h 1
    simpa using h1

end CP1DrazinModel
end GromovWittenErlangen
end InfoGeometry
