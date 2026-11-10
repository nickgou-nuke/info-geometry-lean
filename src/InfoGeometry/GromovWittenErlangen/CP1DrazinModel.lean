/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
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

/-- Build the fixed/edge localization packet with supplied sector weights. -/
def virtualLocalizationWithContributions
    (vertexWeight : Fixed → Coeff) (edgeWeight : Edge → Coeff) :
    VirtualLocalizationOrbitPacket G T Target Coeff where
  graph := localizationGraph
  vertexContribution := vertexWeight
  edgeContribution := edgeWeight

/-- A concrete two-sector example with distinct fixed-sector contributions. -/
def virtualLocalization : VirtualLocalizationOrbitPacket G T Target Coeff :=
  virtualLocalizationWithContributions
    (fun sector => match sector with
      | Fixed.zero => 1
      | Fixed.infinity => -1)
    (fun _ => 2)

/-- The two fixed points in the fixture carry genuinely different contributions. -/
theorem virtualLocalization_vertex_terms_distinct :
    virtualLocalization.vertexContribution Fixed.zero ≠
      virtualLocalization.vertexContribution Fixed.infinity := by
  change (1 : Int) ≠ -1
  norm_num

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

/-! ### Regular Drazin decomposition for a general nonzero edge weight -/

/-- A nonzero real edge weight is regular with inverse `w⁻¹` and zero residue. -/
def regularEdgeDrazinOfWeight (w : Algebra) (hw : w ≠ 0) :
    RelativeCoreNilpotentDecomposition Algebra where
  projections := regularProjections
  element := w
  regularPart := w
  coreInv := w⁻¹
  nilpotentPart := 0
  element_eq_regular_add_nilpotent := by simp
  regular_supported_left := by simp [regularProjections]
  regular_supported_right := by simp [regularProjections]
  nilpotent_residue_supported_left := by simp
  nilpotent_residue_supported_right := by simp
  coreInv_supported_left := by simp [regularProjections]
  coreInv_supported_right := by simp [regularProjections]
  regular_mul_coreInv := by simp [regularProjections, mul_inv_cancel₀ hw]
  coreInv_mul_regular := by simp [regularProjections, inv_mul_cancel₀ hw]
  nilpotent_mul_coreInv := by simp
  coreInv_mul_nilpotent := by simp
  nilpotent_isNilpotent := IsNilpotent.zero

/-- The unit edge fixture is the weight-one specialization of the regular construction. -/
def regularEdgeDrazin : RelativeCoreNilpotentDecomposition Algebra :=
  regularEdgeDrazinOfWeight 1 (by norm_num)

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
