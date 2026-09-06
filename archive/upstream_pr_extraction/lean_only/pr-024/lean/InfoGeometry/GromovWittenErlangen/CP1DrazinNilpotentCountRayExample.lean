import InfoGeometry.Canonical.RelativePotentialCountBridge
import InfoGeometry.Canonical.RelativeSurprisalOperatorLift
import InfoGeometry.GromovWittenErlangen.DrazinLocalization

/-!
# CP1 Drazin nilpotent count-ray example

Concrete smoke model combining two repo-native corridors:

* positive finite counts
  `→ countRay → gaugeSectionFinProb → density/surprisal operator`;
* one-edge GW/Drazin localization with a nonzero square-zero residue sector.

The point is deliberately narrow.  Projective count normalization is independent
of the Drazin defect; Drazin regularization acts on the localization/operator
layer and isolates the nilpotent residue.
-/

noncomputable section

namespace InfoGeometry
namespace GromovWittenErlangen
namespace CP1DrazinNilpotentCountRayExample

open InfoGeometry.Canonical.RelativePotentialCountBridge
open InfoGeometry.Canonical.RelativePotentialDiscreteBridge
open InfoGeometry.Canonical.RelativeSurprisalOperatorLift
open InfoGeometry.MaxEnt.JaynesInfoStatMech.ThermalDiagonal
open InfoGeometry.OperatorAlgebra.DrazinProjectionLocalization

attribute [local instance] starRingOfComm

/-! ## Positive finite count/probability/operator corridor -/

/-- Concrete positive sample counts `(20, 30, 10)`. -/
def sampleCounts : RelativeCounts 3 :=
  fun i => if i = 0 then 20 else if i = 1 then 30 else 10

/-- Concrete positive reference counts `(10, 10, 10)`. -/
def referenceCounts : RelativeCounts 3 :=
  fun _ => 10

/-- The concrete sample counts are pointwise positive. -/
theorem sampleCounts_pos (i : Fin 3) : 0 < sampleCounts i := by
  fin_cases i <;> norm_num [sampleCounts]

/-- The concrete reference counts are pointwise positive. -/
theorem referenceCounts_pos (i : Fin 3) : 0 < referenceCounts i := by
  norm_num [referenceCounts]

/-- Positive projective count ray of the concrete sample counts. -/
def sampleCountRay :
    InfoGeometry.Canonical.PositiveRayCore.PositiveRay (Fin 3) :=
  countRay sampleCounts sampleCounts_pos

/-- Probability gauge section of the concrete sample count ray. -/
def sampleFinProb : InfoGeometry.FinProb (Fin 3) :=
  gaugeSectionFinProb (α := Fin 3) sampleCountRay

/-- The probability gauge has the expected normalized-count real readout. -/
theorem sampleFinProb_apply_toReal (i : Fin 3) :
    (sampleFinProb i).toReal =
      sampleCounts i / countMass sampleCounts sampleCounts_pos := by
  exact gaugeSectionFinProb_countRay_apply_toReal
    (n := 3) (counts := sampleCounts) (hcounts := sampleCounts_pos) i

/-- Diagonal density matrix of the concrete probability gauge. -/
def sampleDensityMatrix : FinMat 3 :=
  densityMatrixOfFinProb sampleFinProb

/-- First-quantized surprisal operator of the concrete probability gauge. -/
def sampleSurprisalOperator : FinMat 3 :=
  surprisalOperator sampleFinProb

/-- Density diagonal entries are the normalized count masses. -/
theorem sampleDensityMatrix_diag (i : Fin 3) :
    sampleDensityMatrix i i =
      sampleCounts i / countMass sampleCounts sampleCounts_pos := by
  rw [sampleDensityMatrix, densityMatrixOfFinProb_diag]
  exact sampleFinProb_apply_toReal i

/-- Entropy of the probability gauge is expectation of the surprisal operator. -/
theorem sampleEntropy_eq_diagonalExpectation_surprisalOperator :
    InfoGeometry.entropy sampleFinProb =
      diagonalExpectation sampleFinProb sampleSurprisalOperator := by
  rw [sampleSurprisalOperator]
  exact entropy_eq_diagonalExpectation_surprisalOperator sampleFinProb

/-- Projective count Hamiltonian profile for the concrete sample/reference pair. -/
def sampleProjectiveHamiltonian : Fin 3 → ℝ :=
  projectiveCountHamiltonianProfile
    sampleCounts referenceCounts sampleCounts_pos referenceCounts_pos

/-- Raw relative count modular-potential operator for the concrete pair. -/
def sampleRawRelativeCountPotentialOperator : FinMat 3 :=
  relativeCountModularPotentialOperator sampleCounts referenceCounts

/-! ## Minimal GW/Drazin nilpotent-defect corridor -/

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
abbrev Algebra := ℤ × ZMod 4

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

/-- Complementary support/residue projections for the product coefficient algebra. -/
def defectProjections : SelfAdjointIdempotentPair Algebra where
  support := (1, 0)
  residue := (0, 1)
  support_idem := by ext <;> norm_num
  residue_idem := by ext <;> norm_num
  support_residue_zero := by ext <;> norm_num
  residue_support_zero := by ext <;> norm_num
  support_add_residue := by ext <;> norm_num
  support_selfAdjoint := by ext <;> norm_num
  residue_selfAdjoint := by ext <;> norm_num

/--
One-edge Drazin decomposition with regular denominator in the first factor and
nonzero square-zero residue in the second factor.
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
  nilpotent_isNilpotent := by
    refine ⟨2, ?_⟩
    ext
    · norm_num
    · native_decide

/-- The concrete residue is square-zero in the `ZMod 4` factor. -/
theorem defectResidue_square_zero :
    ((0, (2 : ZMod 4)) : Algebra) * ((0, (2 : ZMod 4)) : Algebra) = 0 := by
  ext
  · norm_num
  · native_decide

/-- The concrete residue is killed by the regular inverse on the right. -/
theorem defectResidue_mul_regularInverse :
    ((0, (2 : ZMod 4)) : Algebra) * ((1, (0 : ZMod 4)) : Algebra) = 0 := by
  ext <;> norm_num

/-- The concrete residue is killed by the regular inverse on the left. -/
theorem defectRegularInverse_mul_residue :
    ((1, (0 : ZMod 4)) : Algebra) * ((0, (2 : ZMod 4)) : Algebra) = 0 := by
  ext <;> norm_num

/-- The unique edge carries the product denominator `(1, 2)`. -/
theorem edgeDrazinData_element_line :
    defectEdgeDrazin.element = (1, 2) :=
  rfl

/-- The unique edge has a visibly nonzero localized Drazin residue. -/
theorem edgeLocalizedDrazinResidue_line :
    defectEdgeDrazin.localizedDrazinResidue = (0, 2) :=
  rfl

/-- The localized residue is square-zero. -/
theorem edgeLocalizedDrazinResidue_square_zero_line :
    defectEdgeDrazin.localizedDrazinResidue *
        defectEdgeDrazin.localizedDrazinResidue = 0 := by
  exact defectResidue_square_zero

/-- The residue is killed by the localized regular inverse. -/
theorem edgeResidue_mul_regularInverse_line :
    defectEdgeDrazin.localizedDrazinResidue *
        defectEdgeDrazin.localizedRegularInverse = 0 :=
  defectEdgeDrazin.residue_mul_regularInverse

/-- The localized regular inverse kills the residue on the left. -/
theorem edgeRegularInverse_mul_residue_line :
    defectEdgeDrazin.localizedRegularInverse *
        defectEdgeDrazin.localizedDrazinResidue = 0 :=
  defectEdgeDrazin.regularInverse_mul_residue

end CP1DrazinNilpotentCountRayExample
end GromovWittenErlangen
end InfoGeometry
