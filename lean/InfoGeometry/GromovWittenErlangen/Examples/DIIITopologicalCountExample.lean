import InfoGeometry.GromovWittenErlangen.CP1DrazinNilpotentDefectModel
import InfoGeometry.Quantum.KitaevChain

/-!
# InfoGeometry.GromovWittenErlangen.Examples.DIIITopologicalCountExample

Concrete three-sector target surface for the projective-count/probability/Drazin
descent.

The example fixes a positive three-sector count representative:

```text
bulk/stable sector      100
boundary zero-mode      2
residue/noise sector    1
```

The count representative remains strictly positive, so it descends through the
repo-owned `countRay → gaugeSectionFinProb → density/surprisal operator`
corridor.  The Drazin residue is carried separately by the concrete
`CP1DrazinNilpotentDefectModel.defectEdgeDrazin` data, whose unique edge has
square-zero residue `(0, 2) : ℤ × ZMod 4`.

This file does not construct a concrete BdG/Kitaev Hamiltonian.  The DIII
`topologicalIndexZ2 = 1` datum is recorded as a witness packet, so the actual
chain/bulk-boundary proof remains separate from the count/probability/Drazin
corridor.
-/

noncomputable section

namespace DIIITopologicalCountExample

open InfoGeometry.Canonical.RelativePotentialCountBridge
open InfoGeometry.Quantum.KitaevChain

attribute [local instance] starRingOfComm

abbrev G := CP1DrazinNilpotentDefectModel.G
abbrev T := CP1DrazinNilpotentDefectModel.T
abbrev Target := CP1DrazinNilpotentDefectModel.Target
abbrev Coeff := CP1DrazinNilpotentDefectModel.Coeff
abbrev Algebra := CP1DrazinNilpotentDefectModel.Algebra

/-- Three count sectors: bulk, boundary zero-mode, and residue/noise. -/
inductive Sector where
  | bulk
  | boundary
  | residue
deriving DecidableEq, Repr

/--
Witness that a concrete Kitaev chain is in the nontrivial DIII/`ZMod 2` sector.

This is intentionally separated from the count example: the present file fixes
the arithmetic/operator target surface, while a model-specific BdG file supplies
the actual chain witness.
-/
structure DIIIZ2SectorWitness where
  chain : List KitaevCell
  topologicalIndexZ2_eq_one : topologicalIndexZ2 chain = 1

/-- Positive three-sector count representative for the DIII count target. -/
def counts : RelativeCounts 3 :=
  fun i =>
    if i = (0 : Fin 3) then 100
    else if i = (1 : Fin 3) then 2
    else 1

/-- Positive reference profile for the three-sector count target. -/
def referenceCounts : RelativeCounts 3 :=
  fun _ => 1

/-- The bulk sector has raw count `100`. -/
theorem counts_zero :
    counts (0 : Fin 3) = 100 := by
  simp [counts]

/-- The boundary zero-mode sector has raw count `2`. -/
theorem counts_one :
    counts (1 : Fin 3) = 2 := by
  simp [counts]

/-- The residue/noise sector remains positive at raw count `1`. -/
theorem counts_two :
    counts (2 : Fin 3) = 1 := by
  have h20 : (2 : Fin 3) ≠ (0 : Fin 3) := by decide
  have h21 : (2 : Fin 3) ≠ (1 : Fin 3) := by decide
  simp [counts, h20, h21]

/-- The concrete count representative is strictly positive. -/
theorem counts_pos :
    ∀ i : Fin 3, 0 < counts i := by
  intro i
  fin_cases i <;> norm_num [counts]

/-- The reference count representative is strictly positive. -/
theorem referenceCounts_pos :
    ∀ i : Fin 3, 0 < referenceCounts i := by
  intro i
  simp [referenceCounts]

/-- Primitive `CountProfile` shadow of the three-sector finite count vector. -/
def countProfile : InfoGeometry.Arithmetic.PrimitiveProjectiveRays.CountProfile :=
  fun n =>
    if n = 0 then 100
    else if n = 1 then 2
    else if n = 2 then 1
    else 0

/-- The three active arithmetic labels. -/
def support : Finset ℕ :=
  Finset.range 3

/-- Map CP1 fixed vertices into the three-sector count carrier. -/
def vertexAtom : CP1DrazinModel.Fixed → Fin 3
  | CP1DrazinModel.Fixed.zero => 0
  | CP1DrazinModel.Fixed.infinity => 1

/-- Map the unique CP1 edge into the residue/noise count sector. -/
def edgeAtom : CP1DrazinModel.Edge → Fin 3
  | CP1DrazinModel.Edge.line => 2

/-- GW localization count-shadow calibration for the concrete three-sector profile. -/
def projectiveCountCalibration : GWProjectiveCountCalibration G T Target Coeff where
  localization := CP1DrazinNilpotentDefectModel.virtualLocalization
  CountAtom := Fin 3
  atomCode := fun i => i.val
  counts := countProfile
  support := support
  vertexAtom := vertexAtom
  edgeAtom := edgeAtom
  coeffReadout := fun z => (z : ℝ)

/-- Canonical count-ray/probability/operator bridge for the concrete counts. -/
def canonicalCountRayBridge : GWCanonicalCountRayBridge 3 G T Target Coeff where
  projectiveCounts := projectiveCountCalibration
  counts := counts
  ref := referenceCounts
  counts_pos := counts_pos
  ref_pos := referenceCounts_pos

/-- Probability/operator bridge for the concrete count-ray target. -/
def projectiveProbabilityBridge :
    GWProjectiveCountProbabilityBridge 3 G T Target Coeff where
  canonical := canonicalCountRayBridge

/-- The probability gauge of the bulk sector is the normalized count value. -/
theorem stateFinProb_bulk_toReal :
    (canonicalCountRayBridge.stateFinProb (0 : Fin 3)).toReal =
      counts (0 : Fin 3) / countMass counts counts_pos :=
  canonicalCountRayBridge.stateFinProb_apply_toReal 0

/-- The probability gauge of the boundary sector is the normalized count value. -/
theorem stateFinProb_boundary_toReal :
    (canonicalCountRayBridge.stateFinProb (1 : Fin 3)).toReal =
      counts (1 : Fin 3) / countMass counts counts_pos :=
  canonicalCountRayBridge.stateFinProb_apply_toReal 1

/-- The density-matrix diagonal of the boundary sector is its normalized count value. -/
theorem densityMatrix_boundary_diag :
    canonicalCountRayBridge.stateDensityMatrix (1 : Fin 3) (1 : Fin 3) =
      counts (1 : Fin 3) / countMass counts counts_pos :=
  canonicalCountRayBridge.stateDensityMatrix_diag 1

/-- Entropy of the probability gauge is expectation of the surprisal operator. -/
theorem entropy_eq_surprisal_expectation :
    InfoGeometry.entropy projectiveProbabilityBridge.stateFinProb =
      InfoGeometry.Canonical.RelativeSurprisalOperatorLift.diagonalExpectation
        projectiveProbabilityBridge.stateFinProb
        projectiveProbabilityBridge.stateSurprisalOperator :=
  projectiveProbabilityBridge.entropy_eq_diagonalExpectation_stateSurprisalOperator

/-- The Drazin residue in the edge sector is square-zero. -/
theorem drazin_residue_square_zero :
    CP1DrazinNilpotentDefectModel.defectEdgeDrazin.localizedDrazinResidue *
        CP1DrazinNilpotentDefectModel.defectEdgeDrazin.localizedDrazinResidue = 0 := by
  change (((0 : ℤ), (2 : ZMod 4)) : CP1DrazinNilpotentDefectModel.Algebra) *
      (((0 : ℤ), (2 : ZMod 4)) : CP1DrazinNilpotentDefectModel.Algebra) = 0
  exact CP1DrazinNilpotentDefectModel.residue_square_zero

/-- The nonzero Drazin residue is killed by the regular inverse on the right. -/
theorem drazin_residue_mul_regularInverse :
    CP1DrazinNilpotentDefectModel.defectEdgeDrazin.localizedDrazinResidue *
        CP1DrazinNilpotentDefectModel.defectEdgeDrazin.localizedRegularInverse = 0 :=
  CP1DrazinNilpotentDefectModel.edgeLocalizedDrazinResidue_mul_regularInverse_line

/-- The regular inverse kills the nonzero Drazin residue on the left. -/
theorem drazin_regularInverse_mul_residue :
    CP1DrazinNilpotentDefectModel.defectEdgeDrazin.localizedRegularInverse *
        CP1DrazinNilpotentDefectModel.defectEdgeDrazin.localizedDrazinResidue = 0 :=
  CP1DrazinNilpotentDefectModel.edgeRegularInverse_mul_localizedDrazinResidue_line

end DIIITopologicalCountExample
