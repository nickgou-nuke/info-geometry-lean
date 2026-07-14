import ZornOPParavector
import GrandUnifiedTKK
import CartanTriality

/-!
# Zorn triality to TKK grading bridge

This file does one thing only:

* it packages the canonical split-octonion lanes into named sectors;
* it sends those sectors into the existing five TKK grades;
* it records the mirror involution that swaps the `+1` and `-1` lanes.

It does not claim a full embedding of all split octonions into the TKK algebra.
That stronger statement still needs a carrier map and a bracket-compatibility
theorem. The present file is the theorem-honest interface layer.
-/

noncomputable section

namespace ZornTrialityTKKBridge

open ZornOPParavector
open GrandUnifiedTKK
open CartanTriality

/-- Canonical split-octonion lane tags used by the bridge. -/
inductive SplitOctonionLane where
  | diagonalProjector
  | upperNilpotent
  | lowerNilpotent
  | associatorWitness
  deriving DecidableEq, Repr

/-- Internal sector labels before landing in TKK grades. -/
inductive ZornSector where
  | neutral
  | positive
  | negative
  | defect
  deriving DecidableEq, Repr

/-- The mirror involution swaps the two nilpotent lanes and fixes the others. -/
def laneMirror : SplitOctonionLane → SplitOctonionLane
  | .diagonalProjector => .diagonalProjector
  | .upperNilpotent => .lowerNilpotent
  | .lowerNilpotent => .upperNilpotent
  | .associatorWitness => .associatorWitness

@[simp]
theorem laneMirror_involutive (s : SplitOctonionLane) :
    laneMirror (laneMirror s) = s := by
  cases s <;> rfl

/-- The sector landing map for split-octonion generators. -/
def laneSector : SplitOctonionLane → ZornSector
  | .diagonalProjector => .neutral
  | .upperNilpotent => .positive
  | .lowerNilpotent => .negative
  | .associatorWitness => .defect

/-- The TKK grade landing map. -/
def sectorGrade : ZornSector → TKK_Grade
  | .neutral => TKK_Grade.g_0
  | .positive => TKK_Grade.g_1
  | .negative => TKK_Grade.g_neg1
  | .defect => TKK_Grade.g_2

/-- The composite landing map from canonical split-octonion lanes into TKK grades. -/
def laneGrade : SplitOctonionLane → TKK_Grade :=
  fun s => sectorGrade (laneSector s)

@[simp] theorem laneGrade_diagonalProjector :
    laneGrade SplitOctonionLane.diagonalProjector = TKK_Grade.g_0 := rfl

@[simp] theorem laneGrade_upperNilpotent :
    laneGrade SplitOctonionLane.upperNilpotent = TKK_Grade.g_1 := rfl

@[simp] theorem laneGrade_lowerNilpotent :
    laneGrade SplitOctonionLane.lowerNilpotent = TKK_Grade.g_neg1 := rfl

@[simp] theorem laneGrade_associatorWitness :
    laneGrade SplitOctonionLane.associatorWitness = TKK_Grade.g_2 := rfl

/-- The mirror swaps the `+1` and `-1` TKK lanes. -/
@[simp]
theorem laneGrade_mirror_upper :
    laneGrade (laneMirror SplitOctonionLane.upperNilpotent) = TKK_Grade.g_neg1 := by
  rfl

@[simp]
theorem laneGrade_mirror_lower :
    laneGrade (laneMirror SplitOctonionLane.lowerNilpotent) = TKK_Grade.g_1 := by
  rfl

/-- The diagonal projector stays in grade zero under the mirror. -/
@[simp]
theorem laneGrade_mirror_diagonal :
    laneGrade (laneMirror SplitOctonionLane.diagonalProjector) = TKK_Grade.g_0 := by
  rfl

/-- The associator witness stays in the extremal grade under the mirror. -/
@[simp]
theorem laneGrade_mirror_associator :
    laneGrade (laneMirror SplitOctonionLane.associatorWitness) = TKK_Grade.g_2 := by
  rfl

/-- Summary theorem: the canonical split-octonion lanes land in the expected TKK grades. -/
theorem canonical_lane_grade_synthesis :
    laneGrade SplitOctonionLane.diagonalProjector = TKK_Grade.g_0 ∧
    laneGrade SplitOctonionLane.upperNilpotent = TKK_Grade.g_1 ∧
    laneGrade SplitOctonionLane.lowerNilpotent = TKK_Grade.g_neg1 ∧
    laneGrade SplitOctonionLane.associatorWitness = TKK_Grade.g_2 ∧
    laneMirror (laneMirror SplitOctonionLane.upperNilpotent) =
      SplitOctonionLane.upperNilpotent := by
  have hDiagonal : laneGrade SplitOctonionLane.diagonalProjector = TKK_Grade.g_0 :=
    laneGrade_diagonalProjector
  have hUpper : laneGrade SplitOctonionLane.upperNilpotent = TKK_Grade.g_1 :=
    laneGrade_upperNilpotent
  have hLower : laneGrade SplitOctonionLane.lowerNilpotent = TKK_Grade.g_neg1 :=
    laneGrade_lowerNilpotent
  have hDefect : laneGrade SplitOctonionLane.associatorWitness = TKK_Grade.g_2 :=
    laneGrade_associatorWitness
  have hMirror :
      laneMirror (laneMirror SplitOctonionLane.upperNilpotent) =
        SplitOctonionLane.upperNilpotent :=
    laneMirror_involutive _
  exact ⟨hDiagonal, hUpper, hLower, hDefect, hMirror⟩

/-- Optional bridge readout: the `Z2` mirror and `Z3`-style lane routing are
kept separate at the type level. -/
structure LaneRouting where
  lane : SplitOctonionLane
  sector : ZornSector
  grade : TKK_Grade
  h_lane_sector : sector = laneSector lane
  h_sector_grade : grade = sectorGrade sector

/-- A canonical routing record for the four named generators. -/
def canonicalRouting : SplitOctonionLane → LaneRouting
  | .diagonalProjector =>
      { lane := .diagonalProjector
        sector := .neutral
        grade := TKK_Grade.g_0
        h_lane_sector := rfl
        h_sector_grade := rfl }
  | .upperNilpotent =>
      { lane := .upperNilpotent
        sector := .positive
        grade := TKK_Grade.g_1
        h_lane_sector := rfl
        h_sector_grade := rfl }
  | .lowerNilpotent =>
      { lane := .lowerNilpotent
        sector := .negative
        grade := TKK_Grade.g_neg1
        h_lane_sector := rfl
        h_sector_grade := rfl }
  | .associatorWitness =>
      { lane := .associatorWitness
        sector := .defect
        grade := TKK_Grade.g_2
        h_lane_sector := rfl
        h_sector_grade := rfl }

@[simp]
theorem canonicalRouting_grade (s : SplitOctonionLane) :
    (canonicalRouting s).grade = laneGrade s := by
  cases s <;> rfl

end ZornTrialityTKKBridge
