import InfoGeometry.Canonical.TKKJordanPairData

/-!
# Zorn triality to TKK grading bridge

This recovered owner keeps the theorem-honest interface layer from the archived
`ZornAuto/ZornTrialityTKKBridge` lane:

* package the canonical split-octonion lanes into named sectors;
* send those sectors into the five TKK grades;
* record the mirror involution swapping the `+1` and `-1` lanes.

It does not claim a full embedding of split octonions into a concrete TKK Lie
algebra. That stronger statement still needs a carrier map and a bracket
compatibility theorem in a restored downstream owner.
-/

noncomputable section

namespace ZornTrialityTKKBridge

open TKKJordanPairData
open TKKJordanPairData.TKKGrade

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
def sectorGrade : ZornSector → TKKGrade
  | .neutral => z0
  | .positive => p1
  | .negative => m1
  | .defect => p2

/-- The composite landing map from canonical split-octonion lanes into TKK grades. -/
def laneGrade : SplitOctonionLane → TKKGrade :=
  fun s => sectorGrade (laneSector s)

@[simp] theorem laneGrade_diagonalProjector :
    laneGrade SplitOctonionLane.diagonalProjector = z0 := rfl

@[simp] theorem laneGrade_upperNilpotent :
    laneGrade SplitOctonionLane.upperNilpotent = p1 := rfl

@[simp] theorem laneGrade_lowerNilpotent :
    laneGrade SplitOctonionLane.lowerNilpotent = m1 := rfl

@[simp] theorem laneGrade_associatorWitness :
    laneGrade SplitOctonionLane.associatorWitness = p2 := rfl

/-- The mirror swaps the `+1` and `-1` TKK lanes. -/
@[simp]
theorem laneGrade_mirror_upper :
    laneGrade (laneMirror SplitOctonionLane.upperNilpotent) = m1 := by
  rfl

@[simp]
theorem laneGrade_mirror_lower :
    laneGrade (laneMirror SplitOctonionLane.lowerNilpotent) = p1 := by
  rfl

/-- The diagonal projector stays in grade zero under the mirror. -/
@[simp]
theorem laneGrade_mirror_diagonal :
    laneGrade (laneMirror SplitOctonionLane.diagonalProjector) = z0 := by
  rfl

/-- The associator witness stays in the extremal grade under the mirror. -/
@[simp]
theorem laneGrade_mirror_associator :
    laneGrade (laneMirror SplitOctonionLane.associatorWitness) = p2 := by
  rfl

/-- Summary theorem: the canonical split-octonion lanes land in the expected TKK grades. -/
theorem canonical_lane_grade_synthesis :
    laneGrade SplitOctonionLane.diagonalProjector = z0 ∧
    laneGrade SplitOctonionLane.upperNilpotent = p1 ∧
    laneGrade SplitOctonionLane.lowerNilpotent = m1 ∧
    laneGrade SplitOctonionLane.associatorWitness = p2 ∧
    laneMirror (laneMirror SplitOctonionLane.upperNilpotent) =
      SplitOctonionLane.upperNilpotent := by
  exact ⟨laneGrade_diagonalProjector, laneGrade_upperNilpotent,
    laneGrade_lowerNilpotent, laneGrade_associatorWitness,
    laneMirror_involutive _⟩

/-!
The routing record carried no independent data: both its sector and grade were
definitionally determined by its lane.  Use the canonical lane carrier and
derive the historical projections instead of storing equality evidence.
-/
abbrev LaneRouting := SplitOctonionLane

namespace LaneRouting

def lane (r : LaneRouting) : SplitOctonionLane := r

def sector (r : LaneRouting) : ZornSector := laneSector r.lane

def grade (r : LaneRouting) : TKKGrade := sectorGrade r.sector

end LaneRouting

/-- A canonical routing record for the four named generators. -/
def canonicalRouting : SplitOctonionLane → LaneRouting := id

@[simp]
theorem canonicalRouting_grade (s : SplitOctonionLane) :
    (canonicalRouting s).grade = laneGrade s := by
  rfl

end ZornTrialityTKKBridge
