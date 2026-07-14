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

open InfoGeometry.Canonical.TKKJordanPairData

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
  | .neutral => TKKGrade.z0
  | .positive => TKKGrade.p1
  | .negative => TKKGrade.m1
  | .defect => TKKGrade.p2

/-- The composite landing map from canonical split-octonion lanes into TKK grades. -/
def laneGrade : SplitOctonionLane → TKKGrade :=
  fun s => sectorGrade (laneSector s)

@[simp] theorem laneGrade_diagonalProjector :
    laneGrade SplitOctonionLane.diagonalProjector = TKKGrade.z0 := rfl

@[simp] theorem laneGrade_upperNilpotent :
    laneGrade SplitOctonionLane.upperNilpotent = TKKGrade.p1 := rfl

@[simp] theorem laneGrade_lowerNilpotent :
    laneGrade SplitOctonionLane.lowerNilpotent = TKKGrade.m1 := rfl

@[simp] theorem laneGrade_associatorWitness :
    laneGrade SplitOctonionLane.associatorWitness = TKKGrade.p2 := rfl

/-- The mirror swaps the `+1` and `-1` TKK lanes. -/
@[simp]
theorem laneGrade_mirror_upper :
    laneGrade (laneMirror SplitOctonionLane.upperNilpotent) = TKKGrade.m1 := by
  rfl

@[simp]
theorem laneGrade_mirror_lower :
    laneGrade (laneMirror SplitOctonionLane.lowerNilpotent) = TKKGrade.p1 := by
  rfl

/-- The diagonal projector stays in grade zero under the mirror. -/
@[simp]
theorem laneGrade_mirror_diagonal :
    laneGrade (laneMirror SplitOctonionLane.diagonalProjector) = TKKGrade.z0 := by
  rfl

/-- The associator witness stays in the extremal grade under the mirror. -/
@[simp]
theorem laneGrade_mirror_associator :
    laneGrade (laneMirror SplitOctonionLane.associatorWitness) = TKKGrade.p2 := by
  rfl

/-- Summary theorem: the canonical split-octonion lanes land in the expected TKK grades. -/
theorem canonical_lane_grade_synthesis :
    laneGrade SplitOctonionLane.diagonalProjector = TKKGrade.z0 ∧
    laneGrade SplitOctonionLane.upperNilpotent = TKKGrade.p1 ∧
    laneGrade SplitOctonionLane.lowerNilpotent = TKKGrade.m1 ∧
    laneGrade SplitOctonionLane.associatorWitness = TKKGrade.p2 ∧
    laneMirror (laneMirror SplitOctonionLane.upperNilpotent) =
      SplitOctonionLane.upperNilpotent := by
  exact ⟨laneGrade_diagonalProjector, laneGrade_upperNilpotent,
    laneGrade_lowerNilpotent, laneGrade_associatorWitness,
    laneMirror_involutive _⟩

/-- Optional bridge readout: the mirror and lane routing stay separate at the type level. -/
structure LaneRouting where
  lane : SplitOctonionLane
  sector : ZornSector
  grade : TKKGrade
  h_lane_sector : sector = laneSector lane
  h_sector_grade : grade = sectorGrade sector

/-- A canonical routing record for the four named generators. -/
def canonicalRouting : SplitOctonionLane → LaneRouting
  | .diagonalProjector =>
      { lane := .diagonalProjector
        sector := .neutral
        grade := TKKGrade.z0
        h_lane_sector := rfl
        h_sector_grade := rfl }
  | .upperNilpotent =>
      { lane := .upperNilpotent
        sector := .positive
        grade := TKKGrade.p1
        h_lane_sector := rfl
        h_sector_grade := rfl }
  | .lowerNilpotent =>
      { lane := .lowerNilpotent
        sector := .negative
        grade := TKKGrade.m1
        h_lane_sector := rfl
        h_sector_grade := rfl }
  | .associatorWitness =>
      { lane := .associatorWitness
        sector := .defect
        grade := TKKGrade.p2
        h_lane_sector := rfl
        h_sector_grade := rfl }

@[simp]
theorem canonicalRouting_grade (s : SplitOctonionLane) :
    (canonicalRouting s).grade = laneGrade s := by
  cases s <;> rfl

end ZornTrialityTKKBridge
