import proofs.FrozenPin55ManifoldFlow

/-!
# Graded natural generator basis for `O(5,5)`

This module refines the frozen `O(5,5)` flow by naming the natural
symmetry-adapted generator grading:

* positive-positive rotations;
* negative-negative rotations;
* positive-negative boosts.

For the split carrier `ℝ^{5,5}`, the full Lie algebra has
`C(5,2)+C(5,2)+5*5 = 10+10+25 = 45` generators.  If coordinates `0..3`
are frozen, the active sector has one positive coordinate and five negative
coordinates, hence `C(1,2)+C(5,2)+1*5 = 0+10+5 = 15` active generators.
-/

namespace O55GradedGeneratorBasis

/-- Natural generator grades for the split `O(5,5)` carrier. -/
inductive O55GeneratorGrade where
  | positiveRotation
  | negativeRotation
  | mixedBoost
  deriving DecidableEq, Repr

/-- `n choose 2`, used for same-sign rotation counts. -/
def chooseTwo (n : ℕ) : ℕ :=
  n * (n - 1) / 2

@[simp] theorem chooseTwo_five : chooseTwo 5 = 10 := by
  norm_num [chooseTwo]

@[simp] theorem chooseTwo_one : chooseTwo 1 = 0 := by
  norm_num [chooseTwo]

/-- Full `O(5,5)` positive-positive rotation count. -/
def fullPositiveRotationCount : ℕ := chooseTwo 5

/-- Full `O(5,5)` negative-negative rotation count. -/
def fullNegativeRotationCount : ℕ := chooseTwo 5

/-- Full `O(5,5)` mixed positive-negative boost count. -/
def fullMixedBoostCount : ℕ := 5 * 5

def fullGradedGeneratorCount : ℕ :=
  fullPositiveRotationCount + fullNegativeRotationCount + fullMixedBoostCount

@[simp] theorem full_positive_rotation_count_eq :
    fullPositiveRotationCount = 10 := by
  simp [fullPositiveRotationCount]

@[simp] theorem full_negative_rotation_count_eq :
    fullNegativeRotationCount = 10 := by
  simp [fullNegativeRotationCount]

@[simp] theorem full_mixed_boost_count_eq :
    fullMixedBoostCount = 25 := by
  norm_num [fullMixedBoostCount]

@[simp] theorem full_graded_generator_count_eq :
    fullGradedGeneratorCount = 45 := by
  norm_num [fullGradedGeneratorCount]

/-- After freezing coordinates `0..3`, only coordinate `4` remains positive and
coordinates `5..9` remain negative. -/
def activePositiveCoordinates : ℕ := 1

def activeNegativeCoordinates : ℕ := 5

def activeCompactGeneratorCount : ℕ :=
  chooseTwo activePositiveCoordinates + chooseTwo activeNegativeCoordinates

def activeMixedBoostCount : ℕ :=
  activePositiveCoordinates * activeNegativeCoordinates

def activeGradedGeneratorCount : ℕ :=
  activeCompactGeneratorCount + activeMixedBoostCount

@[simp] theorem active_compact_generator_count_eq :
    activeCompactGeneratorCount = 10 := by
  simp [activeCompactGeneratorCount, activePositiveCoordinates,
    activeNegativeCoordinates]

@[simp] theorem active_mixed_boost_count_eq :
    activeMixedBoostCount = 5 := by
  norm_num [activeMixedBoostCount, activePositiveCoordinates,
    activeNegativeCoordinates]

@[simp] theorem active_graded_generator_count_eq :
    activeGradedGeneratorCount = 15 := by
  norm_num [activeGradedGeneratorCount]

end O55GradedGeneratorBasis
