import Mathlib.Tactic

/-!
# Wallpaper-group mechanical metamaterial dataset digest

Formal digest of Hendriks et al., arXiv:2507.11195,
"Wallpaper Group-Based Mechanical Metamaterials: Dataset Including Mechanical
Responses".

The paper contributes a dataset of 2D porous mechanical metamaterials generated
from all 17 wallpaper groups using connected periodic graph skeletons and smooth
Bézier boundaries, then simulated by finite-strain computational homogenization.
This file records the dataset arithmetic and the symmetry hooks needed by the
paperwall/Klein/glide formalization.
-/

namespace WallpaperMetamaterialDataset

/-! ## 1. Wallpaper group coverage -/

/-- Standard IUCr short names for the 17 wallpaper groups, as used by the dataset. -/
def wallpaperGroups : List String :=
  ["p1", "p2", "pm", "pg", "cm", "pmm", "pmg", "pgg", "cmm",
   "p4", "p4m", "p4g", "p3", "p3m1", "p31m", "p6", "p6m"]

/-- Dataset covers all 17 wallpaper groups. -/
theorem wallpaperGroups_length : wallpaperGroups.length = 17 := by
  simp [wallpaperGroups]

/-- Groups explicitly containing glide reflections in IUCr notation. -/
def glideGroups : List String := ["pg", "pmg", "pgg", "p4g"]

/-- There are four explicit glide-containing names in this list. -/
theorem glideGroups_length : glideGroups.length = 4 := by
  simp [glideGroups]

/-! ## 2. Dataset cardinalities -/

/-- Number of distinct geometries per wallpaper group. -/
def geometriesPerGroup : ℕ := 60

/-- Number of loading trajectories per geometry. -/
def trajectoriesPerGeometry : ℕ := 12

/-- Number of groups represented. -/
def numberWallpaperGroups : ℕ := wallpaperGroups.length

/-- Total geometry count. -/
def totalGeometries : ℕ := numberWallpaperGroups * geometriesPerGroup

/-- Total trajectory count. -/
def totalTrajectories : ℕ := totalGeometries * trajectoriesPerGeometry

/-- `17 × 60 = 1020` geometries. -/
theorem totalGeometries_eq_1020 : totalGeometries = 1020 := by
  unfold totalGeometries numberWallpaperGroups geometriesPerGroup
  rw [wallpaperGroups_length]

/-- `1020 × 12 = 12240` trajectories. -/
theorem totalTrajectories_eq_12240 : totalTrajectories = 12240 := by
  unfold totalTrajectories trajectoriesPerGeometry
  rw [totalGeometries_eq_1020]

/-- Reported failed/nonconvergent trajectories. -/
def failedTrajectories : ℕ := 42

/-- Failed trajectories are a strict minority. -/
theorem failedTrajectories_lt_total : failedTrajectories < totalTrajectories := by
  rw [totalTrajectories_eq_12240]
  unfold failedTrajectories
  norm_num

/-- Reported total microstructural responses across pseudo-time steps. -/
def reportedResponses : ℕ := 135947

/-- The average pseudo-time-step statement is represented as `12240 * 111 / 10 ≈ 135947`. -/
def roundedAverageStepNumerator : ℕ := totalTrajectories * 111

/-- The reported response count is within one percent of using average `11.1` steps. -/
theorem reportedResponses_within_one_percent :
    100 * Int.natAbs ((reportedResponses : ℤ) * 10 - (roundedAverageStepNumerator : ℤ))
      < (roundedAverageStepNumerator : ℕ) := by
  unfold reportedResponses roundedAverageStepNumerator
  rw [totalTrajectories_eq_12240]
  norm_num

/-! ## 3. Simulation tensor shapes -/

/-- Shape tags for arrays in one `.pkl` record. -/
inductive ArrayQuantity where
  | F       -- deformation gradient, shape `(steps,2,2)`
  | P       -- first Piola-Kirchhoff stress, shape `(steps,2,2)`
  | D       -- tangent stiffness, shape `(steps,2,2,2,2)`
  | Dref    -- reference tangent stiffness, shape `(2,2,2,2)`
  | x       -- deformed nodal coordinates, shape `(steps,nodes,2)`
  | p       -- reference nodal coordinates, shape `(nodes,2)`
  | tri6    -- quadratic triangular elements, shape `(elements,6)`
  deriving DecidableEq, Repr

/-- The tensor rank of each array quantity, abstracting away variable dimensions. -/
def tensorRank : ArrayQuantity → ℕ
  | .F => 3
  | .P => 3
  | .D => 5
  | .Dref => 4
  | .x => 3
  | .p => 2
  | .tri6 => 2

/-- Mechanical tensors `F` and `P` have the same rank/2D matrix shape. -/
theorem F_P_same_rank : tensorRank .F = tensorRank .P := rfl

/-- Tangent stiffness has higher rank than stress/deformation-gradient records. -/
theorem D_rank_gt_F : tensorRank .F < tensorRank .D := by
  norm_num [tensorRank]

end WallpaperMetamaterialDataset
