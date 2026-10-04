import Mathlib.LinearAlgebra.Dimension.Finrank
import Mathlib.Data.Real.Basic
import Mathlib.Tactic

/-!
# Coordinate projection from a 27-dimensional carrier to six coordinates

`AlbertSpace` is used here only as the vector-space carrier
`ℝ³ × (ℝ⁸)³`; this file does not define octonion multiplication or the Albert
Jordan product. `associativeCollapseMap` keeps three scalar coordinates and
the first coordinate in each of three eight-coordinate blocks. Its kernel is
therefore 21-dimensional. The result is linear algebra, not a statement about
associativity, norms, or a Grassmannian map.
-/

namespace InfoGeometry.Canonical

open Module

/-- The eight real coordinates of one octonion carrier. -/
abbrev OctonionSpace := ℝ × ℝ × ℝ × ℝ × ℝ × ℝ × ℝ × ℝ

/-- The 27-dimensional real vector-space carrier `ℝ³ × (ℝ⁸)³`. -/
abbrev AlbertSpace := ℝ × ℝ × ℝ × OctonionSpace × OctonionSpace × OctonionSpace

/-- Six real coordinates, arranged as a six-dimensional target space. -/
abbrev RealSymmetricSpace := ℝ × ℝ × ℝ × ℝ × ℝ × ℝ

/-- Keep the three scalar coordinates and one coordinate from each 8-block. -/
def associativeCollapseMap : AlbertSpace →ₗ[ℝ] RealSymmetricSpace where
  toFun := fun X =>
    (X.1,
      X.2.1,
      X.2.2.1,
      X.2.2.2.1.1,
      X.2.2.2.2.1.1,
      X.2.2.2.2.2.1)
  map_add' := by
    intro X Y
    ext <;> simp
  map_smul' := by
    intro c X
    ext <;> simp

/-- Insert six coordinates into the selected scalar slots of the 27-carrier. -/
def associativeCollapseSection : RealSymmetricSpace →ₗ[ℝ] AlbertSpace where
  toFun := fun y =>
    (y.1,
      y.2.1,
      y.2.2.1,
      (y.2.2.2.1, 0, 0, 0, 0, 0, 0, 0),
      (y.2.2.2.2.1, 0, 0, 0, 0, 0, 0, 0),
      (y.2.2.2.2.2, 0, 0, 0, 0, 0, 0, 0))
  map_add' := by
    intro x y
    ext <;> simp
  map_smul' := by
    intro c x
    ext <;> simp

theorem finrank_octonion_eq_eight : finrank ℝ OctonionSpace = 8 := by
  simp [finrank_prod]

theorem finrank_albert_eq_27 : finrank ℝ AlbertSpace = 27 := by
  simp [finrank_prod, finrank_octonion_eq_eight]

theorem finrank_symmetric_eq_6 : finrank ℝ RealSymmetricSpace = 6 := by
  simp [finrank_prod]

/-- The displayed coordinate insertion is a right inverse to the projection. -/
@[simp]
theorem associativeCollapseMap_comp_section (y : RealSymmetricSpace) :
    associativeCollapseMap (associativeCollapseSection y) = y := by
  rfl

theorem associativeCollapseMap_surjective :
    Function.Surjective associativeCollapseMap := by
  intro y
  exact ⟨associativeCollapseSection y, associativeCollapseMap_comp_section y⟩

theorem associativeCollapseMap_range_eq_top :
    LinearMap.range associativeCollapseMap = ⊤ :=
  LinearMap.range_eq_top.mpr associativeCollapseMap_surjective

/-- Rank-nullity computes the kernel dimension of this coordinate projection. -/
theorem associativeCollapseMap_ker_finrank :
    finrank ℝ (LinearMap.ker associativeCollapseMap) = 21 := by
  have hRange : finrank ℝ (LinearMap.range associativeCollapseMap) = 6 := by
    rw [associativeCollapseMap_range_eq_top, finrank_top, finrank_symmetric_eq_6]
  have hRankNullity := LinearMap.finrank_range_add_finrank_ker associativeCollapseMap
  rw [hRange, finrank_albert_eq_27] at hRankNullity
  omega

end InfoGeometry.Canonical
