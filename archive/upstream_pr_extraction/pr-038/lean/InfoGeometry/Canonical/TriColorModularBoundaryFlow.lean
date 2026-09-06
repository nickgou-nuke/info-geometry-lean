import Mathlib
import InfoGeometry.Canonical.LocalZornProjectiveAction

namespace InfoGeometry.Canonical

open InfoGeometry.Algebra

/-- The three color directions. -/
def redDir : ZornVec3 ℝ := ZornVec3.basis 0
def greenDir : ZornVec3 ℝ := ZornVec3.basis 1
def blueDir : ZornVec3 ℝ := ZornVec3.basis 2

theorem redDir_norm : ZornVec3.dot redDir redDir = 1 := localZorn_basis_direction_norm 0
theorem greenDir_norm : ZornVec3.dot greenDir greenDir = 1 := localZorn_basis_direction_norm 1
theorem blueDir_norm : ZornVec3.dot blueDir blueDir = 1 := localZorn_basis_direction_norm 2

/-- The parameter slice for the modular boost. -/
noncomputable def modularBoostSlice (e : ZornVec3 ℝ) (s : ℝ) : ZornVectorMatrix ℝ :=
  localZornSlice e (Real.exp s) (Real.exp (-s)) 0 0

theorem modularBoostSlice_norm (e : ZornVec3 ℝ) (he : ZornVec3.dot e e = 1) (s : ℝ) :
    ZornVectorMatrix.norm (modularBoostSlice e s) = 1 := by
  unfold modularBoostSlice
  rw [localZornSlice_norm_eq_det e he]
  simp [modularBoostSlice, localZornMatrix, Matrix.det_fin_two, Real.exp_neg]

/-- The projective boundary flows for each color sector. -/
noncomputable def redBoundaryFlow (s : ℝ) : RealProjectiveBoundary → RealProjectiveBoundary :=
  localZornSliceProjectiveAction redDir redDir_norm
    (Real.exp s) (Real.exp (-s)) 0 0
    (modularBoostSlice_norm redDir redDir_norm s)

noncomputable def greenBoundaryFlow (s : ℝ) : RealProjectiveBoundary → RealProjectiveBoundary :=
  localZornSliceProjectiveAction greenDir greenDir_norm
    (Real.exp s) (Real.exp (-s)) 0 0
    (modularBoostSlice_norm greenDir greenDir_norm s)

noncomputable def blueBoundaryFlow (s : ℝ) : RealProjectiveBoundary → RealProjectiveBoundary :=
  localZornSliceProjectiveAction blueDir blueDir_norm
    (Real.exp s) (Real.exp (-s)) 0 0
    (modularBoostSlice_norm blueDir blueDir_norm s)

theorem red_modularBoundaryFlow_eq_common (s : ℝ) :
    redBoundaryFlow s = modularBoostProjectiveAction s := by
  unfold redBoundaryFlow
  funext p
  rw [localZornSlice_projectiveAction_is_native]
  rfl

theorem green_modularBoundaryFlow_eq_common (s : ℝ) :
    greenBoundaryFlow s = modularBoostProjectiveAction s := by
  unfold greenBoundaryFlow
  funext p
  rw [localZornSlice_projectiveAction_is_native]
  rfl

theorem blue_modularBoundaryFlow_eq_common (s : ℝ) :
    blueBoundaryFlow s = modularBoostProjectiveAction s := by
  unfold blueBoundaryFlow
  funext p
  rw [localZornSlice_projectiveAction_is_native]
  rfl

/-- Apex Theorem: TriColor Boundary Flow Equality -/
theorem triColor_modularBoundaryFlow_eq (s : ℝ) :
    redBoundaryFlow s = greenBoundaryFlow s ∧
    greenBoundaryFlow s = blueBoundaryFlow s := by
  constructor
  · rw [red_modularBoundaryFlow_eq_common, green_modularBoundaryFlow_eq_common]
  · rw [green_modularBoundaryFlow_eq_common, blue_modularBoundaryFlow_eq_common]

end InfoGeometry.Canonical
