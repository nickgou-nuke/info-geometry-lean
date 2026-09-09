import InfoGeometry.Canonical.KashiwaraCuntzCohomology

namespace InfoGeometry.Canonical.KashiwaraCuntzCohomology

/-!
# Cuntz Crystal Representation

This module formalizes the representation of the Cuntz algebra $O_2$ relations
on the space of finite binary Cantor/crystal words (`CrystalWord`).
-/

/-- Orthogonality of the left and right branches under raising (S_L^* S_R = 0). -/
theorem raiseLeft_lowerRight (w : CrystalWord) :
    raiseLeft (lowerRight w) = none := by
  rfl

/-- Orthogonality of the right and left branches under raising (S_R^* S_L = 0). -/
theorem raiseRight_lowerLeft (w : CrystalWord) :
    raiseRight (lowerLeft w) = none := by
  rfl

/-- The Cuntz range projection definition on Option. -/
def leftProjection (w : CrystalWord) : Option CrystalWord :=
  match raiseLeft w with
  | some w' => some (lowerLeft w')
  | none => none

/-- The Cuntz range projection definition on Option. -/
def rightProjection (w : CrystalWord) : Option CrystalWord :=
  match raiseRight w with
  | some w' => some (lowerRight w')
  | none => none

/-- The identity reconstruction (partition of unity S_L S_L^* + S_R S_R^* = 1)
    holds on all non-empty words. -/
theorem cuntz_projection_reconstruction (w : CrystalWord) (_ : w ≠ []) :
    leftProjection w = some w ∨ rightProjection w = some w := by
  cases w with
  | nil => contradiction
  | cons b w' =>
      cases b
      · left
        simp [leftProjection, raiseLeft, lowerLeft, lowerBranch]
      · right
        simp [rightProjection, raiseRight, lowerRight, lowerBranch]

/-- The projections are mutually exclusive (disjoint ranges). -/
theorem projections_disjoint (w : CrystalWord) :
    leftProjection w = none ∨ rightProjection w = none := by
  cases w with
  | nil =>
      left
      rfl
  | cons b w' =>
      cases b
      · right
        rfl
      · left
        rfl

end InfoGeometry.Canonical.KashiwaraCuntzCohomology
