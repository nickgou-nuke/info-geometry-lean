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

@[simp] theorem leftProjection_cons_false (w : CrystalWord) :
    leftProjection (false :: w) = some (false :: w) := by
  simp [leftProjection, raiseLeft, raiseBranch]

@[simp] theorem leftProjection_cons_true (w : CrystalWord) :
    leftProjection (true :: w) = none := by
  simp [leftProjection, raiseLeft, raiseBranch]

@[simp] theorem rightProjection_cons_false (w : CrystalWord) :
    rightProjection (false :: w) = none := by
  simp [rightProjection, raiseRight, raiseBranch]

@[simp] theorem rightProjection_cons_true (w : CrystalWord) :
    rightProjection (true :: w) = some (true :: w) := by
  simp [rightProjection, raiseRight, raiseBranch]

theorem leftProjection_eq_some_iff (w : CrystalWord) :
    leftProjection w = some w ↔ ∃ u, w = false :: u := by
  cases w with
  | nil => simp [leftProjection, raiseLeft, raiseBranch]
  | cons b w =>
      cases b <;> simp

theorem rightProjection_eq_some_iff (w : CrystalWord) :
    rightProjection w = some w ↔ ∃ u, w = true :: u := by
  cases w with
  | nil => simp [rightProjection, raiseRight, raiseBranch]
  | cons b w =>
      cases b <;> simp

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

/-- Exact reconstruction criterion for the two finite branch projections. -/
theorem cuntz_projection_reconstruction_iff (w : CrystalWord) :
    (leftProjection w = some w ∨ rightProjection w = some w) ↔ w ≠ [] := by
  constructor
  · intro h
    cases w with
    | nil =>
        simp [leftProjection, rightProjection, raiseLeft, raiseRight] at h
    | cons b w' =>
        simp
  · exact cuntz_projection_reconstruction w

/-- The two branch projections cannot both reconstruct the same word. -/
theorem cuntz_projection_exclusive (w : CrystalWord) :
    ¬ (leftProjection w = some w ∧ rightProjection w = some w) := by
  cases w with
  | nil =>
      simp [leftProjection, rightProjection, raiseLeft, raiseRight,
        raiseBranch]
  | cons b w' =>
      cases b <;>
      simp [leftProjection, rightProjection, raiseLeft, raiseRight,
        raiseBranch]

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
