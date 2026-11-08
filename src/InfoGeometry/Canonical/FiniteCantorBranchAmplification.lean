/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/

import InfoGeometry.Canonical.FiniteCantorCuntzBranches

/-!
# Operator refinement through rectangular branches

The two finite branches act between successive stages. They induce a faithful
unital refinement of endomorphisms by applying the same operator to each
branch. This is a finite-stage construction on the existing word tower.
-/

noncomputable section

namespace InfoGeometry.Canonical.FiniteCantorCuntzBranches

open InfoGeometry.Canonical.UHFInductiveColimitBoundary

/-- Apply an endomorphism independently to both last-bit branches. -/
def amplify (n : ℕ) (T : Module.End ℝ (Stage n)) :
    Module.End ℝ (Stage (n + 1)) :=
  (branch n false).comp (T.comp (branchAdjoint n false)) +
    (branch n true).comp (T.comp (branchAdjoint n true))

theorem amplify_apply (n : ℕ) (T : Module.End ℝ (Stage n))
    (f : Stage (n + 1)) (w : InfoGeometry.Canonical.UHFInductiveColimitBoundary.BitWord (n + 1)) :
    amplify n T f w = T (branchAdjoint n (lastBit n w) f) (prefixSucc n w) := by
  cases h : lastBit n w <;> simp [amplify, branch_apply, h]

/-- Restriction to either branch recovers the original operator action. -/
theorem branchAdjoint_amplify (n : ℕ) (b : Bool)
    (T : Module.End ℝ (Stage n)) (f : Stage (n + 1)) :
    branchAdjoint n b (amplify n T f) = T (branchAdjoint n b f) := by
  ext w
  simp only [branchAdjoint_apply, amplify_apply, lastBit_extendSucc,
    InfoGeometry.Canonical.UHFInductiveColimitBoundary.prefixSucc_extendSucc]

theorem amplify_one (n : ℕ) : amplify n 1 = 1 := by
  simpa [amplify, Module.End.one_eq_id] using branch_range_partition n

theorem amplify_mul (n : ℕ) (T U : Module.End ℝ (Stage n)) :
    amplify n (T * U) = amplify n T * amplify n U := by
  apply LinearMap.ext
  intro f
  ext w
  simp only [Module.End.mul_apply, amplify_apply, branchAdjoint_amplify]

theorem amplify_add (n : ℕ) (T U : Module.End ℝ (Stage n)) :
    amplify n (T + U) = amplify n T + amplify n U := by
  apply LinearMap.ext
  intro f
  ext w
  simp [amplify_apply]

theorem amplify_injective (n : ℕ) : Function.Injective (amplify n) := by
  intro T U h
  apply LinearMap.ext
  intro f
  have h' := congrArg (fun V : Module.End ℝ (Stage (n + 1)) =>
    branchAdjoint n false (V (diagonalEmbed n f))) h
  simpa only [branchAdjoint_amplify, branchAdjoint_diagonalEmbed] using h'

/-- Refinement respects the existing diagonal bonding map on vectors. -/
theorem amplify_diagonalEmbed (n : ℕ) (T : Module.End ℝ (Stage n)) (f : Stage n) :
    amplify n T (diagonalEmbed n f) = diagonalEmbed n (T f) := by
  ext w
  rw [amplify_apply, branchAdjoint_diagonalEmbed, diagonalEmbed_apply]

end InfoGeometry.Canonical.FiniteCantorCuntzBranches
