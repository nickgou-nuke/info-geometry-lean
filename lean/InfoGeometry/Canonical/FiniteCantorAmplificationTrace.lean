/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Canonical.FiniteCantorBranchRefinement
import Mathlib.LinearAlgebra.Trace

/-!
# Faithful operator refinement and its trace

The existing rectangular word branches define the refinement. This file
packages that same map as a ring homomorphism, proves that it reflects
commutation, and computes its trace. These are successive finite-stage laws;
no same-stage Cuntz family or new colimit is asserted.
-/

noncomputable section
namespace InfoGeometry.Canonical.FiniteCantorCuntzBranches

def amplifyRingHom (n : ℕ) :
    Module.End ℝ (Stage n) →+* Module.End ℝ (Stage (n + 1)) where
  toFun := amplify n
  map_one' := amplify_one n
  map_mul' := amplify_mul n
  map_zero' := by simp [amplify]
  map_add' := amplify_add n

theorem amplify_commute_iff (n : ℕ) (T U : Module.End ℝ (Stage n)) :
    Commute (amplify n T) (amplify n U) ↔ Commute T U := by
  change amplify n T * amplify n U = amplify n U * amplify n T ↔ T * U = U * T
  rw [← amplify_mul, ← amplify_mul]
  exact (amplify_injective n).eq_iff

theorem trace_branch_sandwich (n : ℕ) (b : Bool) (T : Module.End ℝ (Stage n)) :
    LinearMap.trace ℝ (Stage (n + 1))
      ((branch n b).comp (T.comp (branchAdjoint n b))) =
      LinearMap.trace ℝ (Stage n) T := by
  rw [LinearMap.trace_comp_comm', LinearMap.comp_assoc, branchAdjoint_comp_branch,
    LinearMap.comp_id]

theorem trace_amplify (n : ℕ) (T : Module.End ℝ (Stage n)) :
    LinearMap.trace ℝ (Stage (n + 1)) (amplify n T) =
      2 * LinearMap.trace ℝ (Stage n) T := by
  rw [amplify, map_add, trace_branch_sandwich, trace_branch_sandwich, two_mul]

theorem normalized_trace_amplify (n : ℕ) (T : Module.End ℝ (Stage n)) :
    LinearMap.trace ℝ (Stage (n + 1)) (amplify n T) / (2 : ℝ)^(n + 1) =
      LinearMap.trace ℝ (Stage n) T / (2 : ℝ)^n := by
  rw [trace_amplify, pow_succ]
  field_simp

end InfoGeometry.Canonical.FiniteCantorCuntzBranches
