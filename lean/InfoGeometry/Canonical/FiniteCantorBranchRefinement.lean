/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Canonical.FiniteCantorBranchAmplification

/-! Exact uniqueness of finite operator refinement through the existing
rectangular branches. No finite square-matrix Cuntz family is postulated. -/

noncomputable section
namespace InfoGeometry.Canonical.FiniteCantorCuntzBranches

/-- The two branches reconstruct every vector at the successor stage. -/
theorem branch_reconstruct (n : ℕ) (f : Stage (n + 1)) :
    branch n false (branchAdjoint n false f) +
      branch n true (branchAdjoint n true f) = f :=
  LinearMap.congr_fun (branch_range_partition n) f

/-- An operator is determined by its restrictions to the two branch ranges. -/
theorem end_eq_of_comp_branch (n : ℕ)
    {V W : Module.End ℝ (Stage (n + 1))}
    (h : ∀ b : Bool, V.comp (branch n b) = W.comp (branch n b)) : V = W := by
  apply LinearMap.ext
  intro f
  calc
    V f = V (branch n false (branchAdjoint n false f) +
        branch n true (branchAdjoint n true f)) := congrArg V (branch_reconstruct n f).symm
    _ = W (branch n false (branchAdjoint n false f) +
        branch n true (branchAdjoint n true f)) := by
      rw [map_add, map_add]
      exact congrArg₂ (· + ·)
        (LinearMap.congr_fun (h false) (branchAdjoint n false f))
        (LinearMap.congr_fun (h true) (branchAdjoint n true f))
    _ = W f := congrArg W (branch_reconstruct n f)

/-- Amplification acts on each branch by the original operator. -/
theorem amplify_comp_branch (n : ℕ) (T : Module.End ℝ (Stage n)) (b : Bool) :
    (amplify n T).comp (branch n b) = (branch n b).comp T := by
  cases b <;>
    simp only [amplify, LinearMap.add_comp, LinearMap.comp_assoc,
      branchAdjoint_comp_branch, branchAdjoint_false_comp_branch_true,
      branchAdjoint_true_comp_branch_false, LinearMap.comp_id,
      LinearMap.comp_zero, add_zero, zero_add]

/-- Exact finite-stage replacement: the amplified operator is uniquely
characterized by simultaneous intertwining of both rectangular branches. -/
theorem eq_amplify_iff (n : ℕ) (V : Module.End ℝ (Stage (n + 1)))
    (T : Module.End ℝ (Stage n)) :
    V = amplify n T ↔ ∀ b : Bool, V.comp (branch n b) = (branch n b).comp T := by
  constructor
  · rintro rfl b
    exact amplify_comp_branch n T b
  · intro h
    apply end_eq_of_comp_branch n
    intro b
    rw [h b, amplify_comp_branch]

/-- Every smaller-stage operator has exactly one refinement with these branch actions. -/
theorem existsUnique_branch_refinement (n : ℕ) (T : Module.End ℝ (Stage n)) :
    ∃! V : Module.End ℝ (Stage (n + 1)),
      ∀ b : Bool, V.comp (branch n b) = (branch n b).comp T := by
  exact ⟨amplify n T, amplify_comp_branch n T,
    fun V h => (eq_amplify_iff n V T).mpr h⟩

end InfoGeometry.Canonical.FiniteCantorCuntzBranches
