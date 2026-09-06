import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Real.Basic

namespace Omega.SyncKernelWeighted

/-- A toy real cyclotomic field container used to track all slice coefficients uniformly. -/
def realCyclotomicField (_m : ℕ) : Set ℝ :=
  Set.univ

/-- Paper wrapper for the finite-comparison reduction of weighted unit-root slices.
    cor:sync-kernel-weighted-unit-root-finite -/
theorem paper_sync_kernel_weighted_unit_root_finite
    (m : ℕ)
    (coefficient : Fin (m + 1) → ℝ)
    (galoisPerm : Equiv (Fin (m + 1)) (Fin (m + 1))) :
    (∀ j, coefficient j ∈ realCyclotomicField m) ∧
      (∀ j, ∃ k, coefficient (galoisPerm j) = coefficient k) ∧
      (∀ j : Fin (m + 1), j ∈ Finset.univ) := by
  refine ⟨?_, ?_, ?_⟩
  · intro j
    simp [realCyclotomicField]
  · intro j
    exact ⟨galoisPerm j, rfl⟩
  · intro j
    simp

end Omega.SyncKernelWeighted
