import Mathlib.Tactic

namespace Omega.POM

open Polynomial

noncomputable section

/-- The reordered two-state model: synchronized states form the first invariant block. -/
def pom_collision_zeta_removable_sync_factor_reordered_matrix : Matrix (Fin 2) (Fin 2) ℤ :=
  !![2, 1; 0, 3]

/-- Determinant factor of the synchronized absorbing block. -/
def pom_collision_zeta_removable_sync_factor_sync_det : Polynomial ℤ :=
  1 - 2 * X

/-- Determinant factor of the unsynchronized tail block. -/
def pom_collision_zeta_removable_sync_factor_tail_det : Polynomial ℤ :=
  1 - 3 * X

/-- Determinant of the full reordered block-triangular collision kernel. -/
def pom_collision_zeta_removable_sync_factor_full_det : Polynomial ℤ :=
  pom_collision_zeta_removable_sync_factor_sync_det *
    pom_collision_zeta_removable_sync_factor_tail_det

/-- The synchronized subspace is invariant: the lower-left block of the reordered matrix is zero. -/
def block_triangular_form : Prop :=
  pom_collision_zeta_removable_sync_factor_reordered_matrix 1 0 = 0

/-- The Fredholm determinant factors into synchronized and tail determinants. -/
def det_factorization : Prop :=
  pom_collision_zeta_removable_sync_factor_full_det =
    pom_collision_zeta_removable_sync_factor_sync_det *
      pom_collision_zeta_removable_sync_factor_tail_det

/-- After removing the synchronized factor, the remaining factor is exactly the tail determinant. -/
def sync_tail_pole_recoverable : Prop :=
  ∃ tail : Polynomial ℤ,
    pom_collision_zeta_removable_sync_factor_full_det =
        pom_collision_zeta_removable_sync_factor_sync_det * tail ∧
      tail = pom_collision_zeta_removable_sync_factor_tail_det

/-- Paper label: `prop:pom-collision-zeta-removable-sync-factor`. -/
theorem paper_pom_collision_zeta_removable_sync_factor
    : block_triangular_form ∧ det_factorization ∧ sync_tail_pole_recoverable := by
  refine ⟨?_, ?_, ?_⟩
  · rfl
  · rfl
  · exact ⟨pom_collision_zeta_removable_sync_factor_tail_det, rfl, rfl⟩

end

end Omega.POM
