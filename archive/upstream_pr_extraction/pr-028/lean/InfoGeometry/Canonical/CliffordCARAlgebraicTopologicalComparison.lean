import InfoGeometry.Canonical.CliffordCARTopologicalColimit
import InfoGeometry.Clifford.Cl11TensorTowerLimit
import InfoGeometry.Algebra.DirectLimitSuperClosureLemmas

/-!
# Algebraic-to-topological comparison for the Clifford/CAR tower

The algebraic direct limit and the `TopCat` colimit are deliberately kept as
different constructions.  This file only supplies the canonical representative
map from the former to the latter and records its finite-stage readback.  No
continuity statement is made: the algebraic direct limit has not been endowed
with a topology here.
-/

noncomputable section

namespace InfoGeometry.Canonical.CliffordCARAlgebraicTopologicalComparison

open CategoryTheory CategoryTheory.Limits
open InfoGeometry.Clifford.Cl11TensorTower
open InfoGeometry.Clifford.Cl11TensorTowerLimit
open InfoGeometry.Algebra.DirectLimitSuperClosureLemmas
open InfoGeometry.Canonical.CliffordCARTopologicalColimit

abbrev AStage (n : ℕ) : Type := InfoGeometry.Clifford.Cl11TensorTowerLimit.Stage n
abbrev AlgebraicLimit : Type := InfoGeometry.Clifford.Cl11TensorTowerLimit.Limit

/-- The iterated algebraic bond agrees pointwise with the TopCat tower bond. -/
theorem bondAlgHom_eq_bondMap
    (m n : ℕ) (h : m ≤ n) (A : AStage m) :
    bondAlgHom m n h A = bondMap stageBond m n h A := by
  refine Nat.le_induction
    (m := m)
    (P := fun t ht => bondAlgHom m t ht A = bondMap stageBond m t ht A)
    ?base ?succ n h
  · simpa [bondAlgHom_refl, bondMap_refl]
  · intro t hmt ih
    rw [bondAlgHom_succ m t hmt]
    rw [bondMap_succ stageBond m t hmt]
    simp [ih, stageBond]

/-- Canonical map sending an algebraic direct-limit representative to the
corresponding point of the topological colimit. -/
noncomputable def algebraicToTopological :
    AlgebraicLimit → topologicalColimit :=
  DirectLimit.lift
    (f := fun m n h => bondMap stageBond m n h)
    (fun n (A : AStage n) => topologicalInjection n A)
    (by
      intro m n h A
      have hmap := bondAlgHom_eq_bondMap m n h A
      rw [← hmap]
      exact (topologicalInjection_transition h A).symm)

@[simp] theorem algebraicToTopological_ofStage (n : ℕ) (A : AStage n) :
    algebraicToTopological (ofStage n A) = topologicalInjection n A := by
  rfl

@[simp] theorem algebraicToTopological_ofStage_transition
    (n : ℕ) (A : AStage n) :
    algebraicToTopological (ofStage (n + 1) (stageEmbed n A)) =
      algebraicToTopological (ofStage n A) := by
  change algebraicToTopological
      (directLimitOf stageBond (n + 1) (stageBond n A)) =
    algebraicToTopological (directLimitOf stageBond n A)
  rw [directLimitOf_bond]

end InfoGeometry.Canonical.CliffordCARAlgebraicTopologicalComparison
