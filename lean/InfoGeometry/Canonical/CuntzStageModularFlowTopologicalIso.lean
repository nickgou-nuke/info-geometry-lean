import InfoGeometry.Canonical.CuntzStageModularFlowTopologicalColimit
import InfoGeometry.Algebra.FiniteSpinAlgebra

/-!
# TopCat isomorphism for the generic descended Cuntz modular flow

The generic stagewise flow already descends to a continuous map on the
topological colimit and proves its inverse and additive-time laws.  This file
packages those maps as a native `TopCat` isomorphism family.
-/

noncomputable section

namespace InfoGeometry.Canonical.CuntzStageModularFlowTopologicalIso

open CategoryTheory
open InfoGeometry.Canonical.CuntzStarInductiveSystem
open InfoGeometry.Canonical.CuntzStageModularFlow
open InfoGeometry.Canonical.CuntzStageModularFlowTopologicalColimit
open InfoGeometry.Canonical.FilteredStarAlgebraTopologicalColimit

variable (Stage : ℕ → Type)
variable [∀ n, CStarAlgebra (Stage n)]
variable [∀ n, PartialOrder (Stage n)]
variable [∀ n, StarOrderedRing (Stage n)]
variable (T : CuntzStarTower Stage)
variable (Φ : CuntzStageModularFlowData Stage T)

def modularFlowTopologicalColimitIso (t : ℝ) :
    topologicalColimit Stage (system Stage T) ≅
      topologicalColimit Stage (system Stage T) where
  hom := modularFlowTopologicalColimitMap Stage T Φ t
  inv := modularFlowTopologicalColimitMap Stage T Φ (-t)
  hom_inv_id := modularFlowTopologicalColimitMap_right_inverse Stage T Φ t
  inv_hom_id := modularFlowTopologicalColimitMap_left_inverse Stage T Φ t

@[simp] theorem modularFlowTopologicalColimitIso_hom_apply
    (t : ℝ) (x : topologicalColimit Stage (system Stage T)) :
    (modularFlowTopologicalColimitIso Stage T Φ t).hom x =
      modularFlowTopologicalColimitMap Stage T Φ t x :=
  rfl

@[simp] theorem modularFlowTopologicalColimitIso_inv_apply
    (t : ℝ) (x : topologicalColimit Stage (system Stage T)) :
    (modularFlowTopologicalColimitIso Stage T Φ t).inv x =
      modularFlowTopologicalColimitMap Stage T Φ (-t) x :=
  rfl

@[simp] theorem modularFlowTopologicalColimitIso_hom_stage
    (t : ℝ) (n : ℕ) (a : Stage n) :
    (modularFlowTopologicalColimitIso Stage T Φ t).hom
        (topologicalInjection Stage (system Stage T) n a) =
      topologicalInjection Stage (system Stage T) n (Φ.flow n t a) := by
  exact modularFlowTopologicalColimitMap_inclusion Stage T Φ t n a

theorem modularFlowTopologicalColimitIso_zero :
    modularFlowTopologicalColimitIso Stage T Φ 0 =
      Iso.refl (topologicalColimit Stage (system Stage T)) := by
  apply CategoryTheory.Iso.ext
  exact modularFlowTopologicalColimitMap_zero Stage T Φ

theorem modularFlowTopologicalColimitIso_add (t s : ℝ) :
    modularFlowTopologicalColimitIso Stage T Φ (t + s) =
      modularFlowTopologicalColimitIso Stage T Φ s ≪≫
        modularFlowTopologicalColimitIso Stage T Φ t := by
  apply CategoryTheory.Iso.ext
  exact modularFlowTopologicalColimitMap_add Stage T Φ t s

end InfoGeometry.Canonical.CuntzStageModularFlowTopologicalIso
