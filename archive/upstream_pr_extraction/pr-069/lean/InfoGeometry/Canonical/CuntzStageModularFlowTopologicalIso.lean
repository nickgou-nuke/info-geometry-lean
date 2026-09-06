import InfoGeometry.Canonical.CuntzStageModularFlowTopologicalColimit

/-!
# TopCat isomorphism for the generic descended Cuntz modular flow

The generic stagewise flow descends to a continuous map on the topological
colimit.  The group and transition laws are supplied explicitly at each
construction site rather than stored as unverified data fields.
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
variable (Φ : CuntzStageModularFlowData Stage)

variable (hflow_add :
  ∀ (n : ℕ) (t s : ℝ) (a : Stage n),
    Φ.flow n (t + s) a = Φ.flow n t (Φ.flow n s a))
variable (hmap_naturality :
  ∀ {m n : ℕ} (hmn : m ≤ n) (t : ℝ) (a : Stage m),
    T.map hmn (Φ.flow m t a) = Φ.flow n t (T.map hmn a))

def modularFlowTopologicalColimitIso (t : ℝ) :
    topologicalColimit Stage (system Stage T) ≅
      topologicalColimit Stage (system Stage T) where
  hom := modularFlowTopologicalColimitMap Stage T Φ hmap_naturality t
  inv := modularFlowTopologicalColimitMap Stage T Φ hmap_naturality (-t)
  hom_inv_id := modularFlowTopologicalColimitMap_right_inverse
    Stage T Φ hflow_add hmap_naturality t
  inv_hom_id := modularFlowTopologicalColimitMap_left_inverse
    Stage T Φ hflow_add hmap_naturality t

@[simp] theorem modularFlowTopologicalColimitIso_hom_apply
    (t : ℝ) (x : topologicalColimit Stage (system Stage T)) :
    (modularFlowTopologicalColimitIso Stage T Φ hflow_add hmap_naturality t).hom x =
      modularFlowTopologicalColimitMap Stage T Φ hmap_naturality t x :=
  rfl

@[simp] theorem modularFlowTopologicalColimitIso_inv_apply
    (t : ℝ) (x : topologicalColimit Stage (system Stage T)) :
    (modularFlowTopologicalColimitIso Stage T Φ hflow_add hmap_naturality t).inv x =
      modularFlowTopologicalColimitMap Stage T Φ hmap_naturality (-t) x :=
  rfl

@[simp] theorem modularFlowTopologicalColimitIso_hom_stage
    (t : ℝ) (n : ℕ) (a : Stage n) :
    (modularFlowTopologicalColimitIso Stage T Φ hflow_add hmap_naturality t).hom
        (topologicalInjection Stage (system Stage T) n a) =
      topologicalInjection Stage (system Stage T) n (Φ.flow n t a) := by
  exact modularFlowTopologicalColimitMap_inclusion
    Stage T Φ hmap_naturality t n a

theorem modularFlowTopologicalColimitIso_zero :
    modularFlowTopologicalColimitIso Stage T Φ hflow_add hmap_naturality 0 =
      Iso.refl (topologicalColimit Stage (system Stage T)) := by
  apply CategoryTheory.Iso.ext
  exact modularFlowTopologicalColimitMap_zero
    Stage T Φ hflow_add hmap_naturality

theorem modularFlowTopologicalColimitIso_add (t s : ℝ) :
    modularFlowTopologicalColimitIso Stage T Φ hflow_add hmap_naturality (t + s) =
      modularFlowTopologicalColimitIso Stage T Φ hflow_add hmap_naturality s ≪≫
        modularFlowTopologicalColimitIso Stage T Φ hflow_add hmap_naturality t := by
  apply CategoryTheory.Iso.ext
  exact modularFlowTopologicalColimitMap_add
    Stage T Φ hflow_add hmap_naturality t s

end InfoGeometry.Canonical.CuntzStageModularFlowTopologicalIso
