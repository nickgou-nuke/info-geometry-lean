import InfoGeometry.Canonical.FixedIndexCuntzModularFlowTopologicalColimit

/-!
# TopCat isomorphism carried by the descended fixed-index modular flow
-/

noncomputable section

namespace InfoGeometry.Canonical.FixedIndexCuntzModularFlowTopologicalIso

open CategoryTheory CategoryTheory.Limits
open InfoGeometry.Canonical.FixedIndexCuntzModularFlowColimit
open InfoGeometry.Canonical.FixedIndexCuntzModularFlowTopologicalColimit
open InfoGeometry.Canonical.FixedIndexCuntzStarTower
open InfoGeometry.Canonical.FilteredStarAlgebraTopologicalColimit
open FilteredColimit.Native.Topological

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable (Stage : ℕ → Type)
variable [∀ n, CStarAlgebra (Stage n)]
variable [∀ n, PartialOrder (Stage n)]
variable [∀ n, StarOrderedRing (Stage n)]
variable (T : FixedIndexCuntzStarTower.Data (ι := ι) Stage)
variable (Φ : FlowData Stage)
variable (hflow_add :
  ∀ (n : ℕ) (t s : ℝ) (a : Stage n),
    Φ.flow n (t + s) a = Φ.flow n t (Φ.flow n s a))
variable (hmap_naturality :
  ∀ {m n : ℕ} (hmn : m ≤ n) (t : ℝ) (a : Stage m),
    T.map hmn (Φ.flow m t a) = Φ.flow n t (T.map hmn a))

def flowTopologicalColimitIso (t : ℝ) :
    topologicalColimit Stage (system Stage T) ≅
      topologicalColimit Stage (system Stage T) where
  hom := flowTopologicalColimitMap Stage T Φ hmap_naturality t
  inv := flowTopologicalColimitMap Stage T Φ hmap_naturality (-t)
  hom_inv_id := flowTopologicalColimitMap_right_inverse
    Stage T Φ hflow_add hmap_naturality t
  inv_hom_id := flowTopologicalColimitMap_left_inverse
    Stage T Φ hflow_add hmap_naturality t

@[simp] theorem flowTopologicalColimitIso_hom_apply
    (t : ℝ) (x : topologicalColimit Stage (system Stage T)) :
    (flowTopologicalColimitIso Stage T Φ hflow_add hmap_naturality t).hom x =
      flowTopologicalColimitMap Stage T Φ hmap_naturality t x :=
  rfl

@[simp] theorem flowTopologicalColimitIso_inv_apply
    (t : ℝ) (x : topologicalColimit Stage (system Stage T)) :
    (flowTopologicalColimitIso Stage T Φ hflow_add hmap_naturality t).inv x =
      flowTopologicalColimitMap Stage T Φ hmap_naturality (-t) x :=
  rfl

theorem flowTopologicalColimitIso_hom_stage
    (t : ℝ) (n : ℕ) (a : Stage n) :
    (flowTopologicalColimitIso Stage T Φ hflow_add hmap_naturality t).hom
        (topologicalInjection Stage (system Stage T) n a) =
      topologicalInjection Stage (system Stage T) n (Φ.flow n t a) := by
  exact flowTopologicalColimitMap_inclusion
    Stage T Φ hmap_naturality t n a

theorem flowTopologicalColimitIso_zero :
    flowTopologicalColimitIso Stage T Φ hflow_add hmap_naturality 0 =
      Iso.refl (topologicalColimit Stage (system Stage T)) := by
  apply CategoryTheory.Iso.ext
  exact flowTopologicalColimitMap_zero
    Stage T Φ hflow_add hmap_naturality

theorem flowTopologicalColimitIso_add (t s : ℝ) :
    flowTopologicalColimitIso Stage T Φ hflow_add hmap_naturality (t + s) =
      flowTopologicalColimitIso Stage T Φ hflow_add hmap_naturality s ≪≫
        flowTopologicalColimitIso Stage T Φ hflow_add hmap_naturality t := by
  apply CategoryTheory.Iso.ext
  exact flowTopologicalColimitMap_add
    Stage T Φ hflow_add hmap_naturality t s

end InfoGeometry.Canonical.FixedIndexCuntzModularFlowTopologicalIso
