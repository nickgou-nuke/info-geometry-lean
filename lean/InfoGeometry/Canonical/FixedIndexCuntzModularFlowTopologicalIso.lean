import InfoGeometry.Canonical.FixedIndexCuntzModularFlowTopologicalColimit
import InfoGeometry.Algebra.FiniteSpinAlgebra

/-!
# TopCat isomorphism carried by the descended Cuntz modular flow

The preceding owner constructs the flow on the topological colimit and proves
the two inverse laws for times `t` and `-t`.  This file packages those maps as
the corresponding native `TopCat` isomorphism.
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
variable (Φ : FlowData Stage T)

def flowTopologicalColimitIso (t : ℝ) :
    topologicalColimit Stage (system Stage T) ≅
      topologicalColimit Stage (system Stage T) where
  hom := flowTopologicalColimitMap Stage T Φ t
  inv := flowTopologicalColimitMap Stage T Φ (-t)
  hom_inv_id := flowTopologicalColimitMap_right_inverse Stage T Φ t
  inv_hom_id := flowTopologicalColimitMap_left_inverse Stage T Φ t

@[simp] theorem flowTopologicalColimitIso_hom_apply
    (t : ℝ) (x : topologicalColimit Stage (system Stage T)) :
    (flowTopologicalColimitIso Stage T Φ t).hom x =
      flowTopologicalColimitMap Stage T Φ t x :=
  rfl

@[simp] theorem flowTopologicalColimitIso_inv_apply
    (t : ℝ) (x : topologicalColimit Stage (system Stage T)) :
    (flowTopologicalColimitIso Stage T Φ t).inv x =
      flowTopologicalColimitMap Stage T Φ (-t) x :=
  rfl

theorem flowTopologicalColimitIso_hom_stage
    (t : ℝ) (n : ℕ) (a : Stage n) :
    (flowTopologicalColimitIso Stage T Φ t).hom
        (topologicalInjection Stage (system Stage T) n a) =
      topologicalInjection Stage (system Stage T) n (Φ.flow n t a) := by
  exact flowTopologicalColimitMap_inclusion Stage T Φ t n a

theorem flowTopologicalColimitIso_zero :
    flowTopologicalColimitIso Stage T Φ 0 =
      Iso.refl (topologicalColimit Stage (system Stage T)) := by
  apply CategoryTheory.Iso.ext
  exact flowTopologicalColimitMap_zero Stage T Φ

theorem flowTopologicalColimitIso_add (t s : ℝ) :
    flowTopologicalColimitIso Stage T Φ (t + s) =
      flowTopologicalColimitIso Stage T Φ s ≪≫
        flowTopologicalColimitIso Stage T Φ t := by
  apply CategoryTheory.Iso.ext
  exact flowTopologicalColimitMap_add Stage T Φ t s

end InfoGeometry.Canonical.FixedIndexCuntzModularFlowTopologicalIso
