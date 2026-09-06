import InfoGeometry.Canonical.DyadicDimensionGroupUniversalProperty
import InfoGeometry.Canonical.DyadicStageTopCatColimit

namespace InfoGeometry.Canonical.DyadicStageUniversalTopCatBridge

open InfoGeometry.Canonical.DyadicDimensionGroupTopCat
open InfoGeometry.Canonical.DyadicStageReadoutTopCat
open InfoGeometry.Canonical.DyadicStageTopCatColimit

noncomputable section

def dyadicCanonicalStageHom (n : ℕ) : ℤ →+ DyadicRational where
  toFun := dyadicStageMap n
  map_zero' := by
    apply Subtype.ext
    simp [dyadicStageMap]
  map_add' := by
    intro z w
    apply Subtype.ext
    change ((z + w : ℤ) : ℚ) / (2 : ℚ) ^ n =
      (z : ℚ) / (2 : ℚ) ^ n + (w : ℚ) / (2 : ℚ) ^ n
    push_cast
    ring

def dyadicCanonicalCocone : DyadicCocone DyadicRational where
  leg := dyadicCanonicalStageHom
  compatible := by
    intro n z
    exact dyadicStageMap_succ n z

theorem dyadicCanonicalCocone_leg (n : ℕ) (z : ℤ) :
    dyadicCanonicalCocone.leg n z = dyadicStageMap n z := rfl

theorem dyadicCanonicalCocone_lift_id :
    dyadicCanonicalCocone.lift =
      AddMonoidHom.id DyadicRational := by
  ext q
  rcases q.property with ⟨z, n, hq⟩
  have hq' : q = dyadicStageMap n z := by
    apply Subtype.ext
    exact hq
  rw [hq']
  rw [DyadicCocone.lift_stage]
  rfl

theorem dyadicStageReadoutCocone_matches_canonical (n : ℕ) (z : ℤ) :
    dyadicStageReadoutCocone.ι.app n z =
      dyadicCanonicalCocone.leg n z := rfl

end
end InfoGeometry.Canonical.DyadicStageUniversalTopCatBridge
