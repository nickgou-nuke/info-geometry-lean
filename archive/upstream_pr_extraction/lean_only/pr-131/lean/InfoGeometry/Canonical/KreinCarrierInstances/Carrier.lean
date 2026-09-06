import InfoGeometry.Topology.WallpaperSymmetry
import InfoGeometry.Canonical.HestenesKreinModularGeometry
import Mathlib.Analysis.InnerProductSpace.ProdL2
import Mathlib.Analysis.Normed.Lp.ProdLp
import Mathlib.Tactic

open InfoGeometry.Canonical.HestenesKreinModularGeometry

noncomputable section

/-- The concrete Klein-bottle chart carrier used by this module.

This is the `L²` product carrier from mathlib, not the raw product type.  The
actual Klein bottle quotient is represented separately by the imported `pg`
wallpaper action. -/
abbrev KleinBottleCarrier : Type := WithLp (2 : ENNReal) (ℝ × ℝ)

/-- The Möbius/glide chart symmetry `(x,y) ↦ (x + 1/2, -y)`. -/
def MoebiusSymmetry : KleinBottleCarrier ≃ KleinBottleCarrier where
  toFun p := WithLp.toLp (2 : ENNReal) (WithLp.fst p + (1 / 2 : ℝ), -WithLp.snd p)
  invFun p := WithLp.toLp (2 : ENNReal) (WithLp.fst p - (1 / 2 : ℝ), -WithLp.snd p)
  left_inv p := by
    apply (WithLp.ofLp_injective (p := (2 : ENNReal)))
    ext <;> simp
  right_inv p := by
    apply (WithLp.ofLp_injective (p := (2 : ENNReal)))
    ext <;> simp

/-- The canonical imported concrete `pg` wallpaper package. -/
def ConcretePG : InfoGeometry.Topology.Wallpaper.WallpaperGroupPG :=
  InfoGeometry.Topology.Wallpaper.concretePG

end
