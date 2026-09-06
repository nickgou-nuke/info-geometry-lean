import InfoGeometry.Canonical.DyadicDimensionGroupTopCat

namespace InfoGeometry.Canonical.DyadicStageReadoutTopCat

open CategoryTheory
open InfoGeometry.Canonical.DyadicDimensionGroupTopCat

noncomputable section

def dyadicStageReadoutTopCatHom (n : ℕ) :
    TopCat.of ℤ ⟶ dyadicRationalTopCat :=
  TopCat.ofHom
    { toFun := dyadicStageMap n
      continuous_toFun := by
        exact continuous_of_discreteTopology }

def dyadicStageTransitionTopCatHom (n : ℕ) :
    TopCat.of ℤ ⟶ TopCat.of ℤ :=
  TopCat.ofHom
    { toFun := fun z : ℤ => 2 * z
      continuous_toFun := by fun_prop }

theorem dyadicStageReadoutTopCatHom_compatibility (n : ℕ) :
    dyadicStageTransitionTopCatHom n ≫
        dyadicStageReadoutTopCatHom (n + 1) =
      dyadicStageReadoutTopCatHom n := by
  apply TopCat.hom_ext
  ext z
  exact dyadicStageMap_succ n z

theorem dyadicStageReadoutTopCatHom_apply (n : ℕ) (z : ℤ) :
    dyadicStageReadoutTopCatHom n z = dyadicStageMap n z := rfl

theorem dyadicStageTransitionTopCatHom_apply (n : ℕ) (z : ℤ) :
    dyadicStageTransitionTopCatHom n z = 2 * z := rfl

end
end InfoGeometry.Canonical.DyadicStageReadoutTopCat
