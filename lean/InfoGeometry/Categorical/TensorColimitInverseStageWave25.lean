/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/

import InfoGeometry.Categorical.TensorColimit

noncomputable section

namespace InfoGeometry.Categorical

open CategoryTheory MonoidalCategory Limits

/-- The inverse tensor-colimit comparison also recovers every canonical stage
injection.  This is the inverse orientation of `tensorColimitIso_ι`, proved
from the same native comparison isomorphism. -/
@[reassoc]
theorem tensorColimitIso_inv_ι
    {R : Type*} [CommRing R]
    {J : Type*} [Category J]
    (F : J ⥤ ModuleCat R) (M : ModuleCat R)
    [HasColimit F]
    [PreservesColimit F ((tensoringRight (ModuleCat R)).obj M)]
    [HasColimit (F ⋙ (tensoringRight (ModuleCat R)).obj M)]
    (j : J) :
    ((tensoringRight (ModuleCat R)).obj M).map
        (colimit.ι F j) ≫
      (tensorColimitIso F M).inv =
      colimit.ι (F ⋙ (tensoringRight (ModuleCat R)).obj M) j := by
  apply (cancel_mono (tensorColimitIso F M).hom).1
  calc
    (((tensoringRight (ModuleCat R)).obj M).map (colimit.ι F j) ≫
        (tensorColimitIso F M).inv) ≫ (tensorColimitIso F M).hom =
      ((tensoringRight (ModuleCat R)).obj M).map (colimit.ι F j) ≫
        ((tensorColimitIso F M).inv ≫ (tensorColimitIso F M).hom) := by
          rw [Category.assoc]
    _ = ((tensoringRight (ModuleCat R)).obj M).map (colimit.ι F j) := by
          rw [Iso.inv_hom_id, Category.comp_id]
    _ = colimit.ι (F ⋙ (tensoringRight (ModuleCat R)).obj M) j ≫
        (tensorColimitIso F M).hom := (tensorColimitIso_ι F M j).symm

end InfoGeometry.Categorical
