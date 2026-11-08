/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Canonical.TopCatColimitCompatibleEndomorphism

namespace InfoGeometry.Canonical.TopCatColimitCompatibleEndomorphism

open CategoryTheory CategoryTheory.Limits

noncomputable section

variable {J : Type*} [Category J]
variable (F : J ⥤ TopCat) [HasColimit F]

theorem induced_isIso_of_involutive
    (η : F ⟶ F) (hη : η ≫ η = 𝟙 F) :
    IsIso (induced F η) := by
  exact (inducedIso F η η hη hη).isIso_hom

end
end InfoGeometry.Canonical.TopCatColimitCompatibleEndomorphism
