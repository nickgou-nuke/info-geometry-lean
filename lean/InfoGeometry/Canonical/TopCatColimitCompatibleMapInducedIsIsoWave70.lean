/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Canonical.TopCatColimitCompatibleMap

namespace InfoGeometry.Canonical.TopCatColimitCompatibleMap

open CategoryTheory CategoryTheory.Limits

noncomputable section

variable {J : Type*} [Category J]
variable {F G : J ⥤ TopCat} [HasColimit F] [HasColimit G]

theorem inducedMap_isIso (e : F ≅ G) :
    IsIso (inducedMap e.hom) := by
  exact (inducedMapIso e).isIso_hom

end
end InfoGeometry.Canonical.TopCatColimitCompatibleMap
