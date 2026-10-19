/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/

import InfoGeometry.Categorical.OperatorAlgebraColimit

namespace InfoGeometry.Categorical.OperatorAlgebraColimit

open CategoryTheory
open CategoryTheory.Limits

universe u

variable {J : Type u} [Category.{u} J] [IsFiltered J]
variable {F F_commutant : J ⥤ RingCat.{u}}
variable (tomita_takesaki : F ≅ F_commutant)

/-- The colimit Tomita isomorphism agrees with the given finite-stage map. -/
theorem tomita_takesaki_colimit_stage (j : J)
    [HasColimit F] [HasColimit F_commutant] :
    colimit.ι F j ≫ (tomita_takesaki_colimit F F_commutant tomita_takesaki).hom =
      tomita_takesaki.hom.app j ≫ colimit.ι F_commutant j := by
  exact HasColimit.ι_isoOfNatIso_hom tomita_takesaki j

/-- The inverse colimit Tomita isomorphism agrees with the inverse finite-stage map. -/
theorem tomita_takesaki_colimit_stage_inv (j : J)
    [HasColimit F] [HasColimit F_commutant] :
    colimit.ι F_commutant j ≫ (tomita_takesaki_colimit F F_commutant tomita_takesaki).inv =
      tomita_takesaki.inv.app j ≫ colimit.ι F j := by
  exact HasColimit.ι_isoOfNatIso_inv tomita_takesaki j

end InfoGeometry.Categorical.OperatorAlgebraColimit
#print axioms InfoGeometry.Categorical.OperatorAlgebraColimit.tomita_takesaki_colimit_stage
#print axioms InfoGeometry.Categorical.OperatorAlgebraColimit.tomita_takesaki_colimit_stage_inv
