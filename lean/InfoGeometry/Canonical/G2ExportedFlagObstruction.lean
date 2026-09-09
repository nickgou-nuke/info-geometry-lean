import InfoGeometry.Algebra.Zorn.G2ExportedIncidenceGenerator
import InfoGeometry.Algebra.Zorn.G2FlagIncidenceAction

/-!
# Obstruction to the upstream exported flag lift

The finite point permutations exported by the CAS certificate are not
incidence automorphisms.  Consequently the conditional `flagPerm` constructor
cannot be applied to them.  This records that boundary explicitly instead of
manufacturing a flag action.
-/

namespace InfoGeometry.Canonical.G2ExportedFlagObstruction

open InfoGeometry.Algebra.Zorn.G2CASNativePointAction
open InfoGeometry.Algebra.Zorn.G2ExportedIncidenceGenerator
open InfoGeometry.Algebra.Zorn.G2FlagIncidenceAction

theorem no_cas_point_zero_flag_lift :
    ¬ PreservesIncidence (casPointPerm 0) :=
  casPointPerm_zero_not_preserves_incidence

theorem no_corrected_t_flag_lift :
    ¬ PreservesIncidence correctedTPointPerm :=
  correctedTPointPerm_not_preserves_incidence

end InfoGeometry.Canonical.G2ExportedFlagObstruction
