import InfoGeometry.Algebra.Zorn.G2ExportedIncidenceGenerator

/-!
# Boundary of the exported flag-action construction

The corresponding upstream draft assumes that every exported point
permutation preserves the hexagon incidence relation.  The native repository
owner instead proves a concrete counterexample for `casPointPerm 0`, so a flag
permutation cannot be defined from that family without changing the carrier or
the incidence data.  This owner records the obstruction explicitly.
-/
namespace InfoGeometry.Algebra.Zorn.G2ExportedFlagAction

open InfoGeometry.Algebra.Zorn.G2ExportedIncidenceGenerator
open InfoGeometry.Algebra.Zorn.G2CASNativePointAction
open InfoGeometry.Algebra.Zorn.G2FlagIncidenceAction

theorem exported_generator_zero_not_flag_action :
    ¬ PreservesIncidence (casPointPerm 0) := by
  exact casPointPerm_zero_not_preserves_incidence

end InfoGeometry.Algebra.Zorn.G2ExportedFlagAction
