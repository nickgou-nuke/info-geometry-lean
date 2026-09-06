import InfoGeometry.Algebra.Zorn.G2ExportedIncidenceGenerator

/-!
# Flag permutations induced by the exported CAS generators

The exported incidence certificate admits genuine flag permutations for the
explicit CAS point permutations.  This owner intentionally does not claim a
global `SplitOctF2Aut` action: the native cross-product carrier has a proved
non-equivariance obstruction, and ambient generation is a separate theorem.
-/

namespace InfoGeometry.Algebra.Zorn.G2ExportedFlagGeneratorAction

open InfoGeometry.Algebra.Zorn.G2CASNativePointAction
open InfoGeometry.Algebra.Zorn.G2ExportedIncidenceGenerator
open InfoGeometry.Algebra.Zorn.G2FlagIncidenceAction

abbrev ExportedFlag := Flag

noncomputable def pcFlagPerm (k : Fin 7) : Equiv.Perm ExportedFlag :=
  flagPerm (casPointPerm k) (casPointPerm_preserves_incidence k)

noncomputable def correctedTFlagPerm : Equiv.Perm ExportedFlag :=
  flagPerm correctedTPointPerm correctedTPointPerm_preserves_incidence

theorem pcFlagPerm_apply (k : Fin 7) (f : ExportedFlag) :
    pcFlagPerm k f =
      flagMap (casPointPerm k) (casPointPerm_preserves_incidence k) f := by
  rfl

theorem correctedTFlagPerm_apply (f : ExportedFlag) :
    correctedTFlagPerm f =
      flagMap correctedTPointPerm correctedTPointPerm_preserves_incidence f := by
  rfl

end InfoGeometry.Algebra.Zorn.G2ExportedFlagGeneratorAction
