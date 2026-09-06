import InfoGeometry.Algebra.Zorn.G2ExportedIncidenceGenerator

/-!
# Flag permutations for the exported incidence-preserving generators

The incidence certificate already proves preservation for the seven exported
point permutations.  This owner lifts those permutations to the 189 incident
flags.  It deliberately does not promote the finite generator chart to an
action of the full ambient automorphism carrier.
-/

namespace InfoGeometry.Algebra.Zorn.G2ExportedFlagAction

open InfoGeometry.Algebra.Zorn.G2FlagIncidenceAction
open InfoGeometry.Algebra.Zorn.G2ExportedIncidenceGenerator
open InfoGeometry.Algebra.Zorn.G2HexagonIncidence
open InfoGeometry.Algebra.Zorn.G2CASNativePointAction

noncomputable def exportedFlagPerm (k : Fin 7) :
    Equiv.Perm (Flag parabolicCertificate) :=
  flagPerm (casPointPerm k) (casPointPerm_preserves_incidence k)

@[simp] theorem exportedFlagPerm_apply (k : Fin 7)
    (f : Flag parabolicCertificate) :
    exportedFlagPerm k f =
      flagMap (casPointPerm k) (casPointPerm_preserves_incidence k) f := rfl

theorem exportedFlagPerm_injective (k : Fin 7) :
    Function.Injective (exportedFlagPerm k) := by
  exact (exportedFlagPerm k).injective

end InfoGeometry.Algebra.Zorn.G2ExportedFlagAction
