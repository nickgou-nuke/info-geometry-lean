import InfoGeometry.Clifford.Cl55WittPinParity
import InfoGeometry.Clifford.Cl55WittSpinOrthogonalAction

namespace InfoGeometry.Clifford.Clifford55

/-!
# Explicit reflection evidence for the native Pin-to-orthogonal action

These are image equalities for the already constructed Pin lifts.  They do
not assert that the full orthogonal group is the image.
-/

theorem pinTwistedOrthogonalAction_fNegPin (i : Fin 5) :
    pinTwistedOrthogonalAction (fNegPin i) = coordinateReflectionGenerator i := by
  apply Subtype.ext
  exact pinTwistedActionEquiv_fNegPin_eq_negativeReflection i

theorem pinTwistedOrthogonalAction_globalSheetPin :
    pinTwistedOrthogonalAction globalSheetPin =
      globalSheetReflectionGenerator := by
  apply Subtype.ext
  exact pinTwistedActionEquiv_globalSheetPin_eq_globalSheetReflection

end InfoGeometry.Clifford.Clifford55
