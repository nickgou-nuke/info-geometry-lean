import InfoGeometry.Algebra.Zorn.G2FlagIncidenceAction
import InfoGeometry.Algebra.Zorn.G2CASNativePointAction

/-!
# Exported point-action/incidence compatibility audit

The CAS permutations act on the native 63-point orbit.  The parabolic
incidence certificate uses a separately indexed point/line table, so these
permutations cannot be used as simultaneous point and line permutations.
This owner records explicit kernel-checked obstructions rather than a false
flag action.
-/

namespace InfoGeometry.Algebra.Zorn.G2ExportedIncidenceGenerator

open InfoGeometry.Algebra.Zorn.G2FlagIncidenceAction
open InfoGeometry.Algebra.Zorn.G2CASNativePointAction
open InfoGeometry.Algebra.Zorn.G2HexagonIncidence
open InfoGeometry.Algebra.Zorn.G2ParabolicIncidenceCertificate

theorem casPointPerm_zero_not_preserves_incidence :
    ¬ PreservesIncidence (casPointPerm 0) := by
  intro h
  have hh := h 0 1
  have hc :
      ¬ (0 ∈ parabolicIncidenceData.linePoints 1 ↔
        0 ∈ parabolicIncidenceData.linePoints 3) := by
    native_decide
  apply hc
  simpa [casPointPerm, casPointPermRaw] using hh

theorem correctedTPointPerm_not_preserves_incidence :
    ¬ PreservesIncidence correctedTPointPerm := by
  intro h
  have hh := h 0 1
  have hc :
      ¬ (0 ∈ parabolicIncidenceData.linePoints 1 ↔
        28 ∈ parabolicIncidenceData.linePoints 7) := by
    native_decide
  apply hc
  simpa [correctedTPointPerm, correctedTPointPermRaw] using hh

end InfoGeometry.Algebra.Zorn.G2ExportedIncidenceGenerator
