import InfoGeometry.Algebra.Zorn.G2FlagIncidenceAction
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Algebra.Zorn.G2CASNativePointAction

/-! The exported CAS point permutations are not silently promoted to flag
actions: this file records their certified incidence obstructions. -/

namespace InfoGeometry.Algebra.Zorn.G2ExportedIncidenceGenerator

open InfoGeometry.Algebra.Zorn.G2FlagIncidenceAction
open InfoGeometry.Algebra.Zorn.G2CASNativePointAction
open InfoGeometry.Algebra.Zorn.G2HexagonIncidence
open InfoGeometry.Algebra.Zorn.G2ParabolicIncidenceCertificate

/-- Explicit incidence witness for the first exported permutation: the
incidence of point `0` with line `1` is not preserved by its image data. -/
theorem casPointPerm_zero_incidence_witness :
    ¬ (0 ∈ parabolicIncidenceData.linePoints 1 ↔
      0 ∈ parabolicIncidenceData.linePoints 3) := by
  decide

theorem casPointPerm_zero_not_preserves_incidence :
    ¬ PreservesIncidence (casPointPerm 0) := by
  intro h
  have hh := h 0 1
  apply casPointPerm_zero_incidence_witness
  simpa [casPointPerm, casPointPermRaw] using hh

/-- Explicit incidence witness for the corrected point permutation. -/
theorem correctedTPointPerm_incidence_witness :
    ¬ (0 ∈ parabolicIncidenceData.linePoints 1 ↔
      28 ∈ parabolicIncidenceData.linePoints 7) := by
  decide

theorem correctedTPointPerm_not_preserves_incidence :
    ¬ PreservesIncidence correctedTPointPerm := by
  intro h
  have hh := h 0 1
  apply correctedTPointPerm_incidence_witness
  simpa [correctedTPointPerm, correctedTPointPermRaw] using hh

end InfoGeometry.Algebra.Zorn.G2ExportedIncidenceGenerator
