import InfoGeometry.Canonical.HexIndexTrialityEquivariance

namespace InfoGeometry.Canonical

open HexagonalSixRootTiling

noncomputable section

theorem sheetColorEquiv_colorRotation (n : HexIndex) :
    sheetColorEquiv (colorRotation n) =
      ((sheetColorEquiv n).1, fin3Successor (sheetColorEquiv n).2) := by
  fin_cases n <;> rfl

theorem hexIndexSixSector_colorRotation (n : HexIndex) :
    trialityColorCycle (hexIndexSixSector n) =
      hexIndexSixSector (colorRotation n) := by
  rw [hexIndexSixSector_eq_sheetColor n,
    hexIndexSixSector_eq_sheetColor (colorRotation n),
    sheetColorEquiv_colorRotation]
  exact trialityColorCycle_sixSectorBasisFin3
    (hexSheetFin2 (sheetColorEquiv n).1) (sheetColorEquiv n).2

end
end InfoGeometry.Canonical
