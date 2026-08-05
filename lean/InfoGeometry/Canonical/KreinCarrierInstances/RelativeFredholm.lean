import InfoGeometry.Canonical.KreinCarrierInstances.Datum
import InfoGeometry.Canonical.HestenesKreinModularGeometry
import Mathlib.Tactic

open InfoGeometry.Canonical.HestenesKreinModularGeometry

noncomputable section

/-- Concrete zero-defect relative Fredholm datum. -/
def concreteRelativeFredholmKlein : RelativeKreinModularFredholmDatum KleinBottleCarrier where
  referenceDatum := concreteKreinDatumKlein
  localizedDatum := concreteKreinDatumKlein
  modularDefect := 0
  modularDefect_eq := by
    ext
    simp [concreteKreinDatumKlein]
  fredholm := {
    determinant := 1
    kreinTrace := 0
    determinant_first_order := by norm_num
  }
  relativePartitionReadout := 1
  relativePartitionReadout_eq_det := by rfl
  relativeCountDensity := 0
  relativeCountDensity_eq_log := by norm_num

end
