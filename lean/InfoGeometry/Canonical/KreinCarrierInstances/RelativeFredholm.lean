import InfoGeometry.Canonical.KreinCarrierInstances.Datum
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Canonical.HestenesKreinModularGeometry
import Mathlib.Tactic

open InfoGeometry.Canonical.HestenesKreinModularGeometry

noncomputable section

def concreteRelativeFredholmKlein_modularDefect : RealEnd KleinBottleCarrier := 0

theorem concreteRelativeFredholmKlein_modularDefect_eq :
    concreteRelativeFredholmKlein_modularDefect =
      concreteKreinDatumKlein.modularWeight - concreteKreinDatumKlein.modularWeight := by
  ext; simp [concreteRelativeFredholmKlein_modularDefect, concreteKreinDatumKlein]

def concreteRelativeFredholmKlein_fredholm_determinant : ℝ := 1

def concreteRelativeFredholmKlein_fredholm_kreinTrace : ℝ := 0

theorem concreteRelativeFredholmKlein_fredholm_determinant_first_order :
    concreteRelativeFredholmKlein_fredholm_determinant = 1 + concreteRelativeFredholmKlein_fredholm_kreinTrace := by
  norm_num [concreteRelativeFredholmKlein_fredholm_determinant, concreteRelativeFredholmKlein_fredholm_kreinTrace]

def concreteRelativeFredholmKlein_fredholm : KreinFredholmDeterminantContract concreteRelativeFredholmKlein_modularDefect where
  determinant := concreteRelativeFredholmKlein_fredholm_determinant
  kreinTrace := concreteRelativeFredholmKlein_fredholm_kreinTrace
  determinant_first_order := concreteRelativeFredholmKlein_fredholm_determinant_first_order

def concreteRelativeFredholmKlein_relativePartitionReadout : ℝ := 1

theorem concreteRelativeFredholmKlein_relativePartitionReadout_eq_det :
    concreteRelativeFredholmKlein_relativePartitionReadout = concreteRelativeFredholmKlein_fredholm.determinant := by
  rfl

def concreteRelativeFredholmKlein_relativeCountDensity : ℝ := 0

theorem concreteRelativeFredholmKlein_relativeCountDensity_eq_log :
    concreteRelativeFredholmKlein_relativeCountDensity = Real.log concreteRelativeFredholmKlein_relativePartitionReadout := by
  dsimp [concreteRelativeFredholmKlein_relativeCountDensity, concreteRelativeFredholmKlein_relativePartitionReadout]
  rw [Real.log_one]

/-- Concrete zero-defect relative Fredholm datum. -/
def concreteRelativeFredholmKlein : RelativeKreinModularFredholmDatum KleinBottleCarrier where
  referenceDatum := concreteKreinDatumKlein
  localizedDatum := concreteKreinDatumKlein
  modularDefect := concreteRelativeFredholmKlein_modularDefect
  modularDefect_eq := concreteRelativeFredholmKlein_modularDefect_eq
  fredholm := concreteRelativeFredholmKlein_fredholm
  relativePartitionReadout := concreteRelativeFredholmKlein_relativePartitionReadout
  relativePartitionReadout_eq_det := concreteRelativeFredholmKlein_relativePartitionReadout_eq_det
  relativeCountDensity := concreteRelativeFredholmKlein_relativeCountDensity
  relativeCountDensity_eq_log := concreteRelativeFredholmKlein_relativeCountDensity_eq_log

end
