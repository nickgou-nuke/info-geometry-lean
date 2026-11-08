import InfoGeometry.KL.Measure
import Mathlib.MeasureTheory.Measure.Dirac

namespace InfoGeometry.Epistemology.DiracRelativeEntropyBoundary

open MeasureTheory
open scoped ENNReal

theorem kl_to_dirac_eq_top_of_mass_outside {Space : Type*}
    [MeasurableSpace Space] [MeasurableSingletonClass Space]
    (distribution : Measure Space) (point : Space)
    (outside : distribution ({point}ᶜ) ≠ 0) :
    InfoGeometry.KL.kl_div distribution (Measure.dirac point) = ∞ := by
  apply InfoGeometry.KL.klDiv_of_not_ac
  intro absolutely_continuous
  apply outside
  exact absolutely_continuous (by simp)

theorem dirac_to_distinct_dirac {Space : Type*}
    [MeasurableSpace Space] [MeasurableSingletonClass Space]
    (first second : Space) (distinct : first ≠ second) :
    InfoGeometry.KL.kl_div (Measure.dirac first) (Measure.dirac second) = ∞ := by
  apply kl_to_dirac_eq_top_of_mass_outside
  simp [distinct]

end InfoGeometry.Epistemology.DiracRelativeEntropyBoundary
