import InfoGeometry.MeasureProjective
import InfoGeometry.Algebra.FiniteSpinAlgebra
import Mathlib.MeasureTheory.Measure.LogLikelihoodRatio

set_option autoImplicit false
open scoped ENNReal

namespace InfoGeometry.MeasureProjective

open MeasureTheory

variable {α : Type*} [MeasurableSpace α] [Nonempty α]


theorem logGeneratorClass_invariant
    (base ξ : NonzeroUState α) :
    ProjectiveState.logGeneratorClass ⟦base⟧ ⟦ξ⟧ =
      logPotentialClass ((ξ.1.normalize : ProbabilityMeasure α) : Measure α)
                        ((base.1.normalize : ProbabilityMeasure α) : Measure α) := rfl

end InfoGeometry.MeasureProjective
