import InfoGeometry.Topological.ApolloniusBraiding
import InfoGeometry.Algebra.FiniteSpinAlgebra

namespace InfoGeometry.Canonical.ApolloniusBraidingCapstone

open InfoGeometry.Topological.ApolloniusBraiding
open Complex

set_option linter.unusedVariables false

theorem verification_capstone
    (gamma : ℝ)
    (F R : Matrix (Fin 2) (Fin 2) ℂ)
    (hF_adj : star F = F)
    (hF_unit : F * F = 1)
    (hR_unit : star R * R = 1)
    (hR_unit' : R * star R = 1) :
    (normSq (spectralPuncture gamma) = 1) ∧
      (star (apolloniusBraidGenerator F R) *
        (apolloniusBraidGenerator F R) = 1) := by
  exact grand_apollonius_cayley_braiding_synthesis gamma F R hF_adj hF_unit
    hR_unit hR_unit'

end InfoGeometry.Canonical.ApolloniusBraidingCapstone
