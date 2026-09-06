import InfoGeometry.Topological.NonAbelianBerry

namespace InfoGeometry.Canonical.NonAbelianBerryCapstone

open InfoGeometry.Topological.NonAbelianBerry

set_option linter.unusedVariables false

theorem verification_capstone (θ ω α : ℝ) :
    (star (apolloniusLoopConnection θ ω) = apolloniusLoopConnection θ ω) ∧
      (star (apolloniusHolonomyMatrix α) *
        (apolloniusHolonomyMatrix α) = 1) := by
  exact grand_apollonius_nonabelian_berry_synthesis θ ω α

end InfoGeometry.Canonical.NonAbelianBerryCapstone
