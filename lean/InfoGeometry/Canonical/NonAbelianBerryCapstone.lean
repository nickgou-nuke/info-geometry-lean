import InfoGeometry.Topological.NonAbelianBerry

namespace InfoGeometry.Canonical.NonAbelianBerryCapstone

open InfoGeometry.Topological.NonAbelianBerry

set_option linter.unusedVariables false

/-- Canonical export of the proved Berry-connection and holonomy identities. -/
theorem verification_capstone (θ ω α : ℝ) :
    (star (apolloniusLoopConnection θ ω) = apolloniusLoopConnection θ ω) ∧
      (star (apolloniusHolonomyMatrix α) *
        (apolloniusHolonomyMatrix α) = 1) := by
  exact grand_apollonius_nonabelian_berry_synthesis θ ω α

end InfoGeometry.Canonical.NonAbelianBerryCapstone
