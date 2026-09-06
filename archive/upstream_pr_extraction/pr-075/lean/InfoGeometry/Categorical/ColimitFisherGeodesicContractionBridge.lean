import InfoGeometry.Canonical.TensorTowerColimit
import InfoGeometry.Canonical.UHFInductiveColimitBoundary

/-!
# Retired scalar staged-contraction surface

The former owner encoded `StagedState n := ℝ × ℝ` and called an explicitly
chosen scalar contraction a Fisher/Radon--Nikodym flow.  It did not construct
a categorical colimit, a Fisher metric, or a measure transport, so its
conclusions cannot be promoted to the continuum.

The categorical owners for inductive limits are `TensorTowerColimit` and
`UHFInductiveColimitBoundary`.  A genuine contraction theorem must be attached
to their carriers and transition morphisms, with an operatorial flow and an
explicit compatibility law.  No scalar surrogate is exported here.
-/

namespace InfoGeometry.Categorical.ColimitFisher

end InfoGeometry.Categorical.ColimitFisher
