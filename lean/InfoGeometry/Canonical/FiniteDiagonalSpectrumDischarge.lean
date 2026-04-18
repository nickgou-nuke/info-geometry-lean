import InfoGeometry.Canonical.PositiveMeasureSpectrum
import InfoGeometry.Meta.Architecture

namespace InfoGeometry.Canonical.Positivity

/-!
# InfoGeometry.Canonical.FiniteDiagonalSpectrumDischarge

Compatibility shadow module.

Finite-dimensional diagonal toy constructions are intentionally excluded from
the canonical owner lane. The active closure surface is
`InfoGeometry.Canonical.PositiveMeasureSpectrum`.
-/

/-- Canonical reminder that positivity/log closure is owned by the non-toy lane. -/
@[rep_depth operator]
theorem finiteDiagonalShadowExcluded : True := by
  trivial

end InfoGeometry.Canonical.Positivity

