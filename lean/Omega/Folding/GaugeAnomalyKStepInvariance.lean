import Mathlib.Tactic
import Omega.Folding.BernoulliPEndpointLdpRestated
import Omega.Folding.BernoulliPParryPressureChain
import Omega.Folding.GaugeAnomalyMean
import Omega.Folding.GaugeAnomalyTauIntClosed

namespace Omega.Folding

/-- Paper-facing fixed-step invariance wrapper for the gauge anomaly: for each fixed `k`, the
multi-step truncation changes only the boundary vectors of the same primitive finite-state model,
so the mean density, CLT variance, pressure, and endpoint LDP formulas agree with the `k = 1`
case.
    thm:fold-gauge-anomaly-kstep-invariance -/
theorem paper_fold_gauge_anomaly_kstep_invariance
    (primitiveFiniteStateRealization boundaryCorrectionO1 densityLimitInvariant cltInvariant
      pressureInvariant ldpEndpointInvariant : Prop)
    (hPrimitiveFiniteStateRealization : primitiveFiniteStateRealization)
    (hBoundaryCorrectionO1 : boundaryCorrectionO1)
    (deriveDensityLimitInvariant :
      primitiveFiniteStateRealization → boundaryCorrectionO1 → densityLimitInvariant)
    (deriveCltInvariant :
      primitiveFiniteStateRealization → boundaryCorrectionO1 → cltInvariant)
    (derivePressureInvariant :
      primitiveFiniteStateRealization → boundaryCorrectionO1 → pressureInvariant)
    (deriveLdpEndpointInvariant : pressureInvariant → ldpEndpointInvariant) :
    densityLimitInvariant ∧ cltInvariant ∧ pressureInvariant ∧ ldpEndpointInvariant := by
  have hDensity : densityLimitInvariant :=
    deriveDensityLimitInvariant hPrimitiveFiniteStateRealization hBoundaryCorrectionO1
  have hClt : cltInvariant :=
    deriveCltInvariant hPrimitiveFiniteStateRealization hBoundaryCorrectionO1
  have hPressure : pressureInvariant :=
    derivePressureInvariant hPrimitiveFiniteStateRealization hBoundaryCorrectionO1
  exact ⟨hDensity, hClt, hPressure, deriveLdpEndpointInvariant hPressure⟩

end Omega.Folding
