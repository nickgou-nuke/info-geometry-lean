import Mathlib.Tactic
import InfoGeometry.External.Automath.Omega.Folding.BernoulliPEndpointLdpRestated
import InfoGeometry.External.Automath.Omega.Folding.BernoulliPParryPressureChain
import InfoGeometry.External.Automath.Omega.Folding.GaugeAnomalyMean
import InfoGeometry.External.Automath.Omega.Folding.GaugeAnomalyTauIntClosed

namespace Omega.Folding

/-- Chapter-local package for the fixed-step gauge-anomaly invariance theorem. The fields encode
the primitive finite-state realization, the `O(1)` boundary correction for a fixed `k`, and the
transfer of density, CLT, pressure, and endpoint LDP data from the one-step observable to the
`k`-step truncation. -/
structure GaugeAnomalyKStepInvarianceData where
  primitiveFiniteStateRealization : Prop
  boundaryCorrectionO1 : Prop
  densityLimitInvariant : Prop
  cltInvariant : Prop
  pressureInvariant : Prop
  ldpEndpointInvariant : Prop
  primitiveFiniteStateRealization_h : primitiveFiniteStateRealization
  boundaryCorrectionO1_h : boundaryCorrectionO1
  deriveDensityLimitInvariant :
    primitiveFiniteStateRealization →
      boundaryCorrectionO1 →
        densityLimitInvariant
  deriveCltInvariant :
    primitiveFiniteStateRealization →
      boundaryCorrectionO1 →
        cltInvariant
  derivePressureInvariant :
    primitiveFiniteStateRealization →
      boundaryCorrectionO1 →
        pressureInvariant
  deriveLdpEndpointInvariant :
    pressureInvariant → ldpEndpointInvariant

/-- Paper-facing fixed-step invariance wrapper for the gauge anomaly: for each fixed `k`, the
multi-step truncation changes only the boundary vectors of the same primitive finite-state model,
so the mean density, CLT variance, pressure, and endpoint LDP formulas agree with the `k = 1`
case.
    thm:fold-gauge-anomaly-kstep-invariance -/
theorem paper_fold_gauge_anomaly_kstep_invariance
    (D : GaugeAnomalyKStepInvarianceData) :
    D.densityLimitInvariant ∧
      D.cltInvariant ∧
      D.pressureInvariant ∧
      D.ldpEndpointInvariant := by
  have hDensity : D.densityLimitInvariant :=
    D.deriveDensityLimitInvariant
      D.primitiveFiniteStateRealization_h
      D.boundaryCorrectionO1_h
  have hClt : D.cltInvariant :=
    D.deriveCltInvariant
      D.primitiveFiniteStateRealization_h
      D.boundaryCorrectionO1_h
  have hPressure : D.pressureInvariant :=
    D.derivePressureInvariant
      D.primitiveFiniteStateRealization_h
      D.boundaryCorrectionO1_h
  exact ⟨hDensity, hClt, hPressure, D.deriveLdpEndpointInvariant hPressure⟩

end Omega.Folding
