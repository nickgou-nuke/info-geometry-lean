import InfoGeometry.Canonical.RealUHFCompatibleReadoutObservable
import InfoGeometry.Canonical.RealUHFProjectionRankCompletionReadoutSquare

/-!
# Explicit square between compatible-family observables and projection rank

The two source carriers are not identified.  A bridge datum supplies a
compatible continuous-family point and explicitly identifies its interval
readout with the normalized readout of a coherent projection system.  The
resulting real observable is then independent of the chosen finite stage.
-/

noncomputable section

namespace InfoGeometry.Canonical.RealUHFCompatibleProjectionReadoutBridge

open InfoGeometry.Canonical
open InfoGeometry.Canonical.RealUHFCompatibleReadoutObservable
open InfoGeometry.Canonical.RealUHFProjectionRankIntervalTopological
open InfoGeometry.Canonical.RealUHFProjectionRankRealCompletionTopological
open InfoGeometry.Canonical.RealUHFProjectionRankCompletionReadoutSquare

structure Data where
  observable : RealUHFCompatibleReadoutObservable.Data
  family : carrier
  projectionSystem : RealUHFProjectionRankSystem
  intervalReadout_agrees :
    observable.intervalReadout family =
      normalizedIntervalReadout projectionSystem

def realReadout (D : Data) : RealUnitInterval :=
  realObservable D.observable D.family

theorem realReadout_eq_normalized (D : Data) :
    realReadout D = normalizedRealReadout D.projectionSystem := by
  unfold realReadout realObservable normalizedRealReadout
  rw [D.intervalReadout_agrees]

theorem realReadout_eq_stage (D : Data) (n : ℕ) :
    dyadicToRealInterval
        (D.projectionSystem.normalizedReadoutInterval n) =
      realReadout D := by
  rw [realReadout_eq_normalized]
  exact normalizedRealReadout_eq_stage D.projectionSystem n

theorem realReadout_eq_stage_zero (D : Data) :
    dyadicToRealInterval
        (D.projectionSystem.normalizedReadoutInterval 0) =
      realReadout D :=
  realReadout_eq_stage D 0

end InfoGeometry.Canonical.RealUHFCompatibleProjectionReadoutBridge
end
