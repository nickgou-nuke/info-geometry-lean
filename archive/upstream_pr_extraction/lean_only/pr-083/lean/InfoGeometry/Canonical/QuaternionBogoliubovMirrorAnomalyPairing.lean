import InfoGeometry.Canonical.QuaternionCoordinateBogoliubovEquiv
import InfoGeometry.Topology.MirrorAnomalyPairing

/-!
# Conditional anomaly pairing on the transported Bogoliubov carrier

The carrier involution is the explicit real-linear transport of the native
mirror/rail map.  Anomaly cancellation remains conditional on an anomaly
readout being odd under that involution.
-/

namespace InfoGeometry.Canonical.QuaternionBogoliubovMirrorAnomalyPairing

universe v

open InfoGeometry.Topology.MappingTorusGluing
open InfoGeometry.Topology.MirrorAnomalyPairing
open InfoGeometry.Canonical.QuaternionCoordinateBogoliubovEquiv

abbrev Carrier := BogoliubovCarrier

noncomputable def datum {A : Type v} [AddGroup A]
    (anomaly : Carrier → A)
    (odd : ∀ x,
      anomaly (mirrorRailBogoliubovInvolution x) = -anomaly x) :
    Datum Carrier A :=
  { gluing :=
      { map := mirrorRailBogoliubovInvolution
        involutive := by
          intro x
          exact mirrorRailBogoliubovInvolution_involutive x }
    anomaly := anomaly
    anomaly_neg := odd }

theorem paired_sum_zero {A : Type v} [AddGroup A]
    (anomaly : Carrier → A)
    (odd : ∀ x,
      anomaly (mirrorRailBogoliubovInvolution x) = -anomaly x)
    (x : Carrier) :
    anomaly x + anomaly (mirrorRailBogoliubovInvolution x) = 0 := by
  exact InfoGeometry.Topology.MirrorAnomalyPairing.paired_sum_zero
    (datum anomaly odd) x

end InfoGeometry.Canonical.QuaternionBogoliubovMirrorAnomalyPairing
