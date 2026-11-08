import InfoGeometry.Topology.SplitOctonionMirrorRailMappingTorus
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Topology.MirrorAnomalyPairing

/-!
# Conditional anomaly pairing for the native mirror/rail involution

The Zorn owner supplies the involution.  The only additional datum required
for cancellation is that the chosen anomaly readout is odd under it.
-/

namespace InfoGeometry.Topology.SplitOctonionMirrorAnomalyPairing

universe v

open InfoGeometry.Lie.SplitOctonionQuaternionZornCoordinates
open InfoGeometry.Lie.SplitOctonionQuaternionParityOrientation
open InfoGeometry.Topology.MirrorAnomalyPairing
open InfoGeometry.Topology.SplitOctonionMirrorRailMappingTorus

abbrev Carrier := CartesianCoordinates

noncomputable def datum {A : Type v} [AddGroup A]
    (anomaly : Carrier → A)
    (odd : ∀ x, anomaly (mirrorRailSwapJK x) = -anomaly x) :
    Datum Carrier A :=
  { gluing := mirrorRailGluing
    anomaly := anomaly
    anomaly_neg := odd }

theorem paired_sum_zero {A : Type v} [AddGroup A]
    (anomaly : Carrier → A)
    (odd : ∀ x, anomaly (mirrorRailSwapJK x) = -anomaly x)
    (x : Carrier) :
    anomaly x + anomaly (mirrorRailSwapJK x) = 0 := by
  exact MirrorAnomalyPairing.paired_sum_zero (datum anomaly odd) x

theorem anomaly_pairing_respects_involution {A : Type v} [AddGroup A]
    (x : Carrier) :
    mirrorRailSwapJK (mirrorRailSwapJK x) = x := by
  exact mirrorRailSwapJK_involutive x

end InfoGeometry.Topology.SplitOctonionMirrorAnomalyPairing
