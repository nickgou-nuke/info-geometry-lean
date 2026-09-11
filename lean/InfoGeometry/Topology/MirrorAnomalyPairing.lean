import InfoGeometry.Topology.MappingTorusGluing
import InfoGeometry.Algebra.FiniteSpinAlgebra

/-!
# Conditional anomaly pairing

The mapping-torus gluing supplies an involution.  Cancellation is a separate
statement: it requires an anomaly readout that changes sign under that
involution.  This owner formalizes exactly that implication.
-/

namespace InfoGeometry.Topology.MirrorAnomalyPairing

universe u v

open InfoGeometry.Topology.MappingTorusGluing

structure Datum (F : Type u) (A : Type v) [AddGroup A] where
  gluing : InvolutiveGluing (F := F)
  anomaly : F → A
  anomaly_neg : ∀ x, anomaly (gluing.map x) = -anomaly x

theorem paired_sum_zero {F : Type u} {A : Type v} [AddGroup A]
    (D : Datum F A) (x : F) :
    D.anomaly x + D.anomaly (D.gluing.map x) = 0 := by
  rw [D.anomaly_neg]
  exact add_neg_cancel _

theorem pairing_is_involutive {F : Type u} {A : Type v} [AddGroup A]
    (D : Datum F A) (x : F) :
    D.gluing.map (D.gluing.map x) = x :=
  D.gluing.involutive x

end InfoGeometry.Topology.MirrorAnomalyPairing
