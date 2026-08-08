import InfoGeometry.Topology.OrderThreeKreinSpinorMetricCompatibility
import InfoGeometry.Topology.OrderThreeInvariantMetricAction

/-!
# Metric property for the Krein-spinor kernel

The Krein quadratic form is indefinite, so it is not promoted to a metric by
definition.  This owner accepts one explicit calibration property identifying
the existing metric on `X` with the square root of the `J`-conjugated kernel.
All metric laws below are then inherited from the native metric space.
-/

noncomputable section

namespace InfoGeometry.Topology.OrderThreeKreinSpinorMetricWitness

open InfoGeometry.Krein
open InfoGeometry.Topology.OrderThreeInvariantMetricAction
open InfoGeometry.Topology.OrderThreeKreinSpinorMetricCompatibility

variable {X H : Type*}
variable [MetricSpace X]
variable [NormedAddCommGroup H] [InnerProductSpace ℝ H]
variable [CompleteSpace H] [KreinSpace H]

abbrev SpinorData :=
  InfoGeometry.Topology.OrderThreeKreinSpinorMetricCompatibility.Data
    (X := X) (H := H)

variable (D : SpinorData (X := X) (H := H))

def kreinDistance (x y : X) : ℝ :=
  Real.sqrt (conjugatedPositiveKernel D x y)

structure MetricWitness where
  distance_eq_krein : ∀ x y,
    dist x y = kreinDistance D x y

variable (W : MetricWitness D)

include W

theorem kreinDistance_nonneg (x y : X) :
    0 ≤ kreinDistance D x y := by
  exact Real.sqrt_nonneg _

theorem kreinDistance_eq_zero_iff (x y : X) :
    kreinDistance D x y = 0 ↔ x = y := by
  rw [← W.distance_eq_krein x y]
  exact dist_eq_zero

theorem kreinDistance_symm (x y : X) :
    kreinDistance D x y = kreinDistance D y x := by
  calc
    kreinDistance D x y = dist x y := (W.distance_eq_krein x y).symm
    _ = dist y x := dist_comm _ _
    _ = kreinDistance D y x := W.distance_eq_krein y x

theorem kreinDistance_triangle (x y z : X) :
    kreinDistance D x z ≤
      kreinDistance D x y + kreinDistance D y z := by
  calc
    kreinDistance D x z = dist x z := (W.distance_eq_krein x z).symm
    _ ≤ dist x y + dist y z := dist_triangle _ _ _
    _ = kreinDistance D x y + kreinDistance D y z := by
      rw [W.distance_eq_krein x y, W.distance_eq_krein y z]

theorem kreinDistance_action_invariant (x y : X) :
    kreinDistance D (D.actionData.action x) (D.actionData.action y) =
      kreinDistance D x y := by
  calc
    kreinDistance D (D.actionData.action x) (D.actionData.action y) =
        dist (D.actionData.action x) (D.actionData.action y) :=
      (W.distance_eq_krein _ _).symm
    _ = dist x y := D.actionData.isometry.dist_eq x y
    _ = kreinDistance D x y := W.distance_eq_krein _ _

def kreinOrbitCost (x y : X) : ENNReal :=
  min (ENNReal.ofReal (kreinDistance D x y))
    (min (ENNReal.ofReal (kreinDistance D x (D.actionData.action y)))
      (ENNReal.ofReal
        (kreinDistance D x (D.actionData.action (D.actionData.action y)))))

theorem kreinOrbitCost_eq_native_orbitCost (x y : X) :
    kreinOrbitCost D x y =
      InfoGeometry.Topology.OrderThreeInvariantMetricAction.orbitCost
        D.actionData x y := by
  unfold kreinOrbitCost
  simp [InfoGeometry.Topology.OrderThreeInvariantMetricAction.orbitCost,
    edist_dist, W.distance_eq_krein]

end InfoGeometry.Topology.OrderThreeKreinSpinorMetricWitness

end
