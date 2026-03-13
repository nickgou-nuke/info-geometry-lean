import InfoGeometry.Canonical.GrandUnification
import Mathlib.Analysis.InnerProductSpace.Positive

namespace InfoGeometry.Canonical.GrandUnification.JordanKKTData

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/--
The Riemannian metric at point `x` is the Hessian of the potential `K`.
In this Hilbert space setting, it is the derivative of the gradient map `gradK`.
-/
noncomputable def metric (J : JordanKKTData E) (x : E) : E →L[ℝ] E :=
  fderiv ℝ J.gradK x

/--
The metric evaluated on two tangent vectors `u` and `v`.
g_x(u, v) = ⟨D(gradK)_x(u), v⟩
-/
noncomputable def g (J : JordanKKTData E) (x : E) (u v : E) : ℝ :=
  inner ℝ (J.metric x u) v

/--
Positivity law for the Hessian metric operator.
This is the canonical operator-level convexity condition.
-/
def MetricPositive (J : JordanKKTData E) : Prop :=
  ∀ x : E, (J.metric x).IsPositive

/--
Metric symmetry derived from operator positivity.
-/
theorem metric_symmetry_of_metricPositive
    (J : JordanKKTData E)
    (hPos : MetricPositive J)
    (x u v : E) :
    J.g x u v = J.g x v u := by
  unfold g
  calc
    inner ℝ (J.metric x u) v = inner ℝ u (J.metric x v) := (hPos x).isSymmetric u v
    _ = inner ℝ (J.metric x v) u := by simp [real_inner_comm]

/--
Diagonal nonnegativity derived from operator positivity.
-/
theorem metric_nonneg_of_metricPositive
    (J : JordanKKTData E)
    (hPos : MetricPositive J)
    (x u : E) :
    0 ≤ J.g x u u := by
  unfold g
  exact (hPos x).inner_nonneg_left u

/--
Bridge theorem: the Riemannian metric is symmetric once symmetry is
provided by the concrete model.
-/
@[blueprint "thm:grand-unification-metric-symmetry"]
theorem metric_symmetry
    (J : JordanKKTData E)
    (hPos : MetricPositive J)
    (x u v : E) :
    J.g x u v = J.g x v u :=
  metric_symmetry_of_metricPositive J hPos x u v

/--
Second-order local Bregman expansion statement.

This is a formulation target for the metric layer and is intentionally left as a
proposition (no derived theorem is claimed at this layer until proved from
calculus assumptions on `J.K` / `J.gradK`).
-/
def BregmanLocalSecondOrder (J : JordanKKTData E) : Prop :=
  ∀ x u : E,
    Filter.Tendsto (fun ε : ℝ => (J.DBregman (x + ε • u) x) / (ε ^ 2))
      (nhdsWithin 0 (Set.Ioi 0))
      (nhds ((1 / 2 : ℝ) * J.g x u u))

end InfoGeometry.Canonical.GrandUnification.JordanKKTData
