import InfoGeometry.Canonical.JordanKKTData
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Canonical.GrandUnification
import Mathlib.Analysis.InnerProductSpace.Positive
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import Mathlib.Analysis.Calculus.FDeriv.Linear
import Mathlib.Analysis.Asymptotics.Lemmas
set_option linter.unnecessarySimpa false

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
The Information Metric is the second-order analytic limit of the Bregman
divergence along rays, obtained by Taylor expansion with remainder.
-/
theorem bregman_local_second_order_of_logDet
    (J : JordanKKTData E)
    (hTwiceDiff : ContDiff ℝ 2 J.K) :
    ∀ x u : E,
      Filter.Tendsto (fun ε : ℝ => (J.DBregman (x + ε • u) x) / (ε ^ 2))
        (nhdsWithin 0 (Set.Ioi 0))
        (nhds ((1 / 2 : ℝ) * J.g x u u)) := by
  intro x u
  let f' : E → E →L[ℝ] ℝ := fun y => InnerProductSpace.toDual ℝ E (J.gradK y)
  let f'' : E →L[ℝ] E →L[ℝ] ℝ :=
    (InnerProductSpace.toDualMap ℝ E).toContinuousLinearMap.comp (J.metric x)

  have hKdiff : DifferentiableAt ℝ J.K x :=
    (hTwiceDiff.contDiffAt).differentiableAt (by simp)
  have hKfderivAt : HasFDerivAt J.K (fderiv ℝ J.K x) x := hKdiff.hasFDerivAt
  have hgrad_match : f' x = fderiv ℝ J.K x := by
    change InnerProductSpace.toDual ℝ E (J.gradK x) = fderiv ℝ J.K x
    exact (J.hasFDerivAt_K x).unique hKfderivAt
  have hlin_eval : f' x u = (fderiv ℝ J.K x) u := by
    simpa [hgrad_match]

  have hf : ∀ z ∈ interior (Set.univ : Set E), HasFDerivAt J.K (f' z) z := by
    intro z hz
    simpa [f'] using J.hasFDerivAt_K z

  have hxGrad : HasFDerivAt J.gradK (J.metric x) x := by
    simpa [metric] using (J.has_hessian x).hasFDerivAt
  have hx : HasFDerivWithinAt f' f'' (interior (Set.univ : Set E)) x := by
    have hx0 : HasFDerivAt f' f'' x := by
      simpa [f', f''] using
        ((InnerProductSpace.toDualMap ℝ E).toContinuousLinearMap.hasFDerivAt.comp x hxGrad)
    exact hx0.hasFDerivWithinAt

  have hlin_eval' : (fderiv ℝ J.K x) u = inner ℝ (J.gradK x) u := by
    calc
      (fderiv ℝ J.K x) u = (f' x) u := by
        simpa [hgrad_match]
      _ = inner ℝ (J.gradK x) u := by
        simp [f', InnerProductSpace.toDual_apply_apply]

  have hTail :
      (fun h : ℝ =>
        J.K (x + h • (0 : E) + h • u)
          - J.K (x + h • (0 : E))
          - h • (f' x u)
          - h ^ 2 • (f'' (0 : E) u)
          - (h ^ 2 / 2) • (f'' u u)) =o[nhdsWithin (0 : ℝ) (Set.Ioi 0)] fun h => h ^ 2 := by
    have hv : x + (0 : E) ∈ interior (Set.univ : Set E) := by simp
    have hw : x + (0 : E) + u ∈ interior (Set.univ : Set E) := by simp
    simpa using
      (convex_univ : Convex ℝ (Set.univ : Set E)).taylor_approx_two_segment
        (f := J.K) (f' := f') (f'' := f'')
        (hf := hf) (xs := by simp) (hx := hx) (x := x)
        (v := (0 : E)) (w := u) hv hw

  have hTail' :
      (fun h : ℝ =>
        J.DBregman (x + h • u) x - (h ^ 2 / 2) * J.g x u u)
        =o[nhdsWithin (0 : ℝ) (Set.Ioi 0)] fun h => h ^ 2 := by
    simpa [f', f'', hlin_eval, JordanKKTData.DBregman, g, metric,
      sub_eq_add_neg, add_assoc, add_left_comm, add_comm, inner_smul_right, mul_comm, mul_left_comm,
      mul_assoc, hlin_eval'] using hTail

  have hDiv :
      Filter.Tendsto
        (fun h : ℝ => (J.DBregman (x + h • u) x - (h ^ 2 / 2) * J.g x u u) / (h ^ 2))
        (nhdsWithin 0 (Set.Ioi 0))
        (nhds 0) := by
    simpa [div_eq_mul_inv] using hTail'.tendsto_div_nhds_zero

  have hEq :
      (fun h : ℝ => J.DBregman (x + h • u) x / (h ^ 2))
        =ᶠ[nhdsWithin 0 (Set.Ioi 0)]
          (fun h : ℝ =>
            (1 / 2 : ℝ) * J.g x u u +
              (J.DBregman (x + h • u) x - (h ^ 2 / 2) * J.g x u u) / (h ^ 2)) := by
    filter_upwards [self_mem_nhdsWithin] with h hh
    have hne : h ≠ 0 := ne_of_gt hh
    field_simp [hne]
    ring

  have hSum :
      Filter.Tendsto
        (fun h : ℝ =>
          (1 / 2 : ℝ) * J.g x u u +
            (J.DBregman (x + h • u) x - (h ^ 2 / 2) * J.g x u u) / (h ^ 2))
        (nhdsWithin 0 (Set.Ioi 0))
        (nhds ((1 / 2 : ℝ) * J.g x u u)) := by
    simpa using (tendsto_const_nhds.add hDiv)
  exact hSum.congr' hEq.symm

end InfoGeometry.Canonical.GrandUnification.JordanKKTData
