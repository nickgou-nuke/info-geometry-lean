import InfoGeometry.Convex.HessianGeometry
import Mathlib.Analysis.InnerProductSpace.Calculus

namespace InfoGeometry.Convex.Euclidean

open InfoGeometry.Convex

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/--
The Euclidean quadratic potential `ψ(x) = 1/2 ⟪x, x⟫`.
Its Bregman divergence is half the squared Euclidean distance.
-/
noncomputable def potential (x : E) : ℝ :=
  (1 / 2 : ℝ) * inner ℝ x x

/-- The Euclidean gradient is the identity map. -/
noncomputable def grad (x : E) : E := x

lemma hasFDerivAt_potential (x : E) :
    HasFDerivAt potential (InnerProductSpace.toDual ℝ E (grad x)) x := by
  unfold potential grad
  have h_id : HasFDerivAt (fun y : E => y) (1 : E →L[ℝ] E) x := by
    simpa using (hasFDerivAt_id x)
  have h_inner :
      HasFDerivAt (fun y : E => inner ℝ y y)
        ((fderivInnerCLM ℝ (x, x)).comp ((1 : E →L[ℝ] E).prod (1 : E →L[ℝ] E))) x :=
    h_id.inner ℝ h_id
  convert h_inner.const_smul (1 / 2 : ℝ) using 1
  ext v
  rw [ContinuousLinearMap.smul_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.prod_apply, fderivInnerCLM_apply]
  simp [InnerProductSpace.toDual_apply_apply, real_inner_comm]
  ring

omit [CompleteSpace E] in
lemma divergence_form_eq_half_sqdist (x y : E) :
    potential x - potential y - inner ℝ (grad y) (x - y) =
      (1 / 2 : ℝ) * inner ℝ (x - y) (x - y) := by
  unfold potential grad
  simp [inner_sub_right, real_inner_comm]
  rw [norm_sub_sq_real]
  ring_nf

omit [CompleteSpace E] in
lemma divergence_form_nonneg (x y : E) :
    0 ≤ potential x - potential y - inner ℝ (grad y) (x - y) := by
  rw [divergence_form_eq_half_sqdist]
  exact mul_nonneg (by norm_num) real_inner_self_nonneg

/-- Euclidean space as a Hessian geometry. -/
noncomputable def hessianGeometry : HessianGeometry E where
  potential := potential
  grad := grad
  has_gradient := hasFDerivAt_potential
  divergence_nonneg_axiom := divergence_form_nonneg

@[simp] theorem grad_eq_id (x : E) :
    hessianGeometry.grad x = x := rfl

@[simp] theorem metricOp_eq_id (x : E) :
    hessianGeometry.metricOp x = ContinuousLinearMap.id ℝ E := by
  ext v
  change (fderiv ℝ grad x) v = v
  change (fderiv ℝ (fun y : E => y) x) v = v
  simp

/-- The Euclidean Bregman divergence is half the squared Euclidean distance. -/
theorem divergence_eq_half_sqdist (x y : E) :
    hessianGeometry.divergence x y =
      (1 / 2 : ℝ) * inner ℝ (x - y) (x - y) := by
  simpa [HessianGeometry.divergence, HessianGeometry.dualMap, hessianGeometry] using
    divergence_form_eq_half_sqdist x y

/--
The Euclidean Bregman interaction score decomposes into the dot product minus
query and key quadratic penalties.
-/
theorem neg_divergence_eq_dot_minus_half_norms (q k : E) :
    -hessianGeometry.divergence q k =
      inner ℝ q k - (1 / 2 : ℝ) * inner ℝ q q - (1 / 2 : ℝ) * inner ℝ k k := by
  rw [divergence_eq_half_sqdist, real_inner_self_eq_norm_sq (q - k),
    real_inner_self_eq_norm_sq q, real_inner_self_eq_norm_sq k, norm_sub_sq_real]
  ring_nf

end InfoGeometry.Convex.Euclidean
