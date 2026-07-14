import InfoGeometry.Convex.HessianGeometry
import Mathlib.Analysis.InnerProductSpace.Calculus

namespace Euclidean

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

/-- Scaled Euclidean quadratic potential `ψ_c(x) = c * ψ(x)`. -/
noncomputable def scaledPotential (c : ℝ) (x : E) : ℝ :=
  c * potential x

/-- Gradient of the scaled Euclidean quadratic potential. -/
noncomputable def scaledGrad (c : ℝ) (x : E) : E :=
  c • x

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

lemma hasFDerivAt_scaledPotential (c : ℝ) (x : E) :
    HasFDerivAt (scaledPotential c) (InnerProductSpace.toDual ℝ E (scaledGrad c x)) x := by
  simpa [scaledPotential, scaledGrad, potential, grad, InnerProductSpace.toDual_apply_apply,
    real_inner_smul_left, mul_comm, mul_left_comm, mul_assoc]
    using (hasFDerivAt_potential (E := E) x).const_smul c

omit [CompleteSpace E] in
lemma divergence_form_eq_half_sqdist (x y : E) :
    potential x - potential y - inner ℝ (grad y) (x - y) =
      (1 / 2 : ℝ) * inner ℝ (x - y) (x - y) := by
  unfold potential grad
  simp [inner_sub_right, real_inner_comm]
  rw [norm_sub_sq_real]
  ring_nf

omit [CompleteSpace E] in
lemma scaled_divergence_form_eq_scaled_half_sqdist (c : ℝ) (x y : E) :
    scaledPotential c x - scaledPotential c y - inner ℝ (scaledGrad c y) (x - y) =
      c * ((1 / 2 : ℝ) * inner ℝ (x - y) (x - y)) := by
  calc
    scaledPotential c x - scaledPotential c y - inner ℝ (scaledGrad c y) (x - y)
        = c * (potential x - potential y - inner ℝ (grad y) (x - y)) := by
          unfold scaledPotential scaledGrad potential grad
          simp [inner_smul_left]
          ring
    _ = c * ((1 / 2 : ℝ) * inner ℝ (x - y) (x - y)) := by
      rw [divergence_form_eq_half_sqdist (E := E) x y]

omit [CompleteSpace E] in
lemma divergence_form_nonneg (x y : E) :
    0 ≤ potential x - potential y - inner ℝ (grad y) (x - y) := by
  rw [divergence_form_eq_half_sqdist]
  exact mul_nonneg (by norm_num) real_inner_self_nonneg

omit [CompleteSpace E] in
lemma scaled_divergence_form_nonneg (c : ℝ) (hc : 0 ≤ c) (x y : E) :
    0 ≤ scaledPotential c x - scaledPotential c y - inner ℝ (scaledGrad c y) (x - y) := by
  rw [scaled_divergence_form_eq_scaled_half_sqdist]
  exact mul_nonneg hc (mul_nonneg (by norm_num) real_inner_self_nonneg)

/-- Euclidean space as a Hessian geometry. -/
noncomputable def hessianGeometry : HessianGeometry E where
  potential := potential
  grad := grad
  has_gradient := hasFDerivAt_potential
  divergence_form_nonneg := divergence_form_nonneg

@[simp] theorem grad_eq_id (x : E) :
    hessianGeometry.grad x = x := rfl

@[simp] theorem metricOp_eq_id (x : E) :
    hessianGeometry.metricOp x = ContinuousLinearMap.id ℝ E := by
  ext v
  change (fderiv ℝ grad x) v = v
  change (fderiv ℝ (fun y : E => y) x) v = v
  simp

/-- Euclidean space with a nonnegative scalar quadratic weight as a Hessian geometry. -/
noncomputable def scaledHessianGeometry (c : ℝ) (hc : 0 ≤ c) : HessianGeometry E where
  potential := scaledPotential c
  grad := scaledGrad c
  has_gradient := hasFDerivAt_scaledPotential (E := E) c
  divergence_form_nonneg := scaled_divergence_form_nonneg (E := E) c hc

@[simp] theorem scaledHessianGeometry_grad_eq_smul
    (c : ℝ) (hc : 0 ≤ c) (x : E) :
    (scaledHessianGeometry (E := E) c hc).grad x = c • x := rfl

-- theorem-class: derived
/-- The scaled Euclidean Hessian geometry has constant metric operator `c • Id`. -/
@[simp] theorem scaledHessianGeometry_metricOp_eq_smul_id
    (c : ℝ) (hc : 0 ≤ c) (x : E) :
    (scaledHessianGeometry (E := E) c hc).metricOp x =
      c • ContinuousLinearMap.id ℝ E := by
  ext v
  have hfd :
      fderiv ℝ (fun y : E => c • y) x = c • fderiv ℝ (fun y : E => y) x := by
    exact congrArg (fun F => F x)
      (fderiv_const_smul_field (𝕜 := ℝ) (R := ℝ) (F := E) (f := fun y : E => y) (c := c))
  have hv := congrArg (fun A : E →L[ℝ] E => A v) hfd
  simpa [ContinuousLinearMap.smul_apply] using hv

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

end Euclidean
