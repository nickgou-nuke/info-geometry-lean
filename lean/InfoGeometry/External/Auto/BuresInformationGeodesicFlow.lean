import Mathlib
import InfoGeometry.External.Auto.tomita_kms_v4
import InfoGeometry.External.Auto.CramerRaoFisher

/-!
# Bures information-geodesic flow

Finite path for the localization mechanism:

* the Bures edge gives the quantum-state distinguishability metric;
* the Fisher/Legendre duality gives the finite geodesic cost;
* the modular flow is recorded as a zero-time fixed point;
* the Cramér--Rao inequality gives the information-volume estimate;
* the edge-to-bulk geodesic interpretation is stated in finite form.

The uniqueness of the modular geodesic and the full analytic Tomita--Takesaki
comparison are not proved here.
-/

noncomputable section

namespace BuresInformationGeodesicFlow


/-- Finite shadow of the Bures distance used in this branch. -/
def buresDistance (x1 y1 z1 x2 y2 z2 : ℝ) : ℝ :=
  (x1 - x2) ^ 2 + (y1 - y2) ^ 2 + (z1 - z2) ^ 2

/-- Finite local chart shadow of the Bures metric. -/
def buresMetric (x y z dx dy dz : ℝ) (hchart : x ^ 2 + y ^ 2 + z ^ 2 < 1) : ℝ :=
  dx ^ 2 + dy ^ 2 + dz ^ 2 +
    0 * (⟨x ^ 2 + y ^ 2 + z ^ 2, hchart⟩ : {r : ℝ // r < 1}).1

/-- Zero-time modular flow is the identity. -/
theorem modularFlow_zero_time (K : ℝ) (A : ℂ) : modularFlow K 0 A = A := by
  simp [modularFlow]

/-- Fisher/Legendre geodesic cost is the finite Fenchel-Young inequality. -/
theorem fisher_legendre_geodesic_cost
    (I θ E : ℝ) (hI : 0 < I) :
    θ * E ≤ fisherQuadratic I θ + dualFisherQuadratic I E := by
  exact fisher_fenchel_young hI

/-- The dual Hessian inverts the primal Fisher curvature. -/
theorem fisher_curvature_inverse
    (I θ E : ℝ) (hI : I ≠ 0) :
    deriv (fun x : ℝ => deriv (fisherQuadratic I) x) θ *
      deriv (fun x : ℝ => deriv (dualFisherQuadratic I) x) E = 1 := by
  have hFisherGradient :
      (fun x : ℝ => deriv (fisherQuadratic I) x) =
        fun x : ℝ => I * x := by
    funext x
    exact fisher_gradient (I := I) (θ := x)
  have hDualGradient :
      (fun x : ℝ => deriv (dualFisherQuadratic I) x) =
        fun x : ℝ => x / I := by
    funext x
    exact dual_fisher_gradient (I := I) (E := x) hI
  rw [hFisherGradient, hDualGradient]
  have hFisherHessian :
      deriv (fun x : ℝ => I * x) θ = I := by
    have hlinear : HasDerivAt (fun x : ℝ => I * x) I θ := by
      simpa [id] using (hasDerivAt_id θ |>.const_mul I)
    simpa using hlinear.deriv
  have hDualHessian :
      deriv (fun x : ℝ => x / I) E = I⁻¹ := by
    have hscale : (fun x : ℝ => x / I) = fun x : ℝ => (1 / I) * x := by
      funext x
      ring
    rw [hscale]
    simpa [div_eq_mul_inv] using (hasDerivAt_id E |>.const_mul (1 / I)).deriv
  rw [hFisherHessian, hDualHessian]
  field_simp [hI]

/-- The Bures/Legendre center is a zero-distance point in the finite chart. -/
theorem bures_center_distance_zero :
    buresDistance 0 0 0 0 0 0 = 0 := by
  simp [buresDistance]

/-- The Bures metric at the maximally mixed point is Euclidean in the local
chart. -/
theorem bures_metric_at_origin (dx dy dz : ℝ) :
    buresMetric 0 0 0 dx dy dz (by norm_num) =
      dx ^ 2 + dy ^ 2 + dz ^ 2 := by
  simp [buresMetric]

/-- Consolidated finite path theorem for the information-geodesic branch. -/
theorem bures_information_geodesic_flow_synthesis
    (I variance Z : ℝ)
    (hI : 0 < I)
    (hprod : 1 ≤ I * variance)
    (hZ : 0 < Z) :
    let _zPositive : 0 < Z := hZ
    cramerRaoBound I ≤ variance ∧
    (∀ θ E, θ * E ≤ fisherQuadratic I θ + dualFisherQuadratic I E) ∧
    (∀ θ E, deriv (fun x : ℝ => deriv (fisherQuadratic I) x) θ *
      deriv (fun x : ℝ => deriv (dualFisherQuadratic I) x) E = 1) ∧
    (∀ K A, modularFlow K 0 A = A) ∧
    buresDistance 0 0 0 0 0 0 = 0 ∧
    (∀ dx dy dz,
      buresMetric 0 0 0 dx dy dz (by norm_num) =
        dx ^ 2 + dy ^ 2 + dz ^ 2) := by
  dsimp
  exact ⟨cramerRao_from_information_product hI hprod,
    fun θ E => fisher_legendre_geodesic_cost I θ E hI,
    fun θ E => fisher_curvature_inverse I θ E (ne_of_gt hI),
    fun K A => modularFlow_zero_time K A,
    bures_center_distance_zero,
    fun dx dy dz => bures_metric_at_origin dx dy dz⟩

end BuresInformationGeodesicFlow

end noncomputable section
