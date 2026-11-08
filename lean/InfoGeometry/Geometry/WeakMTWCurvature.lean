import Mathlib

/-!
# Ma-Trudinger-Wang (MTW) Curvature Tensor and Weak MTW Condition

This module formalizes the Ma-Trudinger-Wang (MTW) cross-curvature tensor in optimal
transport and information geometry.

In Riemannian information geometry, the squared distance cost `c(x, y) = dist(x, y)² / 2`
governs optimal transport (Wasserstein-2 geometry) and defines dual affine connections.
The MTW tensor is defined as the fourth-order cross-derivative of the cost:

$$\mathfrak{S}(x, v; \xi, \eta) = -\frac{3}{2} \left.\frac{\partial^4}{\partial s^2 \partial t^2}\right|_{s=t=0} c(\exp_x(t \xi), \exp_x(v + s \eta))$$

The **Weak MTW condition** (`HasWeakMTW`) asserts that $\mathfrak{S}(x, v; \xi, \eta) \ge 0$
for all orthogonal tangent vectors $\xi \perp \eta$ at $x$ along the injectivity domain.
Under `HasWeakMTW`, the injectivity domain $I(x) \subset T_x M$ is geodesically convex,
guaranteeing global smoothness of Brenier optimal transport maps.
-/

namespace InfoGeometry.Geometry.WeakMTW

noncomputable section

open scoped Manifold ContDiff Topology
open Set Filter Manifold Bundle

abbrev Model (n : ℕ) := EuclideanSpace ℝ (Fin n)
abbrev model (n : ℕ) := 𝓘(ℝ, Model n)

variable {n : ℕ} {M : Type*} [MetricSpace M] [ChartedSpace (Model n) M]
  [IsManifold (model n) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace (model n) x)]
  [IsContMDiffRiemannianBundle (model n) ∞ (Model n)
    (fun x : M => TangentSpace (model n) x)]
  [IsRiemannianManifold (model n) M]

/-- A complete smooth geodesic `γ` through `x` with initial velocity `v`. -/
def CompleteGeodesicWithInitialData (x : M) (v : TangentSpace (model n) x)
    (γ : ℝ → M) : Prop :=
  ContMDiff 𝓘(ℝ, ℝ) (model n) ∞ γ ∧
  ∃ h : γ 0 = x,
    (h ▸ mfderiv 𝓘(ℝ, ℝ) (model n) γ 0 (1 : ℝ)) = v ∧
    ∀ t : ℝ, ∃ ε : ℝ, 0 < ε ∧
      ∀ s ∈ Metric.ball t ε, ∀ r ∈ Metric.ball t ε,
        dist (γ s) (γ r) = ‖v‖ * |s - r|

/-- Endpoint of the geodesic segment of unit length with velocity `v`. -/
def ExpEndpoint (x : M) (v : TangentSpace (model n) x) (y : M) : Prop :=
  ∃ γ : ℝ → M, CompleteGeodesicWithInitialData x v γ ∧ γ 1 = y

/-- The Riemannian exponential map `exp_x(v)`. -/
noncomputable def exp (x : M) (v : TangentSpace (model n) x) : M := by
  classical
  exact if h : ∃ y, ExpEndpoint x v y then Classical.choose h else x

/-- The injectivity domain in the tangent space `T_x M`: vectors `v` where the ray strictly minimizes distance beyond `1`. -/
def injectivityDomain (x : M) : Set (TangentSpace (model n) x) :=
  {v | ∃ a : ℝ, 1 < a ∧ dist x (exp x (a • v)) = a * ‖v‖}

/-- The squared distance transport cost function `c(x, y) = dist(x, y)² / 2`. -/
def cost (x y : M) : ℝ := dist x y ^ 2 / 2

/-- The Ma-Trudinger-Wang (MTW) cross-curvature tensor $\mathfrak{S}(x, v; \xi, \eta)$. -/
noncomputable def mtw (x : M) (v ξ η : TangentSpace (model n) x) : ℝ :=
  -(3 / 2 : ℝ) * deriv (fun s : ℝ =>
    deriv (fun s' : ℝ => deriv (fun t : ℝ =>
      deriv (fun t' : ℝ => cost (exp x (t' • ξ)) (exp x (v + s' • η))) t) 0) s) 0

/-- The weak MTW condition: non-negativity of the MTW tensor on orthogonal directions $\xi \perp \eta$. -/
def HasWeakMTW : Prop :=
  ∀ (x : M) (v : TangentSpace (model n) x), v ∈ injectivityDomain x →
    ∀ ξ η : TangentSpace (model n) x, inner ℝ ξ η = 0 → 0 ≤ mtw x v ξ η

/-- Main theorem statement: weak MTW curvature implies geodesic convexity of the injectivity domain. -/
def MainConvexity : Prop :=
  ∀ x : M, Convex ℝ (injectivityDomain (n := n) x)

end

end InfoGeometry.Geometry.WeakMTW
