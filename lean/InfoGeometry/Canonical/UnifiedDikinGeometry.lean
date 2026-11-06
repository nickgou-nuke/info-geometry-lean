/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Topology.Algebra.Module.Basic
import InfoGeometry.Geometry.LegendreDifferential

open InfoGeometry.Geometry.LegendreDifferential

/-!
# Unified Dikin Geometry Framework — Core Type Classes & 1D Hessian Bridge

This file integrates the polyphyletic "Dikin" lineage into a single type-class
hierarchy, capturing the shared information-geometric pattern:

> A convex barrier potential `Φ` → its Hessian defines a local quadratic metric `g` →
> the sublevel set `{y | g_x(y - x) ≤ r²}` is a "Dikin ellipsoid" that confines
> trajectories away from the barrier boundary.

Hierarchy:
- `DikinMetric E`   : quadratic form `dikin_metric : E → E → ℝ` + ellipsoid
- `DikinBarrier E`  : extends `DikinMetric`; barrier `dikin_barrier : E → ℝ`
                      with law `dikin_metric x v = hessianMap dikin_barrier x v v`
- `DikinGeometry E` : extends `DikinBarrier`; includes unit-ellipsoid center membership

No `sorry`, `admit`, or axioms beyond `propext`, `Classical.choice`, and `Quot.sound`.
-/

noncomputable section

/-- Base class: a Dikin metric (positive-definite quadratic form) on a normed
`ℝ`-vector space `E`, together with its associated Dikin ellipsoids.

`dikin_metric x v` is the value of the local quadratic metric `g_x` at tangent
vector `v`. It must satisfy `g_x(0) = 0` and `g_x(v) > 0` for `v ≠ 0`.
`dikin_ellipsoid x r` is the sublevel set `{y | g_x(y - x) ≤ r²}`. -/
class DikinMetric (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E] where
  dikin_metric : E → E → ℝ
  dikin_ellipsoid : E → ℝ → Set E
  dikin_metric_zero : ∀ (x : E), dikin_metric x 0 = 0
  dikin_metric_pos : ∀ {x v : E}, v ≠ 0 → 0 < dikin_metric x v
  dikin_ellipsoid_def : ∀ (x : E) (r : ℝ),
    dikin_ellipsoid x r = {y : E | dikin_metric x (y - x) ≤ r ^ 2}

namespace DikinMetric

/-- The center of a Dikin ellipsoid always belongs to its own ellipsoid (for `r ≥ 0`). -/
theorem dikin_ellipsoid_center_mem {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [self : DikinMetric E] (x : E) {r : ℝ} (hr : (0 : ℝ) ≤ r) :
    x ∈ self.dikin_ellipsoid x r := by
  rw [self.dikin_ellipsoid_def x r]
  change self.dikin_metric x (x - x) ≤ r ^ 2
  rw [sub_self, self.dikin_metric_zero x, sq]
  exact mul_nonneg hr hr

/-- Larger radius gives a larger (or equal) Dikin ellipsoid. -/
theorem dikin_ellipsoid_mono_radius {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [self : DikinMetric E] {x : E} {r s : ℝ} (hrs : r ^ 2 ≤ s ^ 2) :
    self.dikin_ellipsoid x r ⊆ self.dikin_ellipsoid x s := by
  intro y hy
  rw [self.dikin_ellipsoid_def x r] at hy
  rw [self.dikin_ellipsoid_def x s]
  exact le_trans hy hrs

/-- Positive definiteness: `g_x(v) = 0` iff `v = 0`. -/
theorem dikin_metric_pos_iff {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [self : DikinMetric E] {x v : E} :
    dikin_metric x v = 0 ↔ v = 0 := by
  constructor
  · intro h
    by_contra h₁
    have h₃ : 0 < self.dikin_metric x v := self.dikin_metric_pos h₁
    linarith [h, h₃]
  · intro h
    rw [h]
    exact self.dikin_metric_zero x

end DikinMetric

/-- A Dikin metric that arises as the Hessian of a convex barrier potential.

`dikin_barrier : E → ℝ` is the potential `Φ`, with the compatibility law that its
Hessian equals the Dikin metric:
`g_x(v) = Hessian(Φ)_x(v, v)`. -/
class DikinBarrier (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E]
    extends DikinMetric E where
  dikin_barrier : E → ℝ
  dikin_barrier_hessian_metric :
    ∀ (x v : E), dikin_metric x v = hessianMap dikin_barrier x v v

namespace DikinBarrier

/-- The barrier's Dikin metric at `x` is the Hessian quadratic form of the barrier. -/
theorem dikin_metric_eq_hessian {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [self : DikinBarrier E] (x v : E) :
    self.dikin_metric x v = hessianMap self.dikin_barrier x v v :=
  self.dikin_barrier_hessian_metric x v

end DikinBarrier

/-- The full Dikin geometry package: a metric together with its barrier potential
and unit-ellipsoid center containment. -/
class DikinGeometry (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E]
    extends DikinBarrier E where
  unit_ellipsoid_center_mem : ∀ (x : E), x ∈ dikin_ellipsoid x 1

/-- A continuous linear map `f : E →L[ℝ] F` is a Dikin morphism when it preserves the Dikin
metric:
`g_F(f x, f v) = g_E(x, v)`. -/
def DikinMorphism {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    [DikinMetric E] [DikinMetric F]
    (f : E →L[ℝ] F) : Prop :=
  ∀ (x v : E),
    DikinMetric.dikin_metric (f x) (f v) = DikinMetric.dikin_metric x v

/-- A Dikin morphism sends Dikin ellipsoids into Dikin ellipsoids of the same radius. -/
theorem DikinMorphism_map_ellipsoid {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    [instE : DikinMetric E] [instF : DikinMetric F]
    {f : E →L[ℝ] F} (hf : DikinMorphism f) (x : E) (r : ℝ) :
    f '' (DikinMetric.dikin_ellipsoid x r) ⊆ DikinMetric.dikin_ellipsoid (f x) r := by
  intro y hy
  rcases hy with ⟨z, hz_mem, rfl⟩
  rw [instE.dikin_ellipsoid_def x r] at hz_mem
  rw [instF.dikin_ellipsoid_def (f x) r]
  change instF.dikin_metric (f x) (f z - f x) ≤ r ^ 2
  rw [← f.map_sub, hf x (z - x)]
  exact hz_mem

/-!
## 1D Fréchet Hessian Evaluation Bridge (`hessianMap_real_of_hasDerivAt`)
-/

/-- **1D Hessian Bridge**:
If `Φ : ℝ → ℝ` has first derivative `g y` for all `y` in a neighborhood of `x`, and `g` has
derivative `h` at `x`, then `hessianMap Φ x v v = h * v ^ 2`. -/
theorem hessianMap_real_of_hasDerivAt
    {Φ g : ℝ → ℝ} {h x : ℝ}
    (hΦ : ∀ᶠ y in nhds x, HasDerivAt Φ (g y) y)
    (hg : HasDerivAt g h x) (v : ℝ) :
    hessianMap Φ x v v = h * v ^ 2 := by
  let L : ℝ →L[ℝ] (ℝ →L[ℝ] ℝ) :=
    ContinuousLinearMap.smulRightL ℝ ℝ ℝ (ContinuousLinearMap.id ℝ ℝ)
  have hLegEq : legendreMap Φ =ᶠ[nhds x] (L ∘ g) := by
    filter_upwards [hΦ] with y hy
    dsimp [legendreMap, L]
    exact hy.hasFDerivAt.fderiv
  have hgF : HasFDerivAt g (ContinuousLinearMap.smulRight (1 : ℝ →L[ℝ] ℝ) h) x :=
    hg.hasFDerivAt
  have hComp :
      HasFDerivAt (L ∘ g)
        (L.comp (ContinuousLinearMap.smulRight (1 : ℝ →L[ℝ] ℝ) h)) x :=
    (L.hasFDerivAt).comp x hgF
  have hLegF :
      HasFDerivAt (legendreMap Φ)
        (L.comp (ContinuousLinearMap.smulRight (1 : ℝ →L[ℝ] ℝ) h)) x :=
    hComp.congr_of_eventuallyEq hLegEq
  have hHess := hessianMap_eq_of_hasFDerivAt_legendreMap hLegF
  rw [hHess]
  simp [L]
  ring

/-!
## Constructive Model Witnesses for `DikinMetric`, `DikinBarrier`, and `DikinGeometry`
-/

/-- Standard Euclidean quadratic barrier `Φ₀(x) = x² / 2` on `ℝ`. -/
def euclideanQuadBarrier (x : ℝ) : ℝ := x ^ 2 / 2

/-- Standard Euclidean quadratic metric `g₀(x, v) = v²` on `ℝ`. -/
def euclideanQuadMetric (_x v : ℝ) : ℝ := v ^ 2

theorem euclideanQuadBarrier_hessian (x v : ℝ) :
    hessianMap euclideanQuadBarrier x v v = v ^ 2 := by
  have hΦ : ∀ᶠ y in nhds x, HasDerivAt euclideanQuadBarrier y y := by
    refine Filter.Eventually.of_forall (fun y => ?_)
    have h1 : HasDerivAt (fun t : ℝ => t ^ 2) (2 * y ^ (2 - 1)) y := hasDerivAt_pow 2 y
    have h2 : HasDerivAt (fun t : ℝ => t ^ 2 / 2) ((2 * y ^ (2 - 1)) / 2) y := h1.div_const 2
    have hEq : (2 * y ^ (2 - 1)) / 2 = y := by ring
    rwa [hEq] at h2
  have hg : HasDerivAt (fun y : ℝ => y) 1 x := hasDerivAt_id x
  have hH := hessianMap_real_of_hasDerivAt hΦ hg v
  linarith [hH]

/-- Constructive model witness for `DikinMetric ℝ`. -/
@[instance_reducible]
def euclideanDikinMetricModel : DikinMetric ℝ where
  dikin_metric := euclideanQuadMetric
  dikin_ellipsoid := fun x r => {y : ℝ | euclideanQuadMetric x (y - x) ≤ r ^ 2}
  dikin_metric_zero := fun _ => by simp [euclideanQuadMetric]
  dikin_metric_pos := fun {_ v} hv => sq_pos_of_ne_zero hv
  dikin_ellipsoid_def := fun _ _ => rfl

/-- Constructive model witness for `DikinBarrier ℝ`. -/
@[instance_reducible]
def euclideanDikinBarrierModel : DikinBarrier ℝ where
  toDikinMetric := euclideanDikinMetricModel
  dikin_barrier := euclideanQuadBarrier
  dikin_barrier_hessian_metric := fun x v => (euclideanQuadBarrier_hessian x v).symm

/-- Constructive model witness for `DikinGeometry ℝ`. -/
@[instance_reducible]
def euclideanDikinGeometryModel : DikinGeometry ℝ where
  toDikinBarrier := euclideanDikinBarrierModel
  unit_ellipsoid_center_mem := fun x => by
    let _ : DikinMetric ℝ := euclideanDikinMetricModel
    exact DikinMetric.dikin_ellipsoid_center_mem x zero_le_one

end
