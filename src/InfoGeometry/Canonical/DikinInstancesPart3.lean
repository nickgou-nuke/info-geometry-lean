/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Canonical.UnifiedDikinGeometry
import InfoGeometry.Canonical.DikinInstances
import InfoGeometry.Canonical.DikinInstancesPart2
import InfoGeometry.Quantum.DikinSouriauTrap

open InfoGeometry.Geometry.LegendreDifferential

/-!
# Dikin Barrier Instances (Part 3: Souriau/Apollonius and Orbit Hessian Compatibility)

Maps Dikin metrics to their barrier potentials via the `DikinBarrier` and `DikinGeometry`
type classes, proving the exact Fréchet Hessian compatibility law:
`g_x(v) = hessianMap barrier x v v`.

Lineages integrated:
1. Souriau/Apollonius on `ℝ`: `souriauBarrier ξ = 2 * log (cosh ξ)`,
   `souriauDikinMetric ξ v = (2 / cosh² ξ) * v²`.
2. Orbit on `ℝ₊`: `orbitBarrier x = -log x`,
   `orbitDikinMetric x v = (1 / x²) * v²`.

No `sorry`, `admit`, or axioms beyond `propext`, `Classical.choice`, and `Quot.sound`.
-/

noncomputable section

/-! ### 1. Souriau/Apollonius Barrier on `ℝ` -/

/-- The Souriau/Apollonius barrier potential: `Φ(ξ) = 2 * log (cosh ξ)`. -/
def souriauBarrier (ξ : ℝ) : ℝ :=
  2 * Real.log (Real.cosh ξ)

/-- **Theorem (`souriauBarrier_hessian_metric`)**:
The Fréchet Hessian of `souriauBarrier` at `ξ` evaluated on `(v, v)` equals the Souriau Dikin
metric `(2 / cosh² ξ) * v²`. -/
theorem souriauBarrier_hessian_metric (ξ v : ℝ) :
    hessianMap souriauBarrier ξ v v = (2 / Real.cosh ξ ^ 2) * v ^ 2 := by
  have hΦ : ∀ᶠ y in nhds ξ,
      HasDerivAt souriauBarrier (2 * (Real.sinh y / Real.cosh y)) y := by
    refine Filter.Eventually.of_forall (fun y => ?_)
    have hCosh : HasDerivAt Real.cosh (Real.sinh y) y := Real.hasDerivAt_cosh y
    have hLog : HasDerivAt (fun t => Real.log (Real.cosh t)) (Real.sinh y / Real.cosh y) y :=
      hCosh.log (Real.cosh_pos y).ne'
    exact hLog.const_mul 2
  have hg : HasDerivAt (fun y => 2 * (Real.sinh y / Real.cosh y))
      (2 / Real.cosh ξ ^ 2) ξ := by
    have hQuot : HasDerivAt (fun y => Real.sinh y / Real.cosh y)
        ((Real.cosh ξ * Real.cosh ξ - Real.sinh ξ * Real.sinh ξ) / Real.cosh ξ ^ 2) ξ :=
      (Real.hasDerivAt_sinh ξ).div (Real.hasDerivAt_cosh ξ) (Real.cosh_pos ξ).ne'
    have hMul := hQuot.const_mul 2
    have hSimp :
        2 * ((Real.cosh ξ * Real.cosh ξ - Real.sinh ξ * Real.sinh ξ) / Real.cosh ξ ^ 2) =
          2 / Real.cosh ξ ^ 2 := by
      have hSq : Real.cosh ξ * Real.cosh ξ - Real.sinh ξ * Real.sinh ξ = 1 := by
        calc
          Real.cosh ξ * Real.cosh ξ - Real.sinh ξ * Real.sinh ξ
              = Real.cosh ξ ^ 2 - Real.sinh ξ ^ 2 := by ring
          _ = 1 := Real.cosh_sq_sub_sinh_sq ξ
      rw [hSq]
      ring
    rwa [hSimp] at hMul
  exact hessianMap_real_of_hasDerivAt hΦ hg v

instance instDikinBarrierReal : DikinBarrier ℝ where
  dikin_barrier := souriauBarrier
  dikin_barrier_hessian_metric := fun ξ v =>
    (souriauBarrier_hessian_metric ξ v).symm

instance instDikinGeometryReal : DikinGeometry ℝ where
  toDikinBarrier := instDikinBarrierReal
  unit_ellipsoid_center_mem := fun ξ =>
    DikinMetric.dikin_ellipsoid_center_mem ξ zero_le_one

/-- The Souriau barrier equals the Apollonius barrier:
`souriauBarrier ξ = -Real.log (1 - Real.tanh ξ ^ 2)`. -/
theorem souriauBarrier_eq_apolloniusBarrier (ξ : ℝ) :
    souriauBarrier ξ = -Real.log (1 - Real.tanh ξ ^ 2) :=
  InfoGeometry.Quantum.DikinSouriauTrap.dikin_barrier_eq_neg_log_one_sub_tanh_sq ξ

/-! ### 2. Orbit Barrier on `ℝ₊` -/

/-- The Orbit barrier potential: `Φ(x) = -log x`. -/
def orbitBarrier (x : ℝ) : ℝ :=
  -Real.log x

/-- **Theorem (`orbitBarrier_hessian_metric`)**:
For `0 < x`, the Fréchet Hessian of `orbitBarrier` at `x` evaluated on `(v, v)` equals
`(1 / x²) * v²`. -/
theorem orbitBarrier_hessian_metric (x v : ℝ) (hx : 0 < x) :
    hessianMap orbitBarrier x v v = (1 / x ^ 2) * v ^ 2 := by
  have hΦ : ∀ᶠ y in nhds x, HasDerivAt orbitBarrier (-y⁻¹) y := by
    filter_upwards [Ioi_mem_nhds hx] with y hy
    exact (Real.hasDerivAt_log (ne_of_gt hy)).neg
  have hg : HasDerivAt (fun y : ℝ => -y⁻¹) (1 / x ^ 2) x := by
    have hInv : HasDerivAt Inv.inv (-(x ^ 2)⁻¹) x := hasDerivAt_inv (ne_of_gt hx)
    have hNeg := hInv.neg
    have hEq : -(-(x ^ 2)⁻¹) = 1 / x ^ 2 := by ring
    rwa [hEq] at hNeg
  exact hessianMap_real_of_hasDerivAt hΦ hg v

/-- The orbit Dikin metric equals the barrier's Fréchet Hessian:
`orbitDikinMetric x v = hessianMap orbitBarrier x v v`. -/
theorem orbitDikinMetric_eq_hessian {x v : ℝ} (hx : 0 < x) :
    orbitDikinMetric x v = hessianMap orbitBarrier x v v :=
  (orbitBarrier_hessian_metric x v hx).symm

end
