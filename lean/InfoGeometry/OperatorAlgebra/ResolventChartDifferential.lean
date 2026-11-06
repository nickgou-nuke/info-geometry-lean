/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import Mathlib.Analysis.Calculus.FDeriv.Mul
import Mathlib.Tactic.NoncommRing

/-!
# Ordered resolvent coordinates and their native differential

The coordinate map is `z ↦ Ring.inverse (1 - z * w) * z`, with `w` fixed.
On its unit domain, its differential is the two-sided multiplication map
`H ↦ Ring.inverse (1 - z * w) * H * Ring.inverse (1 - w * z)`.

The inverse transport, exact increment, and factorization of the differential
are associative ring identities. The native Fréchet derivative additionally
uses a normed algebra with summable geometric series; in particular, a complete
normed algebra supplies the required instance. Both denominator unit hypotheses
are displayed explicitly. No commutation between the base point, the fixed
parameter, or the tangent direction is assumed.

This module differentiates a rational operator map. Identifying that map with
a scalar potential's Legendre map, or its differential with a geometric metric,
requires further constructions and is not asserted here.
-/

noncomputable section

namespace InfoGeometry.OperatorAlgebra.ResolventChartDifferential

section Ring

variable {A : Type*} [Ring A]

/-- The native ring inverse keeps the coordinate factor on the right. -/
def resolventChart (w z : A) : A :=
  Ring.inverse (1 - z * w) * z

/-- Inverting the two denominators transports the coordinate in its ordered position. -/
theorem inverse_one_sub_mul_mul (z w : A)
    (hzw : IsUnit (1 - z * w)) (hwz : IsUnit (1 - w * z)) :
    Ring.inverse (1 - z * w) * z = z * Ring.inverse (1 - w * z) := by
  apply (Ring.inverse_mul_eq_iff_eq_mul (1 - z * w) z
    (z * Ring.inverse (1 - w * z)) hzw).2
  calc
    z = z * ((1 - w * z) * Ring.inverse (1 - w * z)) := by
      rw [Ring.mul_inverse_cancel _ hwz, mul_one]
    _ = (1 - z * w) * (z * Ring.inverse (1 - w * z)) := by
      noncomm_ring

/-- Exact finite increment of the ordered coordinate, with no limiting argument. -/
theorem resolventChart_add_sub (w z H : A)
    (hzw : IsUnit (1 - z * w)) (hwz : IsUnit (1 - w * z))
    (hnew : IsUnit (1 - (z + H) * w)) :
    resolventChart w (z + H) - resolventChart w z =
      Ring.inverse (1 - (z + H) * w) * H * Ring.inverse (1 - w * z) := by
  unfold resolventChart
  rw [inverse_one_sub_mul_mul z w hzw hwz]
  calc
    Ring.inverse (1 - (z + H) * w) * (z + H) -
        z * Ring.inverse (1 - w * z) =
      (Ring.inverse (1 - (z + H) * w) * (z + H)) *
          ((1 - w * z) * Ring.inverse (1 - w * z)) -
        (Ring.inverse (1 - (z + H) * w) * (1 - (z + H) * w)) *
          (z * Ring.inverse (1 - w * z)) := by
      rw [Ring.mul_inverse_cancel _ hwz, Ring.inverse_mul_cancel _ hnew,
        mul_one, one_mul]
    _ = Ring.inverse (1 - (z + H) * w) * H * Ring.inverse (1 - w * z) := by
      noncomm_ring

/-- The noncommutative product-rule expression factors around the tangent direction. -/
theorem resolvent_differential_factorization (z w H : A)
    (hzw : IsUnit (1 - z * w)) (hwz : IsUnit (1 - w * z)) :
    Ring.inverse (1 - z * w) * H +
        Ring.inverse (1 - z * w) * (H * w) * Ring.inverse (1 - z * w) * z =
      Ring.inverse (1 - z * w) * H * Ring.inverse (1 - w * z) := by
  have hright : 1 + (w * z) * Ring.inverse (1 - w * z) =
      Ring.inverse (1 - w * z) := by
    calc
      1 + (w * z) * Ring.inverse (1 - w * z) =
          (1 - w * z) * Ring.inverse (1 - w * z) +
            (w * z) * Ring.inverse (1 - w * z) := by
        rw [Ring.mul_inverse_cancel _ hwz]
      _ = Ring.inverse (1 - w * z) := by noncomm_ring
  calc
    Ring.inverse (1 - z * w) * H +
        Ring.inverse (1 - z * w) * (H * w) * Ring.inverse (1 - z * w) * z =
      Ring.inverse (1 - z * w) * H *
        (1 + w * (Ring.inverse (1 - z * w) * z)) := by noncomm_ring
    _ = Ring.inverse (1 - z * w) * H *
        (1 + (w * z) * Ring.inverse (1 - w * z)) := by
      rw [inverse_one_sub_mul_mul z w hzw hwz]
      noncomm_ring
    _ = Ring.inverse (1 - z * w) * H * Ring.inverse (1 - w * z) := by
      rw [hright]

end Ring

section Differential

variable {𝕜 A : Type*} [NontriviallyNormedField 𝕜]
variable [NormedRing A] [NormedAlgebra 𝕜 A] [HasSummableGeomSeries A]

/-- The actual Fréchet derivative is the ordered two-sided resolvent sandwich. -/
theorem hasFDerivAt_resolventChart (w z : A)
    (hzw : IsUnit (1 - z * w)) (hwz : IsUnit (1 - w * z)) :
    HasFDerivAt (resolventChart w)
      (ContinuousLinearMap.mulLeftRight 𝕜 A
        (Ring.inverse (1 - z * w)) (Ring.inverse (1 - w * z))) z := by
  have hright : HasFDerivAt (fun X : A => X * w)
      ((ContinuousLinearMap.mul 𝕜 A).flip w) z :=
    ((ContinuousLinearMap.mul 𝕜 A).flip w).hasFDerivAt
  have hden : HasFDerivAt (fun X : A => 1 - X * w)
      (-((ContinuousLinearMap.mul 𝕜 A).flip w)) z :=
    hright.const_sub 1
  have hinv : HasFDerivAt (Ring.inverse : A → A)
      (-ContinuousLinearMap.mulLeftRight 𝕜 A
        (Ring.inverse (1 - z * w)) (Ring.inverse (1 - z * w)))
      (1 - z * w) := by
    obtain ⟨u, hu⟩ := hzw
    simpa only [← hu, Ring.inverse_unit] using
      hasFDerivAt_ringInverse (𝕜 := 𝕜) u
  have hprod := (hinv.comp z hden).mul' (hasFDerivAt_id z)
  apply hprod.congr_fderiv
  ext H
  change Ring.inverse (1 - z * w) * H +
      (-(Ring.inverse (1 - z * w) * (-(H * w)) * Ring.inverse (1 - z * w))) * z =
    Ring.inverse (1 - z * w) * H * Ring.inverse (1 - w * z)
  simp only [mul_neg, neg_mul, neg_neg]
  exact resolvent_differential_factorization z w H hzw hwz

/-- Evaluation of the native derivative in an arbitrary operator direction. -/
theorem fderiv_resolventChart_apply (w z H : A)
    (hzw : IsUnit (1 - z * w)) (hwz : IsUnit (1 - w * z)) :
    fderiv 𝕜 (resolventChart w) z H =
      Ring.inverse (1 - z * w) * H * Ring.inverse (1 - w * z) := by
  rw [(hasFDerivAt_resolventChart (𝕜 := 𝕜) w z hzw hwz).fderiv]
  rfl

end Differential

end InfoGeometry.OperatorAlgebra.ResolventChartDifferential
