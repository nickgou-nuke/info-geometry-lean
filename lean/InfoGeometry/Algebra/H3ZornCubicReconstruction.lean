/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Algebra.H3ZornTraceNondegenerate
import InfoGeometry.Algebra.H3ZornCubicPolarization
import InfoGeometry.Algebra.BaezF4H3Zorn

/-!
# Reconstruction of the full Albert product from its cubic form and unit

The normalized cubic form is the existing `h3zornNormTrilin` on all of
`H3Zorn ℝ`. Evaluating it at the distinguished identity recovers the linear
trace and trace pairing. Nondegeneracy then recovers the cross product and
the actual Jordan product. This is the reconstruction argument in Seligman's
1960 paper, §§5 and 8, in the repository's normalized product convention.

No definiteness assumption is made on the split trace pairing. Every
conclusion is derived from tensor preservation and, where stated, the fixed
unit condition; product preservation is not an input certificate.
-/

noncomputable section

namespace InfoGeometry.Algebra

open H3Zorn

/-- The normalization of the existing polarized cubic norm. -/
theorem h3zornNormTrilin_apply (x y z : H3Zorn ℝ) :
    h3zornNormTrilin x y z = (1 / 6 : ℝ) * traceBilin x (crossProduct y z) :=
  rfl

/-- One distinguished unit recovers the trace pairing from the cubic form. -/
theorem h3zornNormTrilin_one_right (x y : H3Zorn ℝ) :
    6 * h3zornNormTrilin x y 1 = linearTrace x * linearTrace y - traceBilin x y := by
  rw [h3zornNormTrilin_apply, crossProduct_one, traceBilin_sub_right,
    traceBilin_smul_right, traceBilin_one]
  ring

/-- Two distinguished units recover the linear trace. -/
theorem h3zornNormTrilin_one_one (x : H3Zorn ℝ) :
    3 * h3zornNormTrilin x 1 1 = linearTrace x := by
  have h := h3zornNormTrilin_one_right x 1
  have ht : linearTrace (1 : H3Zorn ℝ) = 3 := by
    change (1 : ℝ) + 1 + 1 = 3
    norm_num
  rw [ht, traceBilin_one] at h
  linarith

/-- The polarized cubic has zero radical in its first argument. -/
theorem h3zorn_eq_zero_of_normTrilin_left (x : H3Zorn ℝ)
    (h : ∀ y z, h3zornNormTrilin x y z = 0) : x = 0 := by
  have ht : linearTrace x = 0 := by
    have hx := h3zornNormTrilin_one_one x
    rw [h 1 1, mul_zero] at hx
    exact hx.symm
  apply eq_zero_of_traceBilin_left x
  intro y
  have hx := h3zornNormTrilin_one_right x y
  rw [h y 1, ht] at hx
  linarith

/-- Preservation of the full cubic form already forces a linear map to be
injective. This statement does not assume that the map fixes the identity. -/
theorem h3zorn_cubicPreserver_injective (f : Module.End ℝ (H3Zorn ℝ))
    (hf : ∀ x y z, h3zornNormTrilin (f x) (f y) (f z) = h3zornNormTrilin x y z) :
    Function.Injective f := by
  intro x y hxy
  apply sub_eq_zero.mp
  apply h3zorn_eq_zero_of_normTrilin_left (x - y)
  intro z w
  rw [← hf, map_sub, hxy, sub_self]
  simp only [map_zero, LinearMap.zero_apply]

/-- Cubic preservation and a fixed identity imply preservation of the trace. -/
theorem h3zorn_trace_eq_of_cubic_and_unit (f : Module.End ℝ (H3Zorn ℝ))
    (hf : ∀ x y z, h3zornNormTrilin (f x) (f y) (f z) = h3zornNormTrilin x y z)
    (h1 : f 1 = 1) (x : H3Zorn ℝ) : linearTrace (f x) = linearTrace x := by
  have hc := hf x 1 1
  rw [h1] at hc
  rw [← h3zornNormTrilin_one_one (f x), hc, h3zornNormTrilin_one_one]

/-- The same hypotheses imply preservation of the full split trace pairing. -/
theorem h3zorn_traceBilin_eq_of_cubic_and_unit (f : Module.End ℝ (H3Zorn ℝ))
    (hf : ∀ x y z, h3zornNormTrilin (f x) (f y) (f z) = h3zornNormTrilin x y z)
    (h1 : f 1 = 1) (x y : H3Zorn ℝ) : traceBilin (f x) (f y) = traceBilin x y := by
  have hx := h3zornNormTrilin_one_right (f x) (f y)
  have hy := h3zornNormTrilin_one_right x y
  rw [h3zorn_trace_eq_of_cubic_and_unit f hf h1 x,
    h3zorn_trace_eq_of_cubic_and_unit f hf h1 y, ← h1, hf] at hx
  exact sub_right_inj.mp (hx.symm.trans hy)

/-- Nondegeneracy turns preservation of the polarized cubic and trace pairing
into covariance of the actual Albert cross product. -/
theorem h3zorn_crossProduct_eq_of_cubic_and_unit
    (e : H3Zorn ℝ ≃ₗ[ℝ] H3Zorn ℝ)
    (he : ∀ x y z, h3zornNormTrilin (e x) (e y) (e z) = h3zornNormTrilin x y z)
    (h1 : e 1 = 1) (x y : H3Zorn ℝ) :
    e (crossProduct x y) = crossProduct (e x) (e y) := by
  apply eq_of_traceBilin_right_eq
  intro z
  obtain ⟨z, rfl⟩ := e.surjective z
  have hb := h3zorn_traceBilin_eq_of_cubic_and_unit e.toLinearMap he h1 z
    (crossProduct x y)
  have hc := he z x y
  simp only [h3zornNormTrilin_apply] at hc
  change traceBilin (e z) (e (crossProduct x y)) = traceBilin z (crossProduct x y) at hb
  linarith

/-- The full normalized Jordan product is reconstructed from the cubic form
and the identity; multiplicativity is proved rather than assumed. -/
theorem h3zorn_jordanMul_eq_of_cubic_and_unit
    (e : H3Zorn ℝ ≃ₗ[ℝ] H3Zorn ℝ)
    (he : ∀ x y z, h3zornNormTrilin (e x) (e y) (e z) = h3zornNormTrilin x y z)
    (h1 : e 1 = 1) (x y : H3Zorn ℝ) : e (x * y) = e x * e y := by
  have ht (z : H3Zorn ℝ) : linearTrace (e z) = linearTrace z :=
    h3zorn_trace_eq_of_cubic_and_unit e.toLinearMap he h1 z
  have hc := h3zorn_crossProduct_eq_of_cubic_and_unit e he h1 x y
  have htc : linearTrace (crossProduct (e x) (e y)) = linearTrace (crossProduct x y) := by
    rw [← hc, ht]
  change e (candidateJordanMul x y) = candidateJordanMul (e x) (e y)
  simp only [candidateJordanMul_trace_formula, map_smul, map_add, map_sub,
    h1, ht, hc, htc]

/-- A unit-fixing cubic symmetry gives an actual member of the existing
Albert Jordan automorphism group. -/
def h3zornJordanAutOfCubic (e : H3Zorn ℝ ≃ₗ[ℝ] H3Zorn ℝ)
    (he : ∀ x y z, h3zornNormTrilin (e x) (e y) (e z) = h3zornNormTrilin x y z)
    (h1 : e 1 = 1) : H3ZornJordanAut :=
  ⟨e, h1, h3zorn_jordanMul_eq_of_cubic_and_unit e he h1⟩

@[simp] theorem h3zornJordanAutOfCubic_toLinearEquiv
    (e : H3Zorn ℝ ≃ₗ[ℝ] H3Zorn ℝ)
    (he : ∀ x y z, h3zornNormTrilin (e x) (e y) (e z) = h3zornNormTrilin x y z)
    (h1 : e 1 = 1) : (h3zornJordanAutOfCubic e he h1).toLinearEquiv = e := rfl

/-- Preservation of the actual cubic polynomial also forces injectivity. -/
theorem h3zorn_normPreserver_injective (f : Module.End ℝ (H3Zorn ℝ))
    (hN : ∀ x, normCubic (f x) = normCubic x) : Function.Injective f :=
  h3zorn_cubicPreserver_injective f
    (h3zornNormTrilin_preserved_of_normCubic_preserved f hN)

/-- A linear equivalence preserving the actual cubic polynomial and fixing
the distinguished identity is a genuine Jordan automorphism. -/
def h3zornJordanAutOfNorm (e : H3Zorn ℝ ≃ₗ[ℝ] H3Zorn ℝ)
    (hN : ∀ x, normCubic (e x) = normCubic x) (h1 : e 1 = 1) : H3ZornJordanAut :=
  h3zornJordanAutOfCubic e
    (h3zornNormTrilin_preserved_of_normCubic_preserved e.toLinearMap hN) h1

@[simp] theorem h3zornJordanAutOfNorm_toLinearEquiv
    (e : H3Zorn ℝ ≃ₗ[ℝ] H3Zorn ℝ)
    (hN : ∀ x, normCubic (e x) = normCubic x) (h1 : e 1 = 1) :
    (h3zornJordanAutOfNorm e hN h1).toLinearEquiv = e := rfl

end InfoGeometry.Algebra
