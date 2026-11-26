/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Geometry.MobiusInfinitesimal
import InfoGeometry.Geometry.MobiusLieExponential
import InfoGeometry.Topology.MobiusGeometry
import Mathlib.Tactic

/-!
# Remaining pure-math packet of the Möbius/Pólya/Lie paper

This module closes the theorem-shaped gaps that a full-repo deep search found
absent, reusing the existing owners:

* `InfoGeometry.Topology.MobiusGeometry` already has normal forms, multipliers,
  conjugacy and fixed points; it has `map_to_01inf` but **not** the two-point
  isometric reduction of Definition 2.1, which is added here.
* `InfoGeometry.Geometry.MobiusLieExponential` already has the closed-form
  exponential; the **Möbius rational-function readback** of eq. (8) is added
  here.
* `InfoGeometry.Geometry.MobiusInfinitesimal` already has the compact complex
  quadratic vector field; the **real/imaginary component expansions** of
  Propositions 3.2 and 3.3 are added here.

The physics "outlook" sections of the paper are heuristic and not theorem
shaped; no claim about them is made here.
-/

noncomputable section

namespace InfoGeometry.Geometry.MobiusPaperRemainder

open InfoGeometry
open InfoGeometry.Canonical.MatrixDetExpTraceJacobi
open InfoGeometry.Geometry
open InfoGeometry.Geometry.MobiusLieExponential

abbrev M2C := Matrix (Fin 2) (Fin 2) ℂ

/-! ## Definition 2.1 — isometric reduction to (0, ∞) -/

/-- The Möbius map `g(z) = (z - z₁)/(z - z₂)`, for distinct fixed points. -/
def isometricReduction (z₁ z₂ : ℂ) (h : z₁ ≠ z₂) : MobiusTransform where
  a := 1
  b := -z₁
  c := 1
  d := -z₂
  det_ne_zero := by
    have hdet : (1 : ℂ) * (-z₂) - (-z₁) * 1 = z₁ - z₂ := by ring
    rw [hdet]
    simpa [sub_eq_add_neg] using (sub_ne_zero.mpr h)

/-- The reduction sends the first fixed point to `0`. -/
theorem isometricReduction_apply_left (z₁ z₂ : ℂ) (h : z₁ ≠ z₂) :
    (isometricReduction z₁ z₂ h).eval (some z₁) = some 0 := by
  rw [MobiusTransform.eval]
  dsimp [isometricReduction]
  have hden : z₁ + -z₂ ≠ 0 := by
    simpa [sub_eq_add_neg] using (sub_ne_zero.mpr h)
  simp [hden]

/-- The reduction sends the second fixed point to `∞`. -/
theorem isometricReduction_apply_right (z₁ z₂ : ℂ) (h : z₁ ≠ z₂) :
    (isometricReduction z₁ z₂ h).eval (some z₂) = none := by
  rw [MobiusTransform.eval]
  dsimp [isometricReduction]
  have hden : z₂ + -z₂ = 0 := by ring
  simp [hden]

/-! ## Remark 3.1 / eq. (8) — Möbius readback of the parabolic exponential -/

/-- The Möbius transformation whose matrix is `exp(t X)`, `X ∈ sl₂(ℂ)`. -/
def expMobius (X : sl2C) (t : ℂ) : MobiusTransform where
  a := (NormedSpace.exp (t • X.matrix)) 0 0
  b := (NormedSpace.exp (t • X.matrix)) 0 1
  c := (NormedSpace.exp (t • X.matrix)) 1 0
  d := (NormedSpace.exp (t • X.matrix)) 1 1
  det_ne_zero := by
    have hd := sl2CExpFlow_det X t
    dsimp [sl2CExpFlow, matrixExpFlow] at hd
    rw [Matrix.det_fin_two] at hd
    rw [hd]
    exact one_ne_zero

/-- Parabolic case: the exponential flow is the rational map of eq. (8),
    `f_t(z) = ((1 + t p) z + t q) / (t r z + (1 - t p))`. -/
theorem expMobius_parabolic_eval (X : sl2C) (hdet : X.matrix.det = 0)
    (t : ℂ) (z : ℂ) (hz : t * X.c * z + (1 - t * X.a) ≠ 0) :
    (expMobius X t).eval (some z) =
      some (((1 + t * X.a) * z + t * X.b) / (t * X.c * z + (1 - t * X.a))) := by
  have hE := exp_sl2C_parabolic X hdet t
  have h00 : (NormedSpace.exp (t • X.matrix)) 0 0 = 1 + t * X.a := by
    rw [hE]
    simp [sl2C.matrix]
  have h01 : (NormedSpace.exp (t • X.matrix)) 0 1 = t * X.b := by
    rw [hE]
    simp [sl2C.matrix]
  have h10 : (NormedSpace.exp (t • X.matrix)) 1 0 = t * X.c := by
    rw [hE]
    simp [sl2C.matrix]
  have h11 : (NormedSpace.exp (t • X.matrix)) 1 1 = 1 - t * X.a := by
    rw [hE]
    simp [sl2C.matrix]
    ring_nf
  rw [MobiusTransform.eval]
  dsimp [expMobius]
  simp [h00, h01, h10, h11, hz]

/-! ## Propositions 3.2 / 3.3 — real and imaginary component expansions -/

/-- Real part of the infinitesimal quadratic field, written with
    `p = a`, `q = b`, `r = c` as in the paper's eq. (15). -/
theorem vectorField_re (X : sl2C) (x y : ℝ) :
    (X.vectorField (Complex.mk x y)).re =
      X.b.re + 2 * (X.a.re * x - X.a.im * y) -
        (X.c.re * (x ^ 2 - y ^ 2) - 2 * X.c.im * x * y) := by
  have hsq : (Complex.mk x y : ℂ) ^ 2 = Complex.mk (x ^ 2 - y ^ 2) (2 * x * y) := by
    apply Complex.ext
    · simp [pow_two]
    · simp [pow_two]
      ring
  simp [sl2C.vectorField, hsq]
  ring

/-- Imaginary part of the infinitesimal quadratic field, eq. (15). -/
theorem vectorField_im (X : sl2C) (x y : ℝ) :
    (X.vectorField (Complex.mk x y)).im =
      X.b.im + 2 * (X.a.re * y + X.a.im * x) -
        (X.c.re * (2 * x * y) + X.c.im * (x ^ 2 - y ^ 2)) := by
  have hsq : (Complex.mk x y : ℂ) ^ 2 = Complex.mk (x ^ 2 - y ^ 2) (2 * x * y) := by
    apply Complex.ext
    · simp [pow_two]
    · simp [pow_two]
      ring
  simp [sl2C.vectorField, hsq]
  ring

/-- Real reduction, Pólya convention `f̃ = u - i v`: eq. (16). -/
theorem vectorField_polya_real_reduction (p q r x y : ℝ) :
    let X : sl2C := sl2C.ofCoords p q r
    star (X.vectorField (Complex.mk x y)) =
      Complex.mk (-r * x ^ 2 + r * y ^ 2 + 2 * p * x + q)
                 (2 * r * x * y - 2 * p * y) := by
  dsimp
  have hsq : (Complex.mk x y : ℂ) ^ 2 = Complex.mk (x ^ 2 - y ^ 2) (2 * x * y) := by
    apply Complex.ext
    · simp [pow_two]
    · simp [pow_two]
      ring
  apply Complex.ext
  · simp [sl2C.vectorField, sl2C.ofCoords, sl2C.a, sl2C.b, sl2C.c, hsq]
    ring
  · simp [sl2C.vectorField, sl2C.ofCoords, sl2C.a, sl2C.b, sl2C.c, hsq]
    ring

end InfoGeometry.Geometry.MobiusPaperRemainder
