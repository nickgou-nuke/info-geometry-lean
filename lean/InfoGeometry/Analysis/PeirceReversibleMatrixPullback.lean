/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Analysis.PeirceReversibleDifferential
import InfoGeometry.Analysis.MatrixTraceQuadratic

/-! # Matrix cotangent pullback for a reversible Peirce gate

All matrices are arbitrary full complex matrices. Differentiation and the
Hilbert--Schmidt pairing are real. The native operator norm is retained;
no equality between that norm and the trace norm is asserted.

The projection is fixed and self-adjoint. The three displayed covectors pair
with every independent ambient parameter and input direction. A final theorem
connects them to the native derivative of an actual scalar loss.
-/

noncomputable section

namespace InfoGeometry.Analysis.PeirceReversibleMatrixPullback

open InfoGeometry.OperatorAlgebra.PeirceSpine
open PeirceReversibleDifferential MatrixTraceQuadratic
open scoped Matrix.Norms.L2Operator

variable {n : Type*} [Fintype n] [DecidableEq n]
local notation "Mat" => Matrix n n ℂ

/-- Ordered multiplication has the expected adjoint for the real trace pairing. -/
theorem tracePair_mulLeftRight (Z L H R : Mat) :
    tracePair Z (L * H * R) = tracePair (star L * Z * star R) H := by
  simp only [tracePair_apply, star_mul, star_star]
  simpa only [mul_assoc] using
    congrArg Complex.re (Matrix.trace_mul_comm (star Z * L * H) R)

/-- Exact vector-Jacobian product against the actual native Fréchet derivative.
The output and its loss cotangent may depend on both gate parameters. -/
theorem tracePair_fderiv_epistemicCornerShear_action
    {P : Mat} (hP : P * P = P) (hPs : star P = P)
    (A C x Z dA dC dx : Mat) :
    tracePair Z (fderiv ℝ
      (fun z : Mat × Mat × Mat => epistemicCornerShear P z.1 z.2.1 * z.2.2)
      (A, C, x) (dA, dC, dx)) =
      tracePair (conePlus P (Z * star (epistemicCornerShear P A C * x))) dA +
        tracePair (coneMinus P (star (1 + conePlus P A) * Z *
          star ((1 - conePlus P A) * (epistemicCornerShear P A C * x)))) dC +
        tracePair (star (epistemicCornerShear P A C) * Z) dx := by
  let a := conePlus P A
  let G := epistemicCornerShear P A C
  let y := G * x
  let m := (1 - a) * y
  have hp : tracePair Z (conePlus P dA * y) =
      tracePair (conePlus P (Z * star y)) dA := by
    simpa only [conePlus, star_mul, star_sub, star_one, hPs, mul_assoc] using
      tracePair_mulLeftRight Z P dA ((1 - P) * y)
  have hm : tracePair Z ((1 + a) * coneMinus P dC * m) =
      tracePair (coneMinus P (star (1 + a) * Z * star m)) dC := by
    simpa only [coneMinus, star_mul, star_sub, star_one, hPs, mul_assoc] using
      tracePair_mulLeftRight Z ((1 + a) * (1 - P)) dC (P * m)
  have hi : tracePair Z (G * dx) = tracePair (star G * Z) dx := by
    simpa only [star_one, mul_one] using tracePair_mulLeftRight Z G dx (1 : Mat)
  rw [fderiv_epistemicCornerShear_action_output ℝ hP]
  simpa only [map_add] using congrArg₂ (· + ·) (congrArg₂ (· + ·) hp hm) hi

/-- Chain rule for a real scalar loss whose output cotangent is represented
by the positive definite real trace pairing. -/
theorem fderiv_loss_epistemicCornerShear_action_apply
    {P : Mat} (hP : P * P = P) (hPs : star P = P)
    (A C x Z dA dC dx : Mat) {loss : Mat → ℝ}
    (hLoss : HasFDerivAt loss (tracePair Z) (epistemicCornerShear P A C * x)) :
    fderiv ℝ
      (fun z : Mat × Mat × Mat => loss (epistemicCornerShear P z.1 z.2.1 * z.2.2))
      (A, C, x) (dA, dC, dx) =
      tracePair (conePlus P (Z * star (epistemicCornerShear P A C * x))) dA +
        tracePair (coneMinus P (star (1 + conePlus P A) * Z *
          star ((1 - conePlus P A) * (epistemicCornerShear P A C * x)))) dC +
        tracePair (star (epistemicCornerShear P A C) * Z) dx := by
  have hGate := hasFDerivAt_epistemicCornerShear_action ℝ P A C x
  have h := hLoss.comp (A, C, x) hGate
  simp only [Function.comp_def] at h
  rw [h.fderiv, ContinuousLinearMap.comp_apply, ← hGate.fderiv]
  exact tracePair_fderiv_epistemicCornerShear_action hP hPs A C x Z dA dC dx

/-- A concrete scalar-loss instance: half the squared Hilbert--Schmidt
size of the output. Its output cotangent is the output itself. -/
theorem fderiv_halfTraceSquare_epistemicCornerShear_action_apply
    {P : Mat} (hP : P * P = P) (hPs : star P = P)
    (A C x dA dC dx : Mat) :
    let y := epistemicCornerShear P A C * x
    fderiv ℝ
      (fun z : Mat × Mat × Mat =>
        halfTraceSquare (epistemicCornerShear P z.1 z.2.1 * z.2.2))
      (A, C, x) (dA, dC, dx) =
      tracePair (conePlus P (y * star y)) dA +
        tracePair (coneMinus P (star (1 + conePlus P A) * y *
          star ((1 - conePlus P A) * y))) dC +
        tracePair (star (epistemicCornerShear P A C) * y) dx := by
  exact fderiv_loss_epistemicCornerShear_action_apply hP hPs A C x
    (epistemicCornerShear P A C * x) dA dC dx
    (hasFDerivAt_halfTraceSquare (epistemicCornerShear P A C * x))

end InfoGeometry.Analysis.PeirceReversibleMatrixPullback
