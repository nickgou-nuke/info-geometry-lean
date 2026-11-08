/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Canonical.TensorPeirceAttentionNetworkAmariYangianPoset
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Matrix.Normed

/-!
# Directional derivative of the Operator Gaussian

This file proves a genuine one-dimensional Mathlib derivative for the existing
attention Gaussian along a simultaneous affine perturbation of its two Peirce
parameters. The theorem is stated for real normed algebras, so it applies to
finite matrix algebras equipped with their operator norm.
-/

namespace InfoGeometry.Canonical.TensorPeirceAttentionGaussianDerivative

open InfoGeometry.Canonical.TensorPeirceAttentionNetworkAmariYangianPoset
open InfoGeometry.OperatorAlgebra.PeirceSpine

variable {B : Type*} [NormedRing B] [NormedAlgebra ℝ B]

noncomputable section

open scoped Matrix.Norms.Operator

theorem hasDerivAt_attentionGaussianPlus_line
    (P A C dA dC : B) :
    HasDerivAt
      (fun t : ℝ => attentionGaussianPlus P (A + t • dA) (C + t • dC))
      (attentionGaussianPlusDiff P A C dA dC) 0 := by
  have hA : HasDerivAt (fun t : ℝ => A + t • dA) dA 0 := by
    have hConst : HasDerivAt (fun _ : ℝ => A) 0 0 := hasDerivAt_const 0 A
    have hLine : HasDerivAt (fun t : ℝ => t • dA) dA 0 := by
      simpa using (hasDerivAt_id (x := (0 : ℝ))).smul_const dA
    convert hConst.add hLine using 1; simp
  have hC : HasDerivAt (fun t : ℝ => C + t • dC) dC 0 := by
    have hConst : HasDerivAt (fun _ : ℝ => C) 0 0 := hasDerivAt_const 0 C
    have hLine : HasDerivAt (fun t : ℝ => t • dC) dC 0 := by
      simpa using (hasDerivAt_id (x := (0 : ℝ))).smul_const dC
    convert hConst.add hLine using 1; simp
  have hPlus :
      HasDerivAt (fun t : ℝ => conePlus P (A + t • dA))
        (conePlus P dA) 0 := by
    simpa [conePlus, mul_add, mul_smul_comm] using
      (hA.const_mul P).mul_const (1 - P)
  have hMinus :
      HasDerivAt (fun t : ℝ => coneMinus P (C + t • dC))
        (coneMinus P dC) 0 := by
    simpa [coneMinus, mul_add, mul_smul_comm] using
      (hC.const_mul (1 - P)).mul_const P
  have hGatePlus :
      HasDerivAt (fun t : ℝ => amariGatePlus P (A + t • dA))
        (conePlus P dA) 0 := by
    simpa [amariGatePlus] using hPlus.const_add (1 : B)
  have hGateMinus :
      HasDerivAt (fun t : ℝ => amariGateMinus P (C + t • dC))
        (coneMinus P dC) 0 := by
    simpa [amariGateMinus] using hMinus.const_add (1 : B)
  have hProd := hGatePlus.mul hGateMinus
  convert hProd using 1
  · funext t
    rfl
  · simp [attentionGaussianPlusDiff, amariGatePlus, amariGateMinus]


/-- Finite square real matrices, equipped with Mathlib's operator norm, satisfy
    the same directional derivative formula. -/
theorem matrix_hasDerivAt_attentionGaussianPlus_line
    {n : Type*} [Fintype n] [DecidableEq n]
    (P A C dA dC : Matrix n n ℝ) :
    letI : NormedRing (Matrix n n ℝ) := Matrix.linftyOpNormedRing
    letI : NormedAlgebra ℝ (Matrix n n ℝ) := Matrix.linftyOpNormedAlgebra
    HasDerivAt
      (fun t : ℝ => attentionGaussianPlus P (A + t • dA) (C + t • dC))
      (attentionGaussianPlusDiff P A C dA dC) 0 := by
  letI : NormedRing (Matrix n n ℝ) := Matrix.linftyOpNormedRing
  letI : NormedAlgebra ℝ (Matrix n n ℝ) := Matrix.linftyOpNormedAlgebra
  exact hasDerivAt_attentionGaussianPlus_line P A C dA dC

end

end InfoGeometry.Canonical.TensorPeirceAttentionGaussianDerivative
