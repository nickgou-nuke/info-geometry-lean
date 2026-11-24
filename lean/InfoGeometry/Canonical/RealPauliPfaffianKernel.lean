/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/

import InfoGeometry.Clifford.GullDoranPseudoscalarBridge
import InfoGeometry.Canonical.MajoranaPfaffian4

/-!
# Real Pauli matrices, the signed interval, and a circular basis

This module reuses the existing real Pauli matrices and the existing
four-index signed Pfaffian polynomial. All declarations below have real
scalar carriers.

The coordinate order is `(re z₀, im z₀, re z₁, im z₁)`, as fixed by
`GullDoranPseudoscalarBridge`. In this orientation the reference real phase
matrix has Pfaffian `+1`. Multiplying the symmetric Pauli representative by
that phase gives a skew matrix whose signed Pfaffian is the Lorentzian
quadratic interval. Its ordinary real determinant is the interval squared.

The circular change of basis is invertible and cyclically permutes the three
spatial Pauli coordinates. It is a finite matrix basis change, with no claim
that its two coordinate blocks are real Majorana--Weyl representations.
-/

noncomputable section

namespace InfoGeometry.Canonical.RealPauliPfaffianKernel

open scoped Matrix
open InfoGeometry.Clifford.GullDoranPseudoscalarBridge
open InfoGeometry.Canonical.MajoranaPfaffian4

abbrev Matrix4 := InfoGeometry.Algebra.FiniteSpin.Mat4R

/-- The signed Lorentzian quadratic form with timelike sign positive. -/
def intervalSq (t x y z : ℝ) : ℝ := t ^ 2 - x ^ 2 - y ^ 2 - z ^ 2

/-- The existing real Pauli generators encode the four real coordinates. -/
def pauli (t x y z : ℝ) : Matrix4 :=
  t • (1 : Matrix4) + x • realSigma1 + y • realSigma2 + z • realSigma3

theorem pauli_explicit (t x y z : ℝ) :
    pauli t x y z =
      !![t + z, 0, x, y;
         0, t + z, -y, x;
         x, -y, t - z, 0;
         y, x, 0, t - z] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [pauli, realSigma1, realSigma2, realSigma3] <;> ring

theorem pauli_transpose (t x y z : ℝ) :
    (pauli t x y z).transpose = pauli t x y z := by
  simp only [pauli_explicit]
  ext i j
  fin_cases i <;> fin_cases j <;> rfl

theorem pauli_commutes_phase (t x y z : ℝ) :
    pauli t x y z * realPhaseAxis = realPhaseAxis * pauli t x y z := by
  simp only [pauli_explicit]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [realPhaseAxis, Matrix.mul_apply, Fin.sum_univ_four]

/-- The quadratic interval is recovered before taking any determinant. -/
theorem pauli_mul_cosolder (t x y z : ℝ) :
    pauli t x y z * pauli t (-x) (-y) (-z) =
      intervalSq t x y z • (1 : Matrix4) := by
  simp only [pauli_explicit]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [intervalSq, Matrix.mul_apply, Fin.sum_univ_four] <;> ring

theorem cosolder_mul_pauli (t x y z : ℝ) :
    pauli t (-x) (-y) (-z) * pauli t x y z =
      intervalSq t x y z • (1 : Matrix4) := by
  simpa [intervalSq] using pauli_mul_cosolder t (-x) (-y) (-z)

/-- The phase turns the symmetric Pauli operator into a skew operator. -/
def phasePauli (t x y z : ℝ) : Matrix4 :=
  realPhaseAxis * pauli t x y z

theorem phasePauli_eq_skewMatrix4 (t x y z : ℝ) :
    phasePauli t x y z =
      skewMatrix4 (-(t + z)) y (-x) x y (-(t - z)) := by
  rw [phasePauli, pauli_explicit]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [realPhaseAxis, skewMatrix4, Matrix.mul_apply, Fin.sum_univ_four]

theorem phasePauli_transpose (t x y z : ℝ) :
    (phasePauli t x y z).transpose = -phasePauli t x y z := by
  simp only [phasePauli_eq_skewMatrix4, skewMatrix4_transpose]

/-- Read the existing signed polynomial from six actual matrix entries. -/
def matrixPfaffian4 (A : Matrix4) : ℝ :=
  pfaffian4 (A 0 1) (A 0 2) (A 0 3) (A 1 2) (A 1 3) (A 2 3)

theorem phase_pfaffian : matrixPfaffian4 realPhaseAxis = 1 := by
  norm_num [matrixPfaffian4, realPhaseAxis, pfaffian4]

/-- The signed real Pfaffian, in the fixed phase orientation, is the interval. -/
theorem phasePauli_pfaffian (t x y z : ℝ) :
    matrixPfaffian4 (phasePauli t x y z) = intervalSq t x y z := by
  simp [matrixPfaffian4, phasePauli_eq_skewMatrix4, skewMatrix4,
    pfaffian4, intervalSq]
  ring

/-- Apply the independently proved finite Pfaffian square law. -/
theorem phasePauli_det (t x y z : ℝ) :
    (phasePauli t x y z).det = intervalSq t x y z ^ 2 := by
  calc
    (phasePauli t x y z).det =
        pfaffian4 (-(t + z)) y (-x) x y (-(t - z)) ^ 2 := by
      rw [phasePauli_eq_skewMatrix4]
      exact (skewMatrix4_pfaffian_sq_eq_det _ _ _ _ _ _).symm
    _ = intervalSq t x y z ^ 2 := by
      unfold pfaffian4 intervalSq
      ring

theorem phase_det : realPhaseAxis.det = 1 := by
  have hJ : realPhaseAxis =
      skewMatrix4 (-1 : ℝ) 0 0 0 0 (-1) := by
    ext i j
    fin_cases i <;> fin_cases j <;> norm_num [realPhaseAxis, skewMatrix4]
  rw [hJ, ← skewMatrix4_pfaffian_sq_eq_det]
  norm_num [pfaffian4]

/-- Ordinary real determinants lose the sign of the quadratic interval. -/
theorem pauli_det (t x y z : ℝ) :
    (pauli t x y z).det = intervalSq t x y z ^ 2 := by
  simpa only [phasePauli, Matrix.det_mul, phase_det, one_mul] using
    phasePauli_det t x y z

/-- The representative of a displacement is the difference of representatives. -/
theorem pauli_sub (t₁ x₁ y₁ z₁ t₂ x₂ y₂ z₂ : ℝ) :
    pauli t₁ x₁ y₁ z₁ - pauli t₂ x₂ y₂ z₂ =
      pauli (t₁ - t₂) (x₁ - x₂) (y₁ - y₂) (z₁ - z₂) := by
  unfold pauli
  module

/-- Addition of four-vectors is addition of their real Pauli representatives. -/
theorem pauli_add (t₁ x₁ y₁ z₁ t₂ x₂ y₂ z₂ : ℝ) :
    pauli t₁ x₁ y₁ z₁ + pauli t₂ x₂ y₂ z₂ =
      pauli (t₁ + t₂) (x₁ + x₂) (y₁ + y₂) (z₁ + z₂) := by
  unfold pauli
  module

theorem pauli_det_eq_zero_iff (t x y z : ℝ) :
    (pauli t x y z).det = 0 ↔ intervalSq t x y z = 0 := by
  rw [pauli_det, sq_eq_zero_iff]

/-- Null separation is detected by the singularity of the difference matrix. -/
theorem pauli_sub_det_eq_zero_iff (t₁ x₁ y₁ z₁ t₂ x₂ y₂ z₂ : ℝ) :
    (pauli t₁ x₁ y₁ z₁ - pauli t₂ x₂ y₂ z₂).det = 0 ↔
      intervalSq (t₁ - t₂) (x₁ - x₂) (y₁ - y₂) (z₁ - z₂) = 0 := by
  rw [pauli_sub, pauli_det_eq_zero_iff]

/-- Unnormalized circular basis: in two-by-two blocks this is
`[[I, I], [J₂, -J₂]]`, with `J₂ = [[0,-1],[1,0]]`. -/
def circularBasis : Matrix4 :=
  !![1, 0, 1, 0;
     0, 1, 0, 1;
     0, -1, 0, 1;
     1, 0, -1, 0]

theorem circularBasis_transpose_mul :
    circularBasis.transpose * circularBasis = (2 : ℝ) • (1 : Matrix4) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [circularBasis, Matrix.transpose_apply, Matrix.mul_apply,
      Fin.sum_univ_four, Matrix.one_apply]

theorem circularBasis_mul_transpose :
    circularBasis * circularBasis.transpose = (2 : ℝ) • (1 : Matrix4) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [circularBasis, Matrix.transpose_apply, Matrix.mul_apply,
      Fin.sum_univ_four, Matrix.one_apply]

/-- Exact circular-coordinate transformation, with no square-root normalization. -/
theorem circularBasis_congruence (t x y z : ℝ) :
    circularBasis.transpose * pauli t x y z * circularBasis =
      (2 : ℝ) • pauli t z x y := by
  simp only [pauli_explicit]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [circularBasis, Matrix.transpose_apply, Matrix.mul_apply,
      Fin.sum_univ_four] <;> ring

def circularBasisInv : Matrix4 := (1 / 2 : ℝ) • circularBasis.transpose

theorem circularBasisInv_mul : circularBasisInv * circularBasis = 1 := by
  rw [circularBasisInv, smul_mul_assoc, circularBasis_transpose_mul]
  norm_num [smul_smul]

theorem circularBasis_mul_inv : circularBasis * circularBasisInv = 1 := by
  rw [circularBasisInv, mul_smul_comm, circularBasis_mul_transpose]
  norm_num [smul_smul]

/-- The corresponding genuine similarity transformation. -/
theorem circularBasis_similarity (t x y z : ℝ) :
    circularBasisInv * pauli t x y z * circularBasis = pauli t z x y := by
  rw [circularBasisInv, smul_mul_assoc, smul_mul_assoc,
    circularBasis_congruence]
  norm_num [smul_smul]

/-- A real timelike Clifford generator on the same four-dimensional carrier.
In two-by-two blocks this is `[[0,K],[-K,0]]`, `K = diag(1,-1)`. -/
def timeGamma : Matrix4 :=
  !![0, 0, 1, 0;
     0, 0, 0, -1;
     -1, 0, 0, 0;
     0, 1, 0, 0]

theorem timeGamma_sq : timeGamma * timeGamma = -(1 : Matrix4) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [timeGamma, Matrix.mul_apply, Fin.sum_univ_four,
      Matrix.one_apply]

/-- The timelike generator exchanges a Pauli vector with its cosolder. -/
theorem timeGamma_mul_pauli (t x y z : ℝ) :
    timeGamma * pauli t x y z = pauli t (-x) (-y) (-z) * timeGamma := by
  simp only [pauli_explicit]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [timeGamma, Matrix.mul_apply, Fin.sum_univ_four] <;> ring

theorem timeGamma_det : timeGamma.det = 1 := by
  have hG : timeGamma = skewMatrix4 (0 : ℝ) 1 0 0 (-1) 0 := by
    ext i j
    fin_cases i <;> fin_cases j <;> norm_num [timeGamma, skewMatrix4]
  rw [hG, ← skewMatrix4_pfaffian_sq_eq_det]
  norm_num [pfaffian4]

/-- The real Dirac vector uses the same real Pauli representative. -/
def diracVector (t x y z : ℝ) : Matrix4 :=
  timeGamma * pauli t (-x) (-y) (-z)

/-- This real Clifford square has the explicitly opposite signature `(-+++)`. -/
theorem diracVector_sq (t x y z : ℝ) :
    diracVector t x y z * diracVector t x y z =
      (-intervalSq t x y z) • (1 : Matrix4) := by
  simp only [diracVector, pauli_explicit]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [timeGamma, intervalSq, Matrix.mul_apply, Fin.sum_univ_four] <;> ring

/-- Polarization retains the real Clifford signature `(-+++)`. -/
theorem diracVector_anticomm (t₁ x₁ y₁ z₁ t₂ x₂ y₂ z₂ : ℝ) :
    diracVector t₁ x₁ y₁ z₁ * diracVector t₂ x₂ y₂ z₂ +
      diracVector t₂ x₂ y₂ z₂ * diracVector t₁ x₁ y₁ z₁ =
      (-2 * (t₁ * t₂ - x₁ * x₂ - y₁ * y₂ - z₁ * z₂)) • (1 : Matrix4) := by
  simp only [diracVector, pauli_explicit]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [timeGamma] <;> ring

theorem diracVector_det (t x y z : ℝ) :
    (diracVector t x y z).det = intervalSq t x y z ^ 2 := by
  simp [diracVector, Matrix.det_mul, timeGamma_det, pauli_det, intervalSq]

/-- The real Pauli phase is exactly the volume product of the real Dirac
generators on this carrier, with signature `(-+++)`. -/
theorem diracVolume_eq_phase :
    timeGamma * ((-timeGamma) * realSigma1) *
      ((-timeGamma) * realSigma2) * ((-timeGamma) * realSigma3) =
        realPhaseAxis := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [timeGamma, realSigma1, realSigma2, realSigma3, realPhaseAxis,
      Matrix.mul_apply, Fin.sum_univ_four]

end InfoGeometry.Canonical.RealPauliPfaffianKernel

end
