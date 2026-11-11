/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Twistor.ConstituentColumnEquivalence
import InfoGeometry.LinearAlgebra.SplitHadamard

/-!
# Ordered algebra of the existing infinity-raising matrix

The matrix `infinityRaisingMatrix` is reused without changing carriers. Its
ordinary coordinate conjugate transpose gives a square-zero CAR partner,
complementary projectors, and two anticommuting involutions. These instantiate
the generic unnormalized split Hadamard transform on the full matrix ring.

All deformations below are complex-linear matrix operations. The existing
`infinityConjugate` operation additionally conjugates its input, as proved by
`columnEquiv_infinityConjugate`; it is not identified with matrix multiplication
alone. The conjugate-product identity records the different square for this
antilinear interpretation and its real-parameter specialization. The symbol `ᴴ`
here denotes coordinate conjugate transpose, not a Witt adjoint. No
spacetime-curvature interpretation is asserted.
-/

noncomputable section

namespace InfoGeometry.Twistor.InfinityRaisingAlgebra

open ConstituentColumnEquivalence
open InfoGeometry.LinearAlgebra.SplitHadamard
open scoped Matrix

local notation "A" => infinityRaisingMatrix

theorem raising_sq_zero : A * A = 0 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [infinityRaisingMatrix, Matrix.mul_apply, Fin.sum_univ_four]

theorem raising_adjoint_sq_zero : Aᴴ * Aᴴ = 0 := by
  have h := congrArg (fun M : Matrix (Fin 4) (Fin 4) ℂ => Mᴴ) raising_sq_zero
  simpa only [Matrix.conjTranspose_mul, Matrix.conjTranspose_zero] using h

/-- The two ordered products sum to the identity on all four coordinates. -/
theorem raising_car : A * Aᴴ + Aᴴ * A = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [infinityRaisingMatrix, Matrix.mul_apply, Matrix.conjTranspose_apply,
      Fin.sum_univ_four, Matrix.one_apply]

/-- The products cannot be interchanged: their upper-left entries differ. -/
theorem raising_noncommute : A * Aᴴ ≠ Aᴴ * A := by
  intro h
  have h00 := congrArg (fun M : Matrix (Fin 4) (Fin 4) ℂ => M 0 0) h
  norm_num [infinityRaisingMatrix, Matrix.mul_apply, Matrix.conjTranspose_apply,
    Fin.sum_univ_four] at h00

def upperProjector : Matrix (Fin 4) (Fin 4) ℂ := A * Aᴴ
def lowerProjector : Matrix (Fin 4) (Fin 4) ℂ := Aᴴ * A

theorem upper_add_lower : upperProjector + lowerProjector = 1 := raising_car

theorem upper_mul_lower : upperProjector * lowerProjector = 0 := by
  calc
    upperProjector * lowerProjector = A * (Aᴴ * Aᴴ) * A := by
      simp only [upperProjector, lowerProjector, mul_assoc]
    _ = 0 := by rw [raising_adjoint_sq_zero, mul_zero, zero_mul]

theorem lower_mul_upper : lowerProjector * upperProjector = 0 := by
  calc
    lowerProjector * upperProjector = Aᴴ * (A * A) * Aᴴ := by
      simp only [upperProjector, lowerProjector, mul_assoc]
    _ = 0 := by rw [raising_sq_zero, mul_zero, zero_mul]

theorem upperProjector_sq : upperProjector * upperProjector = upperProjector := by
  calc
    upperProjector * upperProjector =
        upperProjector * upperProjector + upperProjector * lowerProjector := by
      rw [upper_mul_lower, add_zero]
    _ = upperProjector * (upperProjector + lowerProjector) := (mul_add _ _ _).symm
    _ = upperProjector := by rw [upper_add_lower, mul_one]

theorem lowerProjector_sq : lowerProjector * lowerProjector = lowerProjector := by
  calc
    lowerProjector * lowerProjector =
        lowerProjector * upperProjector + lowerProjector * lowerProjector := by
      rw [lower_mul_upper, zero_add]
    _ = lowerProjector * (upperProjector + lowerProjector) := (mul_add _ _ _).symm
    _ = lowerProjector := by rw [upper_add_lower, mul_one]

theorem upperProjector_conjTranspose : upperProjectorᴴ = upperProjector := by
  simp [upperProjector]

theorem lowerProjector_conjTranspose : lowerProjectorᴴ = lowerProjector := by
  simp [lowerProjector]

def infinityGrading : Matrix (Fin 4) (Fin 4) ℂ := upperProjector - lowerProjector
def infinityExchange : Matrix (Fin 4) (Fin 4) ℂ := A + Aᴴ

theorem infinityGrading_sq : infinityGrading * infinityGrading = 1 := by
  calc
    infinityGrading * infinityGrading = upperProjector + lowerProjector := by
      dsimp [infinityGrading]
      noncomm_ring [upperProjector_sq, lowerProjector_sq, upper_mul_lower, lower_mul_upper]
    _ = 1 := upper_add_lower

theorem infinityExchange_sq : infinityExchange * infinityExchange = 1 := by
  calc
    infinityExchange * infinityExchange = A * Aᴴ + Aᴴ * A := by
      dsimp [infinityExchange]
      noncomm_ring [raising_sq_zero, raising_adjoint_sq_zero]
    _ = 1 := raising_car

theorem infinityExchange_grading_anticommute :
    infinityExchange * infinityGrading + infinityGrading * infinityExchange = 0 := by
  have hA (M : Matrix (Fin 4) (Fin 4) ℂ) : A * (A * M) = 0 := by
    rw [← mul_assoc, raising_sq_zero, zero_mul]
  have hB (M : Matrix (Fin 4) (Fin 4) ℂ) : Aᴴ * (Aᴴ * M) = 0 := by
    rw [← mul_assoc, raising_adjoint_sq_zero, zero_mul]
  dsimp [infinityExchange, infinityGrading, upperProjector, lowerProjector]
  noncomm_ring [raising_sq_zero, raising_adjoint_sq_zero, hA, hB]

/-- A complex-linear deformation using the existing matrix and its coordinate adjoint. -/
def raisingDeformation (lam : ℂ) : Matrix (Fin 4) (Fin 4) ℂ := A - lam • Aᴴ

theorem raisingDeformation_sq (lam : ℂ) :
    raisingDeformation lam * raisingDeformation lam = (-lam) • (1 : Matrix (Fin 4) (Fin 4) ℂ) := by
  calc
    raisingDeformation lam * raisingDeformation lam = (-lam) • (A * Aᴴ + Aᴴ * A) := by
      dsimp [raisingDeformation]
      simp only [sub_mul, mul_sub, smul_mul_assoc, mul_smul_comm,
        raising_sq_zero, raising_adjoint_sq_zero, smul_smul, smul_zero, smul_add, neg_smul]
      abel
    _ = (-lam) • (1 : Matrix (Fin 4) (Fin 4) ℂ) := by rw [raising_car]

theorem raisingDeformation_left_inverse (lam : ℂ) (hlam : lam ≠ 0) :
    ((-lam)⁻¹ • raisingDeformation lam) * raisingDeformation lam = 1 := by
  rw [smul_mul_assoc, raisingDeformation_sq, inv_smul_smul₀ (neg_ne_zero.mpr hlam)]

theorem raisingDeformation_right_inverse (lam : ℂ) (hlam : lam ≠ 0) :
    raisingDeformation lam * ((-lam)⁻¹ • raisingDeformation lam) = 1 := by
  rw [mul_smul_comm, raisingDeformation_sq, inv_smul_smul₀ (neg_ne_zero.mpr hlam)]

/-- Composing the antilinear operation twice conjugates its scalar parameter
on the upper projector. This is a product with entrywise conjugation. -/
theorem raisingDeformation_conjugate_product (lam : ℂ) :
    raisingDeformation lam * (raisingDeformation lam).map star =
      (-(star lam)) • upperProjector - lam • lowerProjector := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [raisingDeformation, upperProjector, lowerProjector, infinityRaisingMatrix,
      Matrix.mul_apply, Matrix.conjTranspose_apply, Fin.sum_univ_four]

/-- For a real parameter the conjugate-product square has the same scalar
value as the complex-linear square. -/
theorem raisingDeformation_real_conjugate_product (lam : ℝ) :
    raisingDeformation (lam : ℂ) * (raisingDeformation (lam : ℂ)).map star =
      (-(lam : ℂ)) • (1 : Matrix (Fin 4) (Fin 4) ℂ) := by
  rw [raisingDeformation_conjugate_product]
  simpa [smul_add, neg_smul, sub_eq_add_neg] using
    congrArg (fun M : Matrix (Fin 4) (Fin 4) ℂ => (-(lam : ℂ)) • M) upper_add_lower

/-- The generic ordered transform acts on the actual noncommutative matrix ring. -/
theorem infinity_splitHadamard_sq (X : Matrix (Fin 4) (Fin 4) ℂ) :
    splitHadamard infinityGrading infinityExchange
      (splitHadamard infinityGrading infinityExchange X) = 2 • X :=
  splitHadamard_sq infinityGrading infinityExchange X
    infinityGrading_sq infinityExchange_sq infinityExchange_grading_anticommute

end InfoGeometry.Twistor.InfinityRaisingAlgebra
