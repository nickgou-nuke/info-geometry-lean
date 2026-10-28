/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Geometry.MatrixCurvatureEnergy

/-! # The native curvature-energy Hessian with its curvature correction

The first derivative is differentiated as a continuous-linear-map-valued
function on the full finite matrix connection space. The resulting Hessian
contains both a positive square and the background-curvature term.
-/

noncomputable section

namespace InfoGeometry.Geometry.MatrixCurvatureEnergy

open scoped Matrix Matrix.Norms.L2Operator
open InfoGeometry.Analysis.MatrixTraceQuadratic

variable {ι n : Type*} [Fintype ι] [Fintype n] [DecidableEq n]
local notation "Mat" => Matrix n n ℂ
local notation "Conn" => ι → Mat

/-- Continuous bilinear second differential of the actual curvature map. -/
def curvatureBilinear (i j : ι) : Conn →L[ℝ] Conn →L[ℝ] Mat :=
  ((ContinuousLinearMap.compL ℝ Conn Mat Mat).flip (ContinuousLinearMap.proj i)).comp
      ((ContinuousLinearMap.mul ℝ Mat).flip.comp (ContinuousLinearMap.proj j)) +
    ((ContinuousLinearMap.compL ℝ Conn Mat Mat).flip (ContinuousLinearMap.proj j)).comp
      ((ContinuousLinearMap.mul ℝ Mat).comp (ContinuousLinearMap.proj i)) -
    ((ContinuousLinearMap.compL ℝ Conn Mat Mat).flip (ContinuousLinearMap.proj j)).comp
      ((ContinuousLinearMap.mul ℝ Mat).flip.comp (ContinuousLinearMap.proj i)) -
    ((ContinuousLinearMap.compL ℝ Conn Mat Mat).flip (ContinuousLinearMap.proj i)).comp
      ((ContinuousLinearMap.mul ℝ Mat).comp (ContinuousLinearMap.proj j))

@[simp] theorem curvatureBilinear_apply (i j : ι) (B C : Conn) :
    curvatureBilinear i j B C =
      C i * B j + B i * C j - C j * B i - B j * C i := rfl

theorem curvatureBilinear_comm (i j : ι) (B C : Conn) :
    curvatureBilinear i j B C = curvatureBilinear i j C B := by
  simp only [curvatureBilinear_apply]
  noncomm_ring

theorem curvatureBilinear_self (i j : ι) (B : Conn) :
    curvatureBilinear i j B B = (2 : ℝ) • (B i * B j - B j * B i) := by
  simp only [curvatureBilinear_apply, two_smul]
  noncomm_ring

theorem hasFDerivAt_curvatureDifferential
    (D : ι → Mat →L[ℝ] Mat) (A : Conn) (i j : ι) :
    HasFDerivAt (fun B => curvatureDifferential D B i j) (curvatureBilinear i j) A := by
  let d₀ : Conn →L[ℝ] Mat := (D i).comp (ContinuousLinearMap.proj j) -
    (D j).comp (ContinuousLinearMap.proj i)
  have h := (curvatureBilinear (n := n) i j).hasFDerivAt (x := A) |>.const_add d₀
  convert! h using 1
  ext B C
  simp [d₀, curvatureDifferential, curvatureBilinear, ContinuousLinearMap.comp_apply]
  noncomm_ring

/-- The full continuous bilinear Hessian, obtained by the native chain rule. -/
def curvatureEnergyHessian (D : ι → Mat →L[ℝ] Mat) (A : Conn) :
    Conn →L[ℝ] Conn →L[ℝ] ℝ :=
  ∑ i, ∑ j,
    ((ContinuousLinearMap.compL ℝ Conn Mat ℝ).precompR Conn
      (tracePair (curvatureEntry D A i j)) (curvatureBilinear i j) +
    (ContinuousLinearMap.compL ℝ Conn Mat ℝ).precompL Conn
      (tracePair.comp (curvatureDifferential D A i j)) (curvatureDifferential D A i j))

theorem curvatureEnergyHessian_apply
    (D : ι → Mat →L[ℝ] Mat) (A B C : Conn) :
    curvatureEnergyHessian D A B C = ∑ i, ∑ j,
      (tracePair (curvatureDifferential D A i j B) (curvatureDifferential D A i j C) +
        tracePair (curvatureEntry D A i j) (curvatureBilinear i j B C)) := by
  simp only [curvatureEnergyHessian, sum_apply, add_apply,
    ContinuousLinearMap.precompR_apply, ContinuousLinearMap.precompL_apply,
    ContinuousLinearMap.compL_apply, ContinuousLinearMap.comp_apply]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  exact add_comm _ _

theorem hasFDerivAt_curvatureEnergyDifferential
    (D : ι → Mat →L[ℝ] Mat) (A : Conn) :
    HasFDerivAt (curvatureEnergyDifferential D) (curvatureEnergyHessian D A) A := by
  unfold curvatureEnergyDifferential curvatureEnergyHessian
  exact HasFDerivAt.fun_sum fun i _ => HasFDerivAt.fun_sum fun j _ =>
    (ContinuousLinearMap.compL ℝ Conn Mat ℝ).hasFDerivAt_of_bilinear
      (tracePair.hasFDerivAt.comp A (hasFDerivAt_curvatureEntry D A i j))
      (hasFDerivAt_curvatureDifferential D A i j)

/-- Native Fréchet differentiation of the native first derivative. -/
theorem hasFDerivAt_fderiv_curvatureEnergy
    (D : ι → Mat →L[ℝ] Mat) (A : Conn) :
    HasFDerivAt (fderiv ℝ (curvatureEnergy D)) (curvatureEnergyHessian D A) A := by
  have h : fderiv ℝ (curvatureEnergy D) = curvatureEnergyDifferential D :=
    funext fun B => (hasFDerivAt_curvatureEnergy D B).fderiv
  rw [h]
  exact hasFDerivAt_curvatureEnergyDifferential D A

theorem fderiv2_curvatureEnergy_apply
    (D : ι → Mat →L[ℝ] Mat) (A B C : Conn) :
    fderiv ℝ (fderiv ℝ (curvatureEnergy D)) A B C = ∑ i, ∑ j,
      (tracePair (curvatureDifferential D A i j B) (curvatureDifferential D A i j C) +
        tracePair (curvatureEntry D A i j) (curvatureBilinear i j B C)) := by
  rw [(hasFDerivAt_fderiv_curvatureEnergy D A).fderiv, curvatureEnergyHessian_apply]

theorem curvatureEnergyHessian_symmetric
    (D : ι → Mat →L[ℝ] Mat) (A B C : Conn) :
    curvatureEnergyHessian D A B C = curvatureEnergyHessian D A C B := by
  simp only [curvatureEnergyHessian_apply]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  rw [tracePair_comm (curvatureDifferential D A i j B), curvatureBilinear_comm i j B C]

/-- The diagonal Hessian retains the full curvature-commutator correction. -/
theorem fderiv2_curvatureEnergy_self
    (D : ι → Mat →L[ℝ] Mat) (A B : Conn) :
    fderiv ℝ (fderiv ℝ (curvatureEnergy D)) A B B = ∑ i, ∑ j,
      (tracePair (curvatureDifferential D A i j B) (curvatureDifferential D A i j B) +
        2 * tracePair (curvatureEntry D A i j) (B i * B j - B j * B i)) := by
  simp only [fderiv2_curvatureEnergy_apply, curvatureBilinear_self, map_smul, smul_eq_mul]

/-- Flatness removes the background-curvature correction. -/
theorem fderiv2_curvatureEnergy_of_flat
    (D : ι → Mat →L[ℝ] Mat) (A B C : Conn)
    (hA : ∀ i j, curvatureEntry D A i j = 0) :
    fderiv ℝ (fderiv ℝ (curvatureEnergy D)) A B C =
      ∑ i, ∑ j, tracePair (curvatureDifferential D A i j B)
        (curvatureDifferential D A i j C) := by
  simp only [fderiv2_curvatureEnergy_apply, hA, map_zero, zero_apply, add_zero]

theorem fderiv2_curvatureEnergy_nonneg_of_flat
    (D : ι → Mat →L[ℝ] Mat) (A B : Conn)
    (hA : ∀ i j, curvatureEntry D A i j = 0) :
    0 ≤ fderiv ℝ (fderiv ℝ (curvatureEnergy D)) A B B := by
  rw [fderiv2_curvatureEnergy_of_flat D A B B hA]
  exact Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => tracePair_self_nonneg _

theorem fderiv2_curvatureEnergy_eq_zero_iff_of_flat
    (D : ι → Mat →L[ℝ] Mat) (A B : Conn)
    (hA : ∀ i j, curvatureEntry D A i j = 0) :
    fderiv ℝ (fderiv ℝ (curvatureEnergy D)) A B B = 0 ↔
      ∀ i j, curvatureDifferential D A i j B = 0 := by
  rw [fderiv2_curvatureEnergy_of_flat D A B B hA]
  simp only [Finset.sum_eq_zero_iff_of_nonneg
      (fun i _ => Finset.sum_nonneg (fun j _ => tracePair_self_nonneg _)),
    Finset.mem_univ, forall_true_left]
  apply forall_congr'
  intro i
  simp only [Finset.sum_eq_zero_iff_of_nonneg
      (fun j _ => tracePair_self_nonneg (curvatureDifferential D A i j B)),
    Finset.mem_univ, forall_true_left, tracePair_self_eq_zero_iff]

end InfoGeometry.Geometry.MatrixCurvatureEnergy
