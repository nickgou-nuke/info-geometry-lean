/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Analysis.MatrixTraceQuadratic
import InfoGeometry.Geometry.AssociativeGaugeConnection

/-! # Native first derivatives of a full matrix curvature energy

Connections are finite families of arbitrary complex matrices. The base
operators are continuous real-linear maps. No commutativity of matrix
coefficients is assumed. Leibniz and commuting-base hypotheses are needed
for geometric gauge identities, but not for differentiation of this actual
polynomial curvature map.
-/

noncomputable section

namespace InfoGeometry.Geometry.MatrixCurvatureEnergy

open scoped Matrix Matrix.Norms.L2Operator
open InfoGeometry.Analysis.MatrixTraceQuadratic

variable {ι n : Type*} [Fintype ι] [Fintype n] [DecidableEq n]
local notation "Mat" => Matrix n n ℂ
local notation "Conn" => ι → Mat

/-- The existing associative curvature on each pair of directions. -/
def curvatureEntry (D : ι → Mat →L[ℝ] Mat) (A : Conn) (i j : ι) : Mat :=
  D i (A j) - D j (A i) + (A i * A j - A j * A i)

omit [Fintype ι] in
theorem curvatureEntry_eq (D : ι → Mat →L[ℝ] Mat) (A : Conn) (i j : ι) :
    curvatureEntry D A i j = AssociativeGaugeConnection.curvature
      (D i).toLinearMap (D j).toLinearMap (A i) (A j) := by
  simp only [curvatureEntry, AssociativeGaugeConnection.curvature,
    ContinuousLinearMap.coe_coe]
  noncomm_ring

/-- Full first differential, including both ordered product variations. -/
def curvatureDifferential (D : ι → Mat →L[ℝ] Mat) (A : Conn) (i j : ι) :
    Conn →L[ℝ] Mat :=
  (D i).comp (ContinuousLinearMap.proj j) -
    (D j).comp (ContinuousLinearMap.proj i) +
    ((ContinuousLinearMap.mul ℝ Mat).flip (A j)).comp (ContinuousLinearMap.proj i) +
    (ContinuousLinearMap.mul ℝ Mat (A i)).comp (ContinuousLinearMap.proj j) -
    ((ContinuousLinearMap.mul ℝ Mat).flip (A i)).comp (ContinuousLinearMap.proj j) -
    (ContinuousLinearMap.mul ℝ Mat (A j)).comp (ContinuousLinearMap.proj i)

omit [Fintype ι] in
@[simp] theorem curvatureDifferential_apply
    (D : ι → Mat →L[ℝ] Mat) (A B : Conn) (i j : ι) :
    curvatureDifferential D A i j B =
      D i (B j) - D j (B i) + B i * A j + A i * B j - B j * A i - A j * B i := rfl

theorem hasFDerivAt_curvatureEntry
    (D : ι → Mat →L[ℝ] Mat) (A : Conn) (i j : ι) :
    HasFDerivAt (fun B => curvatureEntry D B i j)
      (curvatureDifferential D A i j) A := by
  have hi := (ContinuousLinearMap.proj i : Conn →L[ℝ] Mat).hasFDerivAt (x := A)
  have hj := (ContinuousLinearMap.proj j : Conn →L[ℝ] Mat).hasFDerivAt (x := A)
  have h := ((D i).hasFDerivAt.comp A hj).sub ((D j).hasFDerivAt.comp A hi)
    |>.add ((hi.mul' hj).sub (hj.mul' hi))
  convert! h using 1
  ext B
  simp [curvatureDifferential, ContinuousLinearMap.comp_apply]
  noncomm_ring

omit [Fintype ι] in
theorem curvatureEntry_add_smul
    (D : ι → Mat →L[ℝ] Mat) (A B : Conn) (i j : ι) (t : ℝ) :
    curvatureEntry D (A + t • B) i j = curvatureEntry D A i j +
      t • curvatureDifferential D A i j B + t ^ 2 • (B i * B j - B j * B i) := by
  simp only [curvatureEntry, curvatureDifferential_apply, Pi.add_apply, Pi.smul_apply,
    map_add, map_smul, add_mul, mul_add, smul_mul_assoc, mul_smul_comm,
    smul_smul, smul_add, smul_sub, pow_two]
  module

/-- Positive finite curvature action with every ordered direction pair counted. -/
def curvatureEnergy (D : ι → Mat →L[ℝ] Mat) (A : Conn) : ℝ :=
  ∑ i, ∑ j, halfTraceSquare (curvatureEntry D A i j)

/-- The continuous linear functional representing the actual first derivative. -/
def curvatureEnergyDifferential (D : ι → Mat →L[ℝ] Mat) (A : Conn) :
    Conn →L[ℝ] ℝ :=
  ∑ i, ∑ j, (tracePair (curvatureEntry D A i j)).comp (curvatureDifferential D A i j)

@[simp] theorem curvatureEnergyDifferential_apply
    (D : ι → Mat →L[ℝ] Mat) (A B : Conn) :
    curvatureEnergyDifferential D A B =
      ∑ i, ∑ j, tracePair (curvatureEntry D A i j) (curvatureDifferential D A i j B) := by
  simp [curvatureEnergyDifferential]

theorem hasFDerivAt_curvatureEnergy (D : ι → Mat →L[ℝ] Mat) (A : Conn) :
    HasFDerivAt (curvatureEnergy D) (curvatureEnergyDifferential D A) A := by
  unfold curvatureEnergy curvatureEnergyDifferential
  apply HasFDerivAt.fun_sum
  intro i _
  apply HasFDerivAt.fun_sum
  intro j _
  exact (hasFDerivAt_halfTraceSquare (curvatureEntry D A i j)).comp A
    (hasFDerivAt_curvatureEntry D A i j)

theorem fderiv_curvatureEnergy_apply (D : ι → Mat →L[ℝ] Mat) (A B : Conn) :
    fderiv ℝ (curvatureEnergy D) A B =
      ∑ i, ∑ j, tracePair (curvatureEntry D A i j) (curvatureDifferential D A i j B) := by
  rw [(hasFDerivAt_curvatureEnergy D A).fderiv, curvatureEnergyDifferential_apply]

theorem curvatureEnergy_nonneg (D : ι → Mat →L[ℝ] Mat) (A : Conn) :
    0 ≤ curvatureEnergy D A := by
  apply Finset.sum_nonneg
  intro i _
  apply Finset.sum_nonneg
  intro j _
  exact mul_nonneg (by norm_num) (tracePair_self_nonneg _)

theorem curvatureEnergy_eq_zero_iff (D : ι → Mat →L[ℝ] Mat) (A : Conn) :
    curvatureEnergy D A = 0 ↔ ∀ i j, curvatureEntry D A i j = 0 := by
  have hpos (i j : ι) : 0 ≤ halfTraceSquare (curvatureEntry D A i j) :=
    mul_nonneg (by norm_num) (tracePair_self_nonneg _)
  simp only [curvatureEnergy,
    Finset.sum_eq_zero_iff_of_nonneg (fun i _ => Finset.sum_nonneg (fun j _ => hpos i j)),
    Finset.mem_univ, forall_true_left]
  apply forall_congr'
  intro i
  rw [Finset.sum_eq_zero_iff_of_nonneg (fun j _ => hpos i j)]
  simp only [Finset.mem_univ, forall_true_left]
  apply forall_congr'
  intro j
  rw [halfTraceSquare, mul_eq_zero, or_iff_right (by norm_num : ¬(1 / 2 : ℝ) = 0),
    tracePair_self_eq_zero_iff]

theorem fderiv_curvatureEnergy_eq_zero_of_flat
    (D : ι → Mat →L[ℝ] Mat) (A : Conn)
    (hA : ∀ i j, curvatureEntry D A i j = 0) :
    fderiv ℝ (curvatureEnergy D) A = 0 := by
  ext B
  simp [fderiv_curvatureEnergy_apply, hA]

end InfoGeometry.Geometry.MatrixCurvatureEnergy
