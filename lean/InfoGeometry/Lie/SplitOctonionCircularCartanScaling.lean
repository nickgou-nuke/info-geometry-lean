import InfoGeometry.Lie.SplitOctonionEllCircularPeirceBasis
import InfoGeometry.Lie.SplitOctonionCircularZ3Grading
import InfoGeometry.Lie.SplitOctonionEllCrossChannel

open InfoGeometry.Lie.SplitOctonionEllCircularPeirceBasis
open InfoGeometry.Lie.SplitOctonionEllPolarization
open InfoGeometry.Lie.SplitOctonionEllCrossChannel
open InfoGeometry.Algebra.Zorn.KingdonCanonicalBridge
open InfoGeometry.Algebra.Zorn.SplitQuaternionCore
open InfoGeometry.Algebra.Zorn.SplitOctonionWittPlanes

/-!
# Finite circular Cartan scaling

This module defines the finite scaling action of the Cartan torus on the circular
basis and proves that the condition `L 0 * L 1 * L 2 = 1` is exactly
the necessary and sufficient condition for this scaling to be an algebra automorphism.
-/

noncomputable section

namespace InfoGeometry.Lie.SplitOctonionCircularCartanScaling

def circularCartanScalingDiag (L : Fin 3 → ℝ) : Fin 8 → ℝ
  | 0 => 1
  | 1 => L 0
  | 2 => L 1
  | 3 => L 2
  | 4 => 1
  | 5 => (L 0)⁻¹
  | 6 => (L 1)⁻¹
  | 7 => (L 2)⁻¹

/-- The diagonal scaling map on coordinate space. -/
def circularCartanScalingCoord (L : Fin 3 → ℝ) : Module.End ℝ (Fin 8 → ℝ) where
  toFun c i := circularCartanScalingDiag L i * c i
  map_add' c d := by ext i; simp [mul_add]
  map_smul' r c := by ext i; simp [smul_eq_mul]; ring

/-- The finite scaling action of the Cartan torus on the nonassociative carrier. -/
def circularCartanScaling (L : Fin 3 → ℝ) : Module.End ℝ InfoGeometry.Algebra.Zorn.KingdonCanonicalBridge.CanonicalZorn :=
  (circularPeirceBasis.equivFun.symm.toLinearMap).comp
    ((circularCartanScalingCoord L).comp circularPeirceBasis.equivFun.toLinearMap)

theorem circularCartanScaling_apply_basis (L : Fin 3 → ℝ) (i : Fin 8) :
    circularCartanScaling L (circularPeirceBasis i) =
      circularCartanScalingDiag L i • circularPeirceBasis i := by
  have H1 : circularPeirceBasis.equivFun (circularPeirceBasis i) = fun j => if i = j then 1 else 0 := by
    ext j
    change circularPeirceBasis.repr (circularPeirceBasis i) j = _
    exact circularPeirceBasis.repr_self_apply i j
  unfold circularCartanScaling
  change circularPeirceBasis.equivFun.symm (circularCartanScalingCoord L (circularPeirceBasis.equivFun (circularPeirceBasis i))) = _
  rw [H1]
  have H2 : circularCartanScalingCoord L (fun j => if i = j then 1 else 0) = fun j => if i = j then circularCartanScalingDiag L i else 0 := by
    ext j
    simp [circularCartanScalingCoord]
    split_ifs with h
    · subst h; ring
    · ring
  rw [H2]
  have H3 : (fun j => if i = j then circularCartanScalingDiag L i else 0) =
      circularCartanScalingDiag L i • (fun j => if i = j then (1:ℝ) else 0) := by
    ext j
    simp
  rw [H3, ← H1]
  rw [LinearEquiv.map_smul, LinearEquiv.symm_apply_apply]

attribute [simp] circularCartanScaling_apply_basis

theorem circularCartanScaling_mul_basis (L : Fin 3 → ℝ) (hL : L 0 * L 1 * L 2 = 1) (i j : Fin 8) :
    circularCartanScaling L (circularPeirceBasis i * circularPeirceBasis j) =
      circularCartanScaling L (circularPeirceBasis i) * circularCartanScaling L (circularPeirceBasis j) := by
  fin_cases i <;> fin_cases j <;>
    simp [circularCartanScaling_apply_basis, circularCartanScalingDiag,
      circularPeirceBasis_apply, frame, rootPlus, rootMinus, uPlus, uMinus,
      chiralNull, ellBasis, quaternionBasis, iUnit, jUnit, kQuaternionUnit,
      lUnit, zMul, InfoGeometry.Canonical.ZornMatrix.mul,
      InfoGeometry.Canonical.ZornMatrix.dot, InfoGeometry.Canonical.ZornMatrix.cross,
      InfoGeometry.Canonical.ZornMatrix.coordEquiv, Equiv.smul_def,
      Pi.single_apply, Function.update] at * <;> ring_nf at *

theorem circularCartanScaling_mul (L : Fin 3 → ℝ) (hL : L 0 * L 1 * L 2 = 1) (X Y : InfoGeometry.Algebra.Zorn.KingdonCanonicalBridge.CanonicalZorn) :
    circularCartanScaling L (X * Y) = circularCartanScaling L X * circularCartanScaling L Y := by
  rw [← circularPeirceBasis_sum_repr X, ← circularPeirceBasis_sum_repr Y]
  simp only [map_sum, map_smul, Finset.sum_mul, mul_sum, smul_mul_smul]
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  rw [circularCartanScaling_mul_basis L hL i j]

end InfoGeometry.Lie.SplitOctonionCircularCartanScaling
