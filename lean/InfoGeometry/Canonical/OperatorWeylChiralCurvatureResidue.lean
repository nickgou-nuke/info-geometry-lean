/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import Mathlib.Tactic
import InfoGeometry.Canonical.OperatorWeylChiralCurvatureBlocks

/-!
# InfoGeometry.Canonical.OperatorWeylChiralCurvatureResidue

Explicit commutator coordinates of the two ordered Weyl curvature blocks.

The parent owner proves that an operator-valued Weyl odd square has diagonal
blocks `σ(A) \barσ(A)` and `\barσ(A) σ(A)`.  This file expands those blocks
without assigning a geometric self-duality label.  Every departure from the
scalar Minkowski quadratic channel is written as an actual commutator of
operator coefficients.
-/

set_option maxHeartbeats 1000000

noncomputable section

namespace InfoGeometry.Canonical.OperatorWeylChiralCurvatureResidue

open Matrix
open InfoGeometry.Optics.OperatorCausalSoldering
open InfoGeometry.Canonical.OperatorWeylChiralCurvatureBlocks

variable {W : Type*} [AddCommGroup W] [Module ℂ W]

abbrev EndW (W : Type*) [AddCommGroup W] [Module ℂ W] := Module.End ℂ W
abbrev OperatorMat2 (W : Type*) [AddCommGroup W] [Module ℂ W] :=
  Matrix (Fin 2) (Fin 2) (EndW W)

/-- Ring commutator of operator coefficients. -/
def opComm (x y : EndW W) : EndW W := x * y - y * x

/-- Symmetric Minkowski quadratic channel of an operator-valued four-vector. -/
def operatorMinkowskiQuadratic (v : OperatorFourVector W) : EndW W :=
  v 0 * v 0 - v 1 * v 1 - v 2 * v 2 - v 3 * v 3

private theorem algebraMap_I_mul_self (W : Type*) [AddCommGroup W] [Module ℂ W] :
    (algebraMap ℂ (EndW W)) Complex.I * (algebraMap ℂ (EndW W)) Complex.I = -1 := by
  rw [← (algebraMap ℂ (EndW W)).map_mul, Complex.I_mul_I]
  simp

/-- Move the central `I` to the front of a triple product. -/
private theorem mul_mul_I (a b : EndW W) :
    a * (b * (algebraMap ℂ (EndW W)) Complex.I) =
      (algebraMap ℂ (EndW W)) Complex.I * (a * b) := by
  rw [← mul_assoc]
  exact (Algebra.commutes Complex.I (a * b)).symm

/-- Move the central `I` to the front when it precedes the right coefficient. -/
private theorem mul_I_mul (a b : EndW W) :
    a * ((algebraMap ℂ (EndW W)) Complex.I * b) =
      (algebraMap ℂ (EndW W)) Complex.I * (a * b) := by
  rw [Algebra.commutes Complex.I b]
  exact mul_mul_I a b

/-- The `I` on both sides of a coefficient cancels to a minus sign. -/
private theorem I_mul_mul_I (a : EndW W) :
    (algebraMap ℂ (EndW W)) Complex.I *
        (a * (algebraMap ℂ (EndW W)) Complex.I) = -a := by
  rw [← mul_assoc, Algebra.commutes, mul_assoc]
  rw [algebraMap_I_mul_self]
  simp

/-- Two central `I`s in front of a coefficient give a minus sign. -/
private theorem I_mul_I_mul (x : EndW W) :
    (algebraMap ℂ (EndW W)) Complex.I *
        ((algebraMap ℂ (EndW W)) Complex.I * x) = -x := by
  rw [← mul_assoc, algebraMap_I_mul_self]
  simp

/-- The same cancellation when the inner `I` precedes the repeated coefficient. -/
private theorem I_mul_mul_I' (a : EndW W) :
    (algebraMap ℂ (EndW W)) Complex.I *
        (a * ((algebraMap ℂ (EndW W)) Complex.I * a)) = -(a * a) := by
  rw [Algebra.commutes Complex.I a, ← mul_assoc]
  exact I_mul_mul_I (a * a)

/-- Exact left Weyl block: scalar quadratic channel plus commutator residue. -/
theorem leftCurvatureBlock_explicit (v : OperatorFourVector W) :
    leftCurvatureBlock v =
      !![operatorMinkowskiQuadratic v - opComm (v 0) (v 3) -
            Complex.I • opComm (v 1) (v 2),
          -opComm (v 0) (v 1) + opComm (v 1) (v 3) +
            Complex.I • (opComm (v 0) (v 2) + opComm (v 3) (v 2));
         -opComm (v 0) (v 1) - opComm (v 1) (v 3) -
            Complex.I • opComm (v 0) (v 2) +
            Complex.I • opComm (v 3) (v 2),
          operatorMinkowskiQuadratic v + opComm (v 0) (v 3) +
            Complex.I • opComm (v 1) (v 2)] := by
  apply Matrix.ext
  intro i j
  fin_cases i <;> fin_cases j <;>
    simp [leftCurvatureBlock, operatorSoldering_apply, operatorCoSoldering,
      operatorMinkowskiQuadratic, opComm, Matrix.mul_apply,
      Fin.sum_univ_two, Algebra.smul_def]
    <;> noncomm_ring
    <;> simp [mul_I_mul, I_mul_I_mul]
    <;> abel

/-- Exact right Weyl block, with the reversed operator ordering retained. -/
theorem rightCurvatureBlock_explicit (v : OperatorFourVector W) :
    rightCurvatureBlock v =
      !![operatorMinkowskiQuadratic v + opComm (v 0) (v 3) -
            Complex.I • opComm (v 1) (v 2),
          opComm (v 0) (v 1) + opComm (v 1) (v 3) -
            Complex.I • opComm (v 0) (v 2) +
            Complex.I • opComm (v 3) (v 2);
         opComm (v 0) (v 1) - opComm (v 1) (v 3) +
            Complex.I • opComm (v 0) (v 2) +
            Complex.I • opComm (v 3) (v 2),
          operatorMinkowskiQuadratic v - opComm (v 0) (v 3) +
            Complex.I • opComm (v 1) (v 2)] := by
  apply Matrix.ext
  intro i j
  fin_cases i <;> fin_cases j <;>
    simp [rightCurvatureBlock, operatorSoldering_apply, operatorCoSoldering,
      operatorMinkowskiQuadratic, opComm, Matrix.mul_apply,
      Fin.sum_univ_two, Algebra.smul_def]
    <;> noncomm_ring
    <;> simp [mul_I_mul, I_mul_I_mul]
    <;> abel

/-- Scalar `2×2` operator block. -/
def scalarOperatorBlock (q : EndW W) : OperatorMat2 W :=
  !![q, 0; 0, q]

/-- If all six independent coefficient commutators vanish, the left Weyl
curvature block collapses to the scalar quadratic channel. -/
theorem leftCurvatureBlock_eq_scalar_of_pairwise_commute
    (v : OperatorFourVector W)
    (h01 : opComm (v 0) (v 1) = 0)
    (h02 : opComm (v 0) (v 2) = 0)
    (h03 : opComm (v 0) (v 3) = 0)
    (h12 : opComm (v 1) (v 2) = 0)
    (h13 : opComm (v 1) (v 3) = 0)
    (h23 : opComm (v 2) (v 3) = 0) :
    leftCurvatureBlock v =
      scalarOperatorBlock (operatorMinkowskiQuadratic v) := by
  rw [leftCurvatureBlock_explicit]
  have h32 : opComm (v 3) (v 2) = 0 := by
    simp [opComm]
    exact sub_eq_zero.mpr (sub_eq_zero.mp h23).symm
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [scalarOperatorBlock, h01, h02, h03, h12, h13, h32]

/-- The same commuting limit collapses the right block to the identical scalar
quadratic channel. -/
theorem rightCurvatureBlock_eq_scalar_of_pairwise_commute
    (v : OperatorFourVector W)
    (h01 : opComm (v 0) (v 1) = 0)
    (h02 : opComm (v 0) (v 2) = 0)
    (h03 : opComm (v 0) (v 3) = 0)
    (h12 : opComm (v 1) (v 2) = 0)
    (h13 : opComm (v 1) (v 3) = 0)
    (h23 : opComm (v 2) (v 3) = 0) :
    rightCurvatureBlock v =
      scalarOperatorBlock (operatorMinkowskiQuadratic v) := by
  rw [rightCurvatureBlock_explicit]
  have h32 : opComm (v 3) (v 2) = 0 := by
    simp [opComm]
    exact sub_eq_zero.mpr (sub_eq_zero.mp h23).symm
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [scalarOperatorBlock, h01, h02, h03, h12, h13, h32]

/-- The operator-valued Weyl square separates cleanly into a common scalar
quadratic part and two order-sensitive commutator residues. -/
theorem chiral_curvature_residue_packet (v : OperatorFourVector W) :
    leftCurvatureBlock v =
      !![operatorMinkowskiQuadratic v - opComm (v 0) (v 3) -
            Complex.I • opComm (v 1) (v 2),
          -opComm (v 0) (v 1) + opComm (v 1) (v 3) +
            Complex.I • (opComm (v 0) (v 2) + opComm (v 3) (v 2));
         -opComm (v 0) (v 1) - opComm (v 1) (v 3) -
            Complex.I • opComm (v 0) (v 2) +
            Complex.I • opComm (v 3) (v 2),
          operatorMinkowskiQuadratic v + opComm (v 0) (v 3) +
            Complex.I • opComm (v 1) (v 2)] ∧
      rightCurvatureBlock v =
      !![operatorMinkowskiQuadratic v + opComm (v 0) (v 3) -
            Complex.I • opComm (v 1) (v 2),
          opComm (v 0) (v 1) + opComm (v 1) (v 3) -
            Complex.I • opComm (v 0) (v 2) +
            Complex.I • opComm (v 3) (v 2);
         opComm (v 0) (v 1) - opComm (v 1) (v 3) +
            Complex.I • opComm (v 0) (v 2) +
            Complex.I • opComm (v 3) (v 2),
          operatorMinkowskiQuadratic v - opComm (v 0) (v 3) +
            Complex.I • opComm (v 1) (v 2)] := by
  exact ⟨leftCurvatureBlock_explicit v, rightCurvatureBlock_explicit v⟩

end InfoGeometry.Canonical.OperatorWeylChiralCurvatureResidue
