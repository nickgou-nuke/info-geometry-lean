import Mathlib.Tactic

import InfoGeometry.Algebra.AssociativeRegularCommutant
import InfoGeometry.Clifford.Cl11Matrix
import InfoGeometry.Clifford.Cl11TensorTower
import InfoGeometry.Canonical.Cl11StageTwoMatrixEquivalence

/-!
# Doubled Cl(1,1) left/right regular and stage-two bridge

This module formalizes the finite algebraic core of the doubled
Cl(1,1)_L / Cl(1,1)_R architecture.

There are two complementary realizations.

1. On the regular module A = M₂(ℝ):
   * left multiplication L_A,
   * right multiplication R_B,
   * exact commutation L_A R_B = R_B L_A,
   * the full commutant of the left regular action is exactly the range of
     right multiplication.

2. On the native tensor tower at stage two:
   * left copy  A ↦ A ⊗ I₂,
   * right copy B ↦ I₂ ⊗ B,
   * the two copies commute,
   * the stage is already algebra-equivalent to M₄(ℝ).

This is a finite associative-algebra statement.  It does not assert a
Tomita--Takesaki standard form, a von Neumann-factor classification, a
Bisognano--Wichmann theorem, or a Type III₁ limit.
-/

noncomputable section

namespace InfoGeometry.Canonical.Cl11LeftRightDoubleBridge

open scoped Matrix Kronecker
open InfoGeometry.Algebra.AssociativeRegularCommutant
open InfoGeometry.Clifford.Cl11Matrix
open InfoGeometry.Clifford.Cl11TensorTower
open InfoGeometry.Canonical.Cl11StageTwoMatrixEquivalence

abbrev Atom := Mat2
abbrev AtomEnd := Module.End ℝ Atom
abbrev StageTwo := MatStage 2
abbrev M4R := InfoGeometry.Algebra.FiniteSpin.Mat4R

/-! ## 1. Regular A--A^op bimodule on M₂(ℝ) -/

/-- Left regular action on the Cl(1,1) matrix atom. -/
def leftAction (A : Atom) : AtomEnd :=
  leftRegular (R := ℝ) A

/-- Right regular action on the Cl(1,1) matrix atom. -/
def rightAction (B : Atom) : AtomEnd :=
  rightRegular (R := ℝ) B

@[simp] theorem leftAction_apply (A X : Atom) :
    leftAction A X = A * X := rfl

@[simp] theorem rightAction_apply (B X : Atom) :
    rightAction B X = X * B := rfl

/-- Left and right regular actions commute exactly. -/
theorem left_right_commute (A B : Atom) :
    (leftAction A).comp (rightAction B) =
      (rightAction B).comp (leftAction A) := by
  apply LinearMap.ext
  intro X
  simp [leftAction, rightAction, mul_assoc]

/-- Pointwise bimodule form of left/right commutation. -/
theorem left_right_commute_apply (A B X : Atom) :
    leftAction A (rightAction B X) =
      rightAction B (leftAction A X) := by
  simp [leftAction, rightAction, mul_assoc]

/-- The full commutant of the left regular action is exactly right
multiplication. -/
theorem left_commutant_eq_right_range :
    leftRegularCommutant (R := ℝ) (A := Atom) =
      {T | ∃ B : Atom, T = rightAction B} := by
  simpa [rightAction] using
    (leftRegularCommutant_eq_rightRegular_range (R := ℝ) (A := Atom))

/-- The right regular representation is faithful. -/
theorem rightAction_injective :
    Function.Injective rightAction := by
  simpa [rightAction] using
    (rightRegular_injective (R := ℝ) (A := Atom))

/-! ## 2. Native tensor realization in stage two -/

/-- Left Cl(1,1) copy in the native stage-two tensor carrier. -/
def leftStageTwo (A : Atom) : StageTwo :=
  A ⊗ₖ (1 : Atom)

/-- Right Cl(1,1) copy in the native stage-two tensor carrier. -/
def rightStageTwo (B : Atom) : StageTwo :=
  (1 : Atom) ⊗ₖ B

/-- The left copy is the existing one-step tower embedding. -/
theorem leftStageTwo_eq_stageEmbed (A : Atom) :
    leftStageTwo A = stageEmbed 1 A := by
  rfl

@[simp] theorem leftStageTwo_one :
    leftStageTwo (1 : Atom) = (1 : StageTwo) := by
  simp [leftStageTwo]

@[simp] theorem rightStageTwo_one :
    rightStageTwo (1 : Atom) = (1 : StageTwo) := by
  simp [rightStageTwo]

@[simp] theorem leftStageTwo_mul (A B : Atom) :
    leftStageTwo (A * B) = leftStageTwo A * leftStageTwo B := by
  simpa [leftStageTwo] using
    (Matrix.mul_kronecker_mul A B (1 : Atom) (1 : Atom)).symm

@[simp] theorem rightStageTwo_mul (A B : Atom) :
    rightStageTwo (A * B) = rightStageTwo A * rightStageTwo B := by
  simpa [rightStageTwo] using
    (Matrix.mul_kronecker_mul (1 : Atom) (1 : Atom) A B).symm

/-- The two stage-two Clifford copies commute exactly. -/
theorem leftStageTwo_rightStageTwo_commute (A B : Atom) :
    leftStageTwo A * rightStageTwo B =
      rightStageTwo B * leftStageTwo A := by
  calc
    leftStageTwo A * rightStageTwo B
        = (A * 1) ⊗ₖ ((1 : Atom) * B) := by
            simpa [leftStageTwo, rightStageTwo] using
              (Matrix.mul_kronecker_mul A (1 : Atom) (1 : Atom) B).symm
    _ = A ⊗ₖ B := by simp
    _ = ((1 : Atom) * A) ⊗ₖ (B * 1) := by simp
    _ = rightStageTwo B * leftStageTwo A := by
            simpa [leftStageTwo, rightStageTwo] using
              (Matrix.mul_kronecker_mul (1 : Atom) A B (1 : Atom))

/-- The common product of the commuting left/right copies is the Kronecker
tensor A ⊗ B. -/
theorem leftStageTwo_mul_rightStageTwo (A B : Atom) :
    leftStageTwo A * rightStageTwo B = A ⊗ₖ B := by
  calc
    leftStageTwo A * rightStageTwo B
        = (A * 1) ⊗ₖ ((1 : Atom) * B) := by
            simpa [leftStageTwo, rightStageTwo] using
              (Matrix.mul_kronecker_mul A (1 : Atom) (1 : Atom) B).symm
    _ = A ⊗ₖ B := by simp

/-- Stage two is the repository-native 4×4 real matrix algebra. -/
def doubledStageToM4R : StageTwo ≃ₐ[ℝ] M4R :=
  stageTwoToM4R

/-- Readout of a doubled elementary tensor in the native M₄(ℝ) carrier. -/
def doubledTensorM4 (A B : Atom) : M4R :=
  doubledStageToM4R (leftStageTwo A * rightStageTwo B)

theorem doubledTensorM4_eq_stage_readout (A B : Atom) :
    doubledTensorM4 A B =
      doubledStageToM4R (A ⊗ₖ B) := by
  rw [doubledTensorM4, leftStageTwo_mul_rightStageTwo]

/-- Commutation survives transport to the M₄(ℝ) readout. -/
theorem doubledM4_left_right_commute (A B : Atom) :
    doubledStageToM4R (leftStageTwo A) *
        doubledStageToM4R (rightStageTwo B) =
      doubledStageToM4R (rightStageTwo B) *
        doubledStageToM4R (leftStageTwo A) := by
  rw [← map_mul, ← map_mul, leftStageTwo_rightStageTwo_commute]

/-! ## 3. Connection to the abstract Cl(1,1) algebra -/

abbrev Cl11 := CliffordAlgebra q11

/-- Left abstract Cl(1,1) element represented in the stage-two left factor. -/
def cl11LeftStageTwo (x : Cl11) : StageTwo :=
  leftStageTwo (cl11EquivMat x)

/-- Right abstract Cl(1,1) element represented in the stage-two right factor. -/
def cl11RightStageTwo (y : Cl11) : StageTwo :=
  rightStageTwo (cl11EquivMat y)

/-- The abstract left and right Cl(1,1) copies commute in the doubled stage. -/
theorem cl11LeftRight_commute (x y : Cl11) :
    cl11LeftStageTwo x * cl11RightStageTwo y =
      cl11RightStageTwo y * cl11LeftStageTwo x := by
  exact leftStageTwo_rightStageTwo_commute (cl11EquivMat x) (cl11EquivMat y)

end InfoGeometry.Canonical.Cl11LeftRightDoubleBridge
