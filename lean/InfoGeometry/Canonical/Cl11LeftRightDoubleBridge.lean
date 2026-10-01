import Mathlib.Tactic

import InfoGeometry.Algebra.AssociativeRegularCommutant
import InfoGeometry.Clifford.Cl11Matrix
import InfoGeometry.Clifford.Cl11TensorTower
import InfoGeometry.Canonical.Cl11StageTwoMatrixEquivalence

/-!
# Doubled Cl(1,1) left/right regular and stage-two bridge

This module formalizes the finite algebraic core of the doubled
Cl(1,1)_L / Cl(1,1)_R architecture.

The repository's stage-one tensor carrier is indexed by
`Idx 1 = Fin 1 × Fin 2`, so it is algebra-equivalent rather than
definitionally equal to `M₂(ℝ)`.  The bridge makes that equivalence explicit
before forming the native stage-two tensor product.
-/

noncomputable section

namespace InfoGeometry.Canonical.Cl11LeftRightDoubleBridge

open scoped Matrix Kronecker
open InfoGeometry.Algebra.AssociativeRegularCommutant
open InfoGeometry.Clifford.Cl11Matrix
open InfoGeometry.Clifford.Cl11TensorTower
open InfoGeometry.Clifford.TowerMatrix
open InfoGeometry.Canonical.Cl11StageTwoMatrixEquivalence

abbrev Atom := Mat2
abbrev AtomEnd := Module.End ℝ Atom
abbrev StageOne := MatStage 1
abbrev StageTwo := MatStage 2
abbrev M4R := InfoGeometry.Algebra.FiniteSpin.Mat4R

/-! ## 1. Regular A--A^op bimodule on M₂(ℝ) -/

def leftAction (A : Atom) : AtomEnd :=
  leftRegular (R := ℝ) A

def rightAction (B : Atom) : AtomEnd :=
  rightRegular (R := ℝ) B

@[simp] theorem leftAction_apply (A X : Atom) :
    leftAction A X = A * X := rfl

@[simp] theorem rightAction_apply (B X : Atom) :
    rightAction B X = X * B := rfl

theorem left_right_commute (A B : Atom) :
    (leftAction A).comp (rightAction B) =
      (rightAction B).comp (leftAction A) := by
  apply LinearMap.ext
  intro X
  simp [leftAction, rightAction, mul_assoc]

theorem left_right_commute_apply (A B X : Atom) :
    leftAction A (rightAction B X) =
      rightAction B (leftAction A X) := by
  simp [leftAction, rightAction, mul_assoc]

theorem left_commutant_eq_right_range :
    leftRegularCommutant (R := ℝ) (A := Atom) =
      {T | ∃ B : Atom, T = rightAction B} := by
  simpa [rightAction] using
    (leftRegularCommutant_eq_rightRegular_range (R := ℝ) (A := Atom))

theorem rightAction_injective :
    Function.Injective rightAction := by
  simpa [rightAction] using
    (rightRegular_injective (R := ℝ) (A := Atom))

/-! ## 2. Explicit stage-one equivalence and native tensor realization -/

/-- Concrete identification `Idx 1 = Fin 1 × Fin 2 ≃ Fin 2`. -/
def stageOneIndexEquiv : InfoGeometry.Clifford.TowerMatrix.Idx 1 ≃ Fin 2 where
  toFun x := x.2
  invFun i := (0, i)
  left_inv x := by
    rcases x with ⟨u, i⟩
    have hu : u = (0 : Fin 1) := Subsingleton.elim _ _
    subst u
    rfl
  right_inv i := rfl

/-- Concrete algebra equivalence between the repository stage-one carrier and
the executable Cl(1,1) matrix atom. -/
noncomputable def stageOneToAtom : StageOne ≃ₐ[ℝ] Atom :=
  Matrix.reindexAlgEquiv ℝ ℝ stageOneIndexEquiv

noncomputable def atomToStageOne : Atom ≃ₐ[ℝ] StageOne :=
  stageOneToAtom.symm

@[simp] theorem stageOneToAtom_atomToStageOne (A : Atom) :
    stageOneToAtom (atomToStageOne A) = A :=
  stageOneToAtom.apply_symm_apply A

@[simp] theorem atomToStageOne_stageOneToAtom (A : StageOne) :
    atomToStageOne (stageOneToAtom A) = A :=
  stageOneToAtom.symm_apply_apply A

/-- Left Cl(1,1) copy in the native stage-two tensor carrier. -/
def leftStageTwo (A : Atom) : StageTwo :=
  atomToStageOne A ⊗ₖ (1 : Atom)

/-- Right Cl(1,1) copy in the native stage-two tensor carrier. -/
def rightStageTwo (B : Atom) : StageTwo :=
  (1 : StageOne) ⊗ₖ B

@[simp] theorem leftStageTwo_one :
    leftStageTwo (1 : Atom) = (1 : StageTwo) := by
  simp [leftStageTwo, atomToStageOne, Matrix.one_kronecker_one]

@[simp] theorem rightStageTwo_one :
    rightStageTwo (1 : Atom) = (1 : StageTwo) := by
  simp [rightStageTwo, Matrix.one_kronecker_one]

@[simp] theorem leftStageTwo_mul (A B : Atom) :
    leftStageTwo (A * B) = leftStageTwo A * leftStageTwo B := by
  simp [leftStageTwo, ← Matrix.mul_kronecker_mul]

@[simp] theorem rightStageTwo_mul (A B : Atom) :
    rightStageTwo (A * B) = rightStageTwo A * rightStageTwo B := by
  simp [rightStageTwo, ← Matrix.mul_kronecker_mul]

theorem leftStageTwo_rightStageTwo_commute (A B : Atom) :
    leftStageTwo A * rightStageTwo B =
      rightStageTwo B * leftStageTwo A := by
  calc
    leftStageTwo A * rightStageTwo B
        = (atomToStageOne A * 1) ⊗ₖ ((1 : Atom) * B) := by
            simpa [leftStageTwo, rightStageTwo] using
              (Matrix.mul_kronecker_mul
                (atomToStageOne A) (1 : StageOne) (1 : Atom) B).symm
    _ = atomToStageOne A ⊗ₖ B := by simp
    _ = ((1 : StageOne) * atomToStageOne A) ⊗ₖ (B * 1) := by simp
    _ = rightStageTwo B * leftStageTwo A := by
            simpa [leftStageTwo, rightStageTwo] using
              (Matrix.mul_kronecker_mul
                (1 : StageOne) (atomToStageOne A) B (1 : Atom))

theorem leftStageTwo_mul_rightStageTwo (A B : Atom) :
    leftStageTwo A * rightStageTwo B =
      atomToStageOne A ⊗ₖ B := by
  calc
    leftStageTwo A * rightStageTwo B
        = (atomToStageOne A * 1) ⊗ₖ ((1 : Atom) * B) := by
            simpa [leftStageTwo, rightStageTwo] using
              (Matrix.mul_kronecker_mul
                (atomToStageOne A) (1 : StageOne) (1 : Atom) B).symm
    _ = atomToStageOne A ⊗ₖ B := by simp

def doubledStageToM4R : StageTwo ≃ₐ[ℝ] M4R :=
  stageTwoToM4R

def doubledTensorM4 (A B : Atom) : M4R :=
  doubledStageToM4R (leftStageTwo A * rightStageTwo B)

theorem doubledTensorM4_eq_stage_readout (A B : Atom) :
    doubledTensorM4 A B =
      doubledStageToM4R (atomToStageOne A ⊗ₖ B) := by
  rw [doubledTensorM4, leftStageTwo_mul_rightStageTwo]

theorem doubledM4_left_right_commute (A B : Atom) :
    doubledStageToM4R (leftStageTwo A) *
        doubledStageToM4R (rightStageTwo B) =
      doubledStageToM4R (rightStageTwo B) *
        doubledStageToM4R (leftStageTwo A) := by
  rw [← map_mul, ← map_mul, leftStageTwo_rightStageTwo_commute]

/-! ## 3. Connection to the abstract Cl(1,1) algebra -/

abbrev Cl11 := CliffordAlgebra q11

def cl11LeftStageTwo (x : Cl11) : StageTwo :=
  leftStageTwo (cl11EquivMat x)

def cl11RightStageTwo (y : Cl11) : StageTwo :=
  rightStageTwo (cl11EquivMat y)

theorem cl11LeftRight_commute (x y : Cl11) :
    cl11LeftStageTwo x * cl11RightStageTwo y =
      cl11RightStageTwo y * cl11LeftStageTwo x := by
  exact leftStageTwo_rightStageTwo_commute (cl11EquivMat x) (cl11EquivMat y)

end InfoGeometry.Canonical.Cl11LeftRightDoubleBridge
