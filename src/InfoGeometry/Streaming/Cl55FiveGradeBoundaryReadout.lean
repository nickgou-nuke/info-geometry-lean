import InfoGeometry.Canonical.Cl11ComplexStageBridge
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Canonical.Cl55WittCAR
import InfoGeometry.Canonical.Cl55WittLieRouting
import InfoGeometry.Canonical.Cl55WittMultigrading
import InfoGeometry.Canonical.Cl55WittFullLieClosure
import InfoGeometry.Streaming.FiniteTwoBoundaryWeakFunctional

/-!
# Complexified stage-five action

This is the carrier bridge for the stage-five Witt--CAR construction.  It
keeps the source matrix algebra, its complexification, and the boundary
functional separate; no topology or physical transport is inferred.
-/

noncomputable section
set_option autoImplicit false

namespace InfoGeometry.Streaming.Cl55FiveGradeBoundaryReadout

open InfoGeometry.Canonical.Cl55WittMultigrading

open InfoGeometry.Clifford.Cl11TensorTower
open InfoGeometry.Clifford.TowerMatrix
open InfoGeometry.Canonical.Cl11ComplexStageBridge
open InfoGeometry.Canonical.Cl55WittCAR
open InfoGeometry.Canonical.Cl55WittLieRouting
open InfoGeometry.Streaming.FiniteTwoBoundaryWeakFunctional

abbrev Cl55ComplexSpinor := Idx 5 → ℂ
abbrev Cl55ComplexEnd := Module.End ℂ Cl55ComplexSpinor

def complexSpinAction (X : MatStage 5) : Cl55ComplexEnd :=
  Matrix.toLin' (complexifyStage 5 X)

@[simp] theorem complexSpinAction_add (X Y : MatStage 5) :
    complexSpinAction (X + Y) = complexSpinAction X + complexSpinAction Y := by
  unfold complexSpinAction
  rw [complexifyStage_add]
  exact map_add (Matrix.toLinAlgEquiv' (R := ℂ) (n := Idx 5)) _ _

@[simp] theorem complexSpinAction_mul (X Y : MatStage 5) :
    complexSpinAction (X * Y) = complexSpinAction X * complexSpinAction Y := by
  unfold complexSpinAction
  rw [complexifyStage_mul, Matrix.toLin'_mul]
  rfl

@[simp] theorem complexSpinAction_neg (X : MatStage 5) :
    complexSpinAction (-X) = -complexSpinAction X := by
  unfold complexSpinAction
  rw [map_neg]
  exact map_neg (Matrix.toLinAlgEquiv' (R := ℂ) (n := Idx 5)) _

@[simp] theorem complexSpinAction_sub (X Y : MatStage 5) :
    complexSpinAction (X - Y) = complexSpinAction X - complexSpinAction Y := by
  rw [sub_eq_add_neg, complexSpinAction_add, complexSpinAction_neg]
  rfl

theorem complexifyStage_real_smul (c : ℝ) (X : MatStage 5) :
    complexifyStage 5 (c • X) = (c : ℂ) • complexifyStage 5 X := by
  ext i j
  simp [complexifyStage_apply]

theorem complexSpinAction_real_smul (c : ℝ) (X : MatStage 5) :
    complexSpinAction (c • X) = (c : ℂ) • complexSpinAction X := by
  unfold complexSpinAction
  rw [complexifyStage_real_smul]
  ext v i
  simp only [LinearMap.comp_apply, Matrix.toLin'_apply, LinearMap.smul_apply]
  simp [Matrix.smul_mulVec, Complex.ofReal_mul]

theorem complexSpinAction_bracket (X Y : MatStage 5) :
    complexSpinAction (bracket X Y) =
      complexSpinAction X * complexSpinAction Y -
        complexSpinAction Y * complexSpinAction X := by
  unfold bracket
  rw [sub_eq_add_neg, complexSpinAction_add, complexSpinAction_neg,
    complexSpinAction_mul, complexSpinAction_mul, sub_eq_add_neg]

theorem complexSpinAction_injective :
    Function.Injective complexSpinAction := by
  intro X Y hXY
  have hmat : complexifyStage 5 X = complexifyStage 5 Y :=
    (Matrix.toLinAlgEquiv' (R := ℂ) (n := Idx 5)).injective hXY
  ext i j
  have hij := congrArg (fun M : ComplexMatStage 5 => M i j) hmat
  apply Complex.ofReal_injective
  simpa [complexifyStage_apply] using hij

abbrev Cl55BoundaryPair :=
  InfoGeometry.Streaming.FiniteTwoBoundaryWeakFunctional.RegularBoundaryPair (Idx 5)

def cl55BoundaryReadout (p : Cl55BoundaryPair) (X : MatStage 5) : ℂ :=
  InfoGeometry.Streaming.FiniteTwoBoundaryWeakFunctional.weakValue p
    (complexSpinAction X)

@[simp] theorem cl55BoundaryReadout_zero (p : Cl55BoundaryPair) :
    cl55BoundaryReadout p 0 = 0 := by
  unfold cl55BoundaryReadout
  rw [show complexSpinAction (0 : MatStage 5) = 0 by
    unfold complexSpinAction complexifyStage
    ext v i
    simp]
  simp

@[simp] theorem cl55BoundaryReadout_one (p : Cl55BoundaryPair) :
    cl55BoundaryReadout p 1 = 1 := by
  unfold cl55BoundaryReadout
  rw [show complexSpinAction (1 : MatStage 5) = 1 by
    unfold complexSpinAction complexifyStage
    ext v i
    simp]
  simp

theorem cl55BoundaryReadout_add (p : Cl55BoundaryPair) (X Y : MatStage 5) :
    cl55BoundaryReadout p (X + Y) =
      cl55BoundaryReadout p X + cl55BoundaryReadout p Y := by
  simp [cl55BoundaryReadout, complexSpinAction_add,
    InfoGeometry.Streaming.FiniteTwoBoundaryWeakFunctional.weakValue_add]

theorem cl55BoundaryReadout_sub (p : Cl55BoundaryPair) (X Y : MatStage 5) :
    cl55BoundaryReadout p (X - Y) =
      cl55BoundaryReadout p X - cl55BoundaryReadout p Y := by
  simp [cl55BoundaryReadout, complexSpinAction_sub,
    InfoGeometry.Streaming.FiniteTwoBoundaryWeakFunctional.weakValue_sub]

@[simp] theorem cl55BoundaryReadout_neg (p : Cl55BoundaryPair) (X : MatStage 5) :
    cl55BoundaryReadout p (-X) = -cl55BoundaryReadout p X := by
  unfold cl55BoundaryReadout
  rw [complexSpinAction_neg]
  have h := FiniteTwoBoundaryWeakFunctional.weakValue_smul p (-1 : ℂ)
    (complexSpinAction X)
  calc
    FiniteTwoBoundaryWeakFunctional.weakValue p (-complexSpinAction X) =
        FiniteTwoBoundaryWeakFunctional.weakValue p
          ((-1 : ℂ) • complexSpinAction X) := by
      congr 1
      exact (neg_one_smul ℂ (complexSpinAction X)).symm
    _ = -FiniteTwoBoundaryWeakFunctional.weakValue p (complexSpinAction X) := by
      simpa only [neg_one_mul] using h

def cl55BoundaryReadoutAddHom (p : Cl55BoundaryPair) :
    MatStage 5 →+ ℂ where
  toFun := cl55BoundaryReadout p
  map_zero' := cl55BoundaryReadout_zero p
  map_add' := cl55BoundaryReadout_add p

@[simp] theorem cl55BoundaryReadoutAddHom_apply
    (p : Cl55BoundaryPair) (X : MatStage 5) :
    cl55BoundaryReadoutAddHom p X = cl55BoundaryReadout p X := rfl

def fullFiveGradeBoundaryReadoutAddHom (p : Cl55BoundaryPair) :
    InfoGeometry.Canonical.Cl55WittFullLieClosure.wittFiveGradeLieSubalgebra →+ ℂ :=
  (cl55BoundaryReadoutAddHom p).comp
    (InfoGeometry.Canonical.Cl55WittFullLieClosure.wittFiveGradeLieSubalgebra.subtype).toAddMonoidHom

@[simp] theorem fullFiveGradeBoundaryReadoutAddHom_apply
    (p : Cl55BoundaryPair)
    (X : InfoGeometry.Canonical.Cl55WittFullLieClosure.wittFiveGradeLieSubalgebra) :
    fullFiveGradeBoundaryReadoutAddHom p X = cl55BoundaryReadout p X.1 := rfl

theorem cl55BoundaryReadout_rescalePre (p : Cl55BoundaryPair)
    (c : ℂ) (hc : c ≠ 0) (X : MatStage 5) :
    cl55BoundaryReadout (FiniteTwoBoundaryWeakFunctional.rescalePre p c hc) X =
      cl55BoundaryReadout p X := by
  exact FiniteTwoBoundaryWeakFunctional.weakValue_rescalePre p c hc
    (complexSpinAction X)

theorem cl55BoundaryReadout_rescalePost (p : Cl55BoundaryPair)
    (c : ℂ) (hc : c ≠ 0) (X : MatStage 5) :
    cl55BoundaryReadout (FiniteTwoBoundaryWeakFunctional.rescalePost p c hc) X =
      cl55BoundaryReadout p X := by
  exact FiniteTwoBoundaryWeakFunctional.weakValue_rescalePost p c hc
    (complexSpinAction X)

theorem cl55BoundaryReadout_bracket (p : Cl55BoundaryPair)
    (X Y : MatStage 5) :
    cl55BoundaryReadout p (bracket X Y) =
      InfoGeometry.Streaming.FiniteTwoBoundaryWeakFunctional.weakValue p
        (complexSpinAction X * complexSpinAction Y -
          complexSpinAction Y * complexSpinAction X) := by
  unfold cl55BoundaryReadout
  rw [complexSpinAction_bracket]

end InfoGeometry.Streaming.Cl55FiveGradeBoundaryReadout
