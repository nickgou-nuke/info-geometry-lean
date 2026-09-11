import InfoGeometry.Exceptional.CompositionTriality
import InfoGeometry.Algebra.FiniteSpinAlgebra

/-!
# Triality actions on a tensor channel

This owner records only the factorwise action supplied by the two triality
carriers.  It does not define the Barton--Sudbery cross-channel bracket.
-/

namespace InfoGeometry.Exceptional.BartonSudberyTrialityAction

open InfoGeometry.Exceptional.CompositionTriality
open InfoGeometry.Exceptional.CompositionTriality.TrialityTriple

variable {R A B : Type*} [CommRing R]
variable [AddCommGroup A] [Module R A]
variable [AddCommGroup B] [Module R B]
variable {mulA : A →ₗ[R] A →ₗ[R] A}
variable {mulB : B →ₗ[R] B →ₗ[R] B}

open scoped TensorProduct

def leftTensorAction (D : Module.End R A) :
    Module.End R (A ⊗[R] B) :=
  TensorProduct.map D (LinearMap.id : B →ₗ[R] B)

def rightTensorAction (E : Module.End R B) :
    Module.End R (A ⊗[R] B) :=
  TensorProduct.map (LinearMap.id : A →ₗ[R] A) E

theorem leftTensorAction_comp (S T : Module.End R A) :
    leftTensorAction (A := A) (B := B) (S * T) =
      leftTensorAction (A := A) (B := B) S *
        leftTensorAction (A := A) (B := B) T := by
  ext x
  simp [leftTensorAction]

theorem rightTensorAction_comp (S T : Module.End R B) :
    rightTensorAction (A := A) (B := B) (S * T) =
      rightTensorAction (A := A) (B := B) S *
        rightTensorAction (A := A) (B := B) T := by
  ext x
  simp [rightTensorAction]

theorem leftTensorAction_commutator
    (S T : Module.End R A) :
    leftTensorAction (A := A) (B := B) (endCommutator S T) =
      endCommutator (leftTensorAction (A := A) (B := B) S)
        (leftTensorAction (A := A) (B := B) T) := by
  ext x
  simp [endCommutator, leftTensorAction, TensorProduct.sub_tmul]

theorem rightTensorAction_commutator
    (S T : Module.End R B) :
    rightTensorAction (A := A) (B := B) (endCommutator S T) =
      endCommutator (rightTensorAction (A := A) (B := B) S)
        (rightTensorAction (A := A) (B := B) T) := by
  ext x
  simp [endCommutator, rightTensorAction, TensorProduct.tmul_sub]

theorem left_right_tensorAction_commute
    (S : Module.End R A) (T : Module.End R B) :
    leftTensorAction (A := A) (B := B) S *
        rightTensorAction (A := A) (B := B) T =
      rightTensorAction (A := A) (B := B) T *
        leftTensorAction (A := A) (B := B) S := by
  ext x
  simp [leftTensorAction, rightTensorAction]

def leftTrialityAction₁
    (T : TrialityTriple mulA) : Module.End R (A ⊗[R] B) :=
  leftTensorAction T.t₁

def leftTrialityAction₂
    (T : TrialityTriple mulA) : Module.End R (A ⊗[R] B) :=
  leftTensorAction T.t₂

def leftTrialityAction₃
    (T : TrialityTriple mulA) : Module.End R (A ⊗[R] B) :=
  leftTensorAction T.t₃

def rightTrialityAction₁
    (T : TrialityTriple mulB) : Module.End R (A ⊗[R] B) :=
  rightTensorAction T.t₁

def rightTrialityAction₂
    (T : TrialityTriple mulB) : Module.End R (A ⊗[R] B) :=
  rightTensorAction T.t₂

def rightTrialityAction₃
    (T : TrialityTriple mulB) : Module.End R (A ⊗[R] B) :=
  rightTensorAction T.t₃

theorem leftTrialityAction₁_commutator
    (T U : TrialityTriple mulA) :
    leftTrialityAction₁ (A := A) (B := B) (commutator T U) =
      endCommutator (leftTrialityAction₁ (A := A) (B := B) T)
        (leftTrialityAction₁ (A := A) (B := B) U) := by
  exact leftTensorAction_commutator T.t₁ U.t₁

theorem leftTrialityAction₂_commutator
    (T U : TrialityTriple mulA) :
    leftTrialityAction₂ (A := A) (B := B) (commutator T U) =
      endCommutator (leftTrialityAction₂ (A := A) (B := B) T)
        (leftTrialityAction₂ (A := A) (B := B) U) := by
  exact leftTensorAction_commutator T.t₂ U.t₂

theorem leftTrialityAction₃_commutator
    (T U : TrialityTriple mulA) :
    leftTrialityAction₃ (A := A) (B := B) (commutator T U) =
      endCommutator (leftTrialityAction₃ (A := A) (B := B) T)
        (leftTrialityAction₃ (A := A) (B := B) U) := by
  exact leftTensorAction_commutator T.t₃ U.t₃

theorem rightTrialityAction₁_commutator
    (T U : TrialityTriple mulB) :
    rightTrialityAction₁ (A := A) (B := B) (commutator T U) =
      endCommutator (rightTrialityAction₁ (A := A) (B := B) T)
        (rightTrialityAction₁ (A := A) (B := B) U) := by
  exact rightTensorAction_commutator T.t₁ U.t₁

theorem rightTrialityAction₂_commutator
    (T U : TrialityTriple mulB) :
    rightTrialityAction₂ (A := A) (B := B) (commutator T U) =
      endCommutator (rightTrialityAction₂ (A := A) (B := B) T)
        (rightTrialityAction₂ (A := A) (B := B) U) := by
  exact rightTensorAction_commutator T.t₂ U.t₂

theorem rightTrialityAction₃_commutator
    (T U : TrialityTriple mulB) :
    rightTrialityAction₃ (A := A) (B := B) (commutator T U) =
      endCommutator (rightTrialityAction₃ (A := A) (B := B) T)
        (rightTrialityAction₃ (A := A) (B := B) U) := by
  exact rightTensorAction_commutator T.t₃ U.t₃

end InfoGeometry.Exceptional.BartonSudberyTrialityAction
