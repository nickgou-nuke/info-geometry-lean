import InfoGeometry.Canonical.HestenesCircularCARTransport
import InfoGeometry.Algebra.FiniteSpinAlgebra

/-! # Finite standard-form Tomita bridge for the Hestenes algebra

The Hilbert--Schmidt carrier of `M₂(ℂ)` is represented by the matrix algebra
itself.  Conjugate transpose exchanges its left and right regular actions.
Pullback through `Cl⁺(1,3) ≃ₐ[ℝ] M₂(ℂ)` gives the corresponding finite
Tomita conjugation on the native even Clifford carrier.

No analytic von Neumann completion or unbounded modular theorem is claimed.
-/

noncomputable section
namespace FiniteHestenesTomitaBridge

open HestenesCl14
open HestenesEvenPauliEquiv
open HestenesKreinMatrixBridge
open HestenesPauliSheetBridge

abbrev HS2 := HestenesPauliSheetBridge.Sheet

def matrixTomita (X : HS2) : HS2 := Matrix.conjTranspose X
def matrixLeftAction (A X : HS2) : HS2 := A * X
def matrixRightAction (X A : HS2) : HS2 := X * A

@[simp] theorem matrixTomita_involutive (X : HS2) :
    matrixTomita (matrixTomita X) = X := by
  simp [matrixTomita]

@[simp] theorem matrixTomita_add (X Y : HS2) :
    matrixTomita (X + Y) = matrixTomita X + matrixTomita Y := by
  simp [matrixTomita, Matrix.conjTranspose_add]

theorem matrixTomita_antimultiplicative (A B : HS2) :
    matrixTomita (A * B) = matrixTomita B * matrixTomita A := by
  simp [matrixTomita, Matrix.conjTranspose_mul]

theorem matrix_left_right_commute (A B X : HS2) :
    matrixLeftAction A (matrixRightAction X B) =
      matrixRightAction (matrixLeftAction A X) B := by
  simp [matrixLeftAction, matrixRightAction, Matrix.mul_assoc]

/-- Finite standard-form algebra/commutant exchange. -/
theorem matrixTomita_left_to_right (A X : HS2) :
    matrixTomita (matrixLeftAction A (matrixTomita X)) =
      matrixRightAction X (matrixTomita A) := by
  simp [matrixTomita, matrixLeftAction, matrixRightAction,
    Matrix.conjTranspose_mul]

/-- Pullback of Hilbert--Schmidt adjunction to the native even Clifford
algebra.  It is an additive real-linear involutive anti-automorphism. -/
def cliffordTomita (x : ClPlus14) : ClPlus14 :=
  clPlusPauliAlgEquiv.symm (matrixTomita (clPlusPauliAlgEquiv x))

def cliffordLeftAction (a x : ClPlus14) : ClPlus14 := a * x
def cliffordRightAction (x a : ClPlus14) : ClPlus14 := x * a

@[simp] theorem map_cliffordTomita (x : ClPlus14) :
    clPlusPauliAlgEquiv (cliffordTomita x) =
      matrixTomita (clPlusPauliAlgEquiv x) := by
  simp [cliffordTomita]

@[simp] theorem cliffordTomita_involutive (x : ClPlus14) :
    cliffordTomita (cliffordTomita x) = x := by
  apply clPlusPauliAlgEquiv.injective
  simp

@[simp] theorem cliffordTomita_add (x y : ClPlus14) :
    cliffordTomita (x + y) = cliffordTomita x + cliffordTomita y := by
  apply clPlusPauliAlgEquiv.injective
  simp

@[simp] theorem cliffordTomita_real_smul (r : ℝ) (x : ClPlus14) :
    cliffordTomita (r • x) = r • cliffordTomita x := by
  apply clPlusPauliAlgEquiv.injective
  rw [map_cliffordTomita, map_smul, map_smul, map_cliffordTomita]
  change Matrix.conjTranspose ((r : ℂ) • clPlusPauliAlgEquiv x) =
    (r : ℂ) • Matrix.conjTranspose (clPlusPauliAlgEquiv x)
  rw [Matrix.conjTranspose_smul]
  simp

@[simp] theorem cliffordTomita_mul (x y : ClPlus14) :
    cliffordTomita (x * y) = cliffordTomita y * cliffordTomita x := by
  apply clPlusPauliAlgEquiv.injective
  simp [matrixTomita_antimultiplicative]

theorem clifford_left_right_commute (a b x : ClPlus14) :
    cliffordLeftAction a (cliffordRightAction x b) =
      cliffordRightAction (cliffordLeftAction a x) b := by
  simp [cliffordLeftAction, cliffordRightAction, mul_assoc]

/-- Native Clifford form of `J L_a J = R_{J a}`. -/
theorem cliffordTomita_left_to_right (a x : ClPlus14) :
    cliffordTomita (cliffordLeftAction a (cliffordTomita x)) =
      cliffordRightAction x (cliffordTomita a) := by
  simp [cliffordLeftAction, cliffordRightAction]

theorem pauli1_selfAdjoint : Matrix.conjTranspose pauli1 = pauli1 := by
  ext i j <;> fin_cases i <;> fin_cases j <;>
    simp [pauli1, Matrix.conjTranspose_apply]

@[simp] theorem cliffordTomita_beta :
    cliffordTomita (sigmaEven 0) = sigmaEven 0 := by
  apply clPlusPauliAlgEquiv.injective
  rw [map_cliffordTomita]
  change matrixTomita (clPlusToPauli (sigmaEven 0)) =
    clPlusToPauli (sigmaEven 0)
  rw [clPlusToPauli_sigma0]
  exact pauli1_selfAdjoint

/-- Tomita adjunction and the intrinsic reverse/Krein operation are distinct
native Clifford involutions under the current conventions. -/
theorem cliffordTomita_ne_reverseKreinEven :
    cliffordTomita ≠ reverseKreinEven := by
  intro h
  have hb := congrFun h (sigmaEven 0)
  rw [cliffordTomita_beta, reverseKreinEven_beta] at hb
  have hm := congrArg clPlusToPauli hb
  rw [clPlusToPauli_sigma0, map_neg, clPlusToPauli_sigma0] at hm
  have hm01 := congrFun (congrFun hm 0) 1
  norm_num [pauli1] at hm01

theorem finite_hestenes_tomita_packet :
    (∀ X : HS2, matrixTomita (matrixTomita X) = X) ∧
      (∀ A X : HS2,
        matrixTomita (matrixLeftAction A (matrixTomita X)) =
          matrixRightAction X (matrixTomita A)) ∧
      (∀ x : ClPlus14, cliffordTomita (cliffordTomita x) = x) ∧
      (∀ a x : ClPlus14,
        cliffordTomita (cliffordLeftAction a (cliffordTomita x)) =
          cliffordRightAction x (cliffordTomita a)) := by
  exact ⟨matrixTomita_involutive, matrixTomita_left_to_right,
    cliffordTomita_involutive, cliffordTomita_left_to_right⟩

end FiniteHestenesTomitaBridge
end noncomputable section
