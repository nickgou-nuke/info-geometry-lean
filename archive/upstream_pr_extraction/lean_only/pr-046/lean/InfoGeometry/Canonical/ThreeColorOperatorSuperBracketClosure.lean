import InfoGeometry.Canonical.ThreeColorOperatorCrossCommutator
import InfoGeometry.Canonical.ChiralConeOperatorAlgebra

/-!
# Superbracket closure of the three-colour chiral operators

The ambient operator-valued Zorn multiplication is nonassociative, so this
owner does not install a Lie superalgebra instance on it.  It proves the
explicit symmetric odd-bracket readouts:

* same-chirality odd brackets land in the opposite chiral sector via the
  symmetric cross defect;
* mixed odd brackets land in the diagonal sector.

The `Z₃` grading is handled by a separate owner.
-/

namespace InfoGeometry.Canonical

variable {A : Type*} [Ring A]

def operatorAdd (X Y : OperatorZornMatrix A) : OperatorZornMatrix A :=
  ⟨X.n_plus + Y.n_plus, X.n_minus + Y.n_minus,
    fun i => X.sigma_plus i + Y.sigma_plus i,
    fun i => X.sigma_minus i + Y.sigma_minus i⟩

def oddOddSuperBracket
    (X Y : OperatorZornMatrix A) : OperatorZornMatrix A :=
  operatorAdd (operatorZornMul X Y) (operatorZornMul Y X)

@[simp] theorem sigmaPlus_superBracket_sigmaPlus
    (U V : OperatorVector A) :
    oddOddSuperBracket (sigmaPlus U) (sigmaPlus V) =
      sigmaMinus (operatorCross U V + operatorCross V U) := by
  rw [oddOddSuperBracket, sigmaPlus_mul_sigmaPlus, sigmaPlus_mul_sigmaPlus]
  apply operatorZornMatrix_ext
  · simp [operatorAdd, sigmaMinus]
  · simp [operatorAdd, sigmaMinus]
  · simp [operatorAdd, sigmaMinus]
  · funext i
    simp [operatorAdd, sigmaMinus]

@[simp] theorem sigmaMinus_superBracket_sigmaMinus
    (U V : OperatorVector A) :
    oddOddSuperBracket (sigmaMinus U) (sigmaMinus V) =
      sigmaPlus (-(operatorCross U V + operatorCross V U)) := by
  rw [oddOddSuperBracket, sigmaMinus_mul_sigmaMinus, sigmaMinus_mul_sigmaMinus]
  apply operatorZornMatrix_ext
  · simp [operatorAdd, sigmaPlus]
  · simp [operatorAdd, sigmaPlus]
  · funext i
    simp [operatorAdd, sigmaPlus, add_comm]
  · simp [operatorAdd, sigmaPlus]

theorem sigmaPlus_superBracket_sigmaMinus
    (U V : OperatorVector A) :
    oddOddSuperBracket (sigmaPlus U) (sigmaMinus V) =
      operatorAdd (nPlus (operatorDot U V)) (nMinus (operatorDot V U)) := by
  rw [oddOddSuperBracket, sigmaPlus_mul_sigmaMinus,
    sigmaMinus_mul_sigmaPlus]

theorem sigmaPlus_superBracket_self
    (U : OperatorVector A) :
    oddOddSuperBracket (sigmaPlus U) (sigmaPlus U) =
      sigmaMinus (operatorCross U U + operatorCross U U) := by
  exact sigmaPlus_superBracket_sigmaPlus (A := A) U U

theorem sigmaMinus_superBracket_self
    (U : OperatorVector A) :
    oddOddSuperBracket (sigmaMinus U) (sigmaMinus U) =
      sigmaPlus (-(operatorCross U U + operatorCross U U)) := by
  exact sigmaMinus_superBracket_sigmaMinus (A := A) U U

section CommutativeCoefficients

variable {C : Type*} [CommRing C]

@[simp] theorem sigmaPlus_oddOddSuperBracket_zero
    (U V : OperatorVector C) :
    oddOddSuperBracket (sigmaPlus U) (sigmaPlus V) = 0 := by
  change oddOddSuperBracket (sigmaPlus U) (sigmaPlus V) =
    ⟨0, 0, fun _ => 0, fun _ => 0⟩
  rw [oddOddSuperBracket, sigmaPlus_mul_sigmaPlus,
    sigmaPlus_mul_sigmaPlus]
  apply operatorZornMatrix_ext
  · simp [operatorAdd, sigmaMinus]
  · simp [operatorAdd, sigmaMinus]
  · funext i
    simp [operatorAdd, sigmaMinus]
  · funext i
    fin_cases i <;>
      simp [operatorAdd, sigmaMinus, operatorCross,
        InfoGeometry.Physics.NCG.NCZornElement.zornCross] <;> ring

@[simp] theorem sigmaMinus_oddOddSuperBracket_zero
    (U V : OperatorVector C) :
    oddOddSuperBracket (sigmaMinus U) (sigmaMinus V) = 0 := by
  change oddOddSuperBracket (sigmaMinus U) (sigmaMinus V) =
    ⟨0, 0, fun _ => 0, fun _ => 0⟩
  rw [oddOddSuperBracket, sigmaMinus_mul_sigmaMinus,
    sigmaMinus_mul_sigmaMinus]
  apply operatorZornMatrix_ext
  · simp [operatorAdd, sigmaPlus]
  · simp [operatorAdd, sigmaPlus]
  · funext i
    fin_cases i <;>
      simp [operatorAdd, sigmaPlus, operatorCross,
        InfoGeometry.Physics.NCG.NCZornElement.zornCross] <;> ring
  · funext i
    simp [operatorAdd, sigmaPlus]

@[simp] theorem chiralSigmaPlus_same_chirality_superbracket_zero
    (k l : Fin 3) (a b : C) :
    oddOddSuperBracket
        (operatorChiralSigmaPlus k a)
        (operatorChiralSigmaPlus l b) = 0 := by
  exact sigmaPlus_oddOddSuperBracket_zero
    (operatorColourUnit k a) (operatorColourUnit l b)

@[simp] theorem chiralSigmaMinus_same_chirality_superbracket_zero
    (k l : Fin 3) (a b : C) :
    oddOddSuperBracket
        (operatorChiralSigmaMinus k a)
        (operatorChiralSigmaMinus l b) = 0 := by
  exact sigmaMinus_oddOddSuperBracket_zero
    (operatorColourUnit k a) (operatorColourUnit l b)

end CommutativeCoefficients

end InfoGeometry.Canonical
