import Mathlib.Algebra.Star.Basic
import InfoGeometry.Algebra.FiniteSpinAlgebra
import Mathlib.Algebra.Ring.Basic

namespace InfoGeometry.Physics

/-!
The algebraic Krein-adjoint core of the Dirac/Kasparov picture.

This owner is deliberately independent of the analytic `KreinSpace` and KK
owners.  It formalizes the algebraic consequences of a self-adjoint
involution `eta` and a self-adjoint grading `gamma`; it does not assert a
Hilbert-space representation, a Fredholm index, or a Kasparov product.
-/

structure KasparovKreinDataRaw (A : Type*) [Ring A] [StarRing A] where
  eta : A
  gamma : A

def KasparovKreinDataLaws {A : Type*} [Ring A] [StarRing A]
    (K : KasparovKreinDataRaw A) : Prop :=
  K.eta * K.eta = 1 ∧
  star K.eta = K.eta ∧
  K.gamma * K.gamma = 1 ∧
  star K.gamma = K.gamma

def KasparovKreinData (A : Type*) [Ring A] [StarRing A] :=
  { K : KasparovKreinDataRaw A // KasparovKreinDataLaws K }

namespace KasparovKreinData

def eta {A : Type*} [Ring A] [StarRing A] (K : KasparovKreinData A) : A := K.1.eta
def gamma {A : Type*} [Ring A] [StarRing A] (K : KasparovKreinData A) : A := K.1.gamma

variable {A : Type*} [Ring A] [StarRing A]
variable (K : KasparovKreinData A)

/-- Algebraic Krein/Dirac adjoint induced by the fundamental symmetry. -/
def diracAdjoint (T : A) : A :=
  K.eta * star T * K.eta

theorem diracAdjoint_involution (T : A)
    :
    diracAdjoint K (diracAdjoint K T) = T := by
  dsimp [diracAdjoint]
  have hstar : star K.eta = K.eta := K.2.2.1
  have heta : K.eta * K.eta = 1 := K.2.1
  simp only [star_mul, star_star]
  rw [hstar]
  calc
    K.eta * (K.eta * (T * K.eta)) * K.eta
        = (K.eta * K.eta) * T * (K.eta * K.eta) := by
            simp [mul_assoc]
    _ = 1 * T * 1 := by rw [heta]
    _ = T := by simp

theorem diracAdjoint_mul (T S : A)
    :
    diracAdjoint K (T * S) = diracAdjoint K S * diracAdjoint K T := by
  dsimp [diracAdjoint]
  rw [star_mul]
  have heta : K.eta * K.eta = 1 := K.2.1
  calc
    K.eta * (star S * star T) * K.eta
        = K.eta * star S * (K.eta * K.eta) * star T * K.eta := by
            rw [heta]
            simp only [mul_one, mul_assoc]
    _ = (K.eta * star S * K.eta) *
          (K.eta * star T * K.eta) := by
            simp only [mul_assoc]

/-- A Dirac operator is Krein-self-adjoint and odd for the grading. -/
def IsKasparovDirac (D : A) : Prop :=
  diracAdjoint K D = D ∧ K.gamma * D = -D * K.gamma

theorem kasparov_dirac_sq_even (D : A)
    (hD : K.gamma * D = -D * K.gamma) :
    K.gamma * (D * D) = (D * D) * K.gamma := by
  calc
    K.gamma * (D * D) = (K.gamma * D) * D := by rw [mul_assoc]
    _ = (-D * K.gamma) * D := by rw [hD]
    _ = -D * (K.gamma * D) := by rw [mul_assoc]
    _ = -D * (-D * K.gamma) := by rw [hD]
    _ = (-D * -D) * K.gamma := by rw [← mul_assoc]
    _ = (D * D) * K.gamma := by rw [neg_mul_neg]

end KasparovKreinData

end InfoGeometry.Physics
