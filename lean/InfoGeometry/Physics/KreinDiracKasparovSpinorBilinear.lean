import Mathlib.Algebra.Star.Basic
import Mathlib.Algebra.Ring.Basic

namespace InfoGeometry.Physics

/-!
The algebraic Krein-adjoint core of the Dirac/Kasparov picture.

This owner is deliberately independent of the analytic `KreinSpace` and KK
owners.  It formalizes the algebraic consequences of a self-adjoint
involution `eta` and a self-adjoint grading `gamma`; it does not assert a
Hilbert-space representation, a Fredholm index, or a Kasparov product.
-/

structure KasparovKreinData (A : Type*) [Ring A] [StarRing A] where
  eta : A
  eta_sq : eta * eta = 1
  eta_star : star eta = eta
  gamma : A
  gamma_sq : gamma * gamma = 1
  gamma_star : star gamma = gamma

namespace KasparovKreinData

variable {A : Type*} [Ring A] [StarRing A]
variable (K : KasparovKreinData A)

/-- Algebraic Krein/Dirac adjoint induced by the fundamental symmetry. -/
def diracAdjoint (T : A) : A :=
  K.eta * star T * K.eta

theorem diracAdjoint_involution (T : A) :
    diracAdjoint K (diracAdjoint K T) = T := by
  dsimp [diracAdjoint]
  simp only [star_mul, K.eta_star, star_star]
  calc
    K.eta * (K.eta * (T * K.eta)) * K.eta
        = (K.eta * K.eta) * T * (K.eta * K.eta) := by
            simp [mul_assoc]
    _ = 1 * T * 1 := by rw [K.eta_sq]
    _ = T := by simp

theorem diracAdjoint_mul (T S : A) :
    diracAdjoint K (T * S) = diracAdjoint K S * diracAdjoint K T := by
  dsimp [diracAdjoint]
  rw [star_mul]
  calc
    K.eta * (star S * star T) * K.eta
        = K.eta * star S * (K.eta * K.eta) * star T * K.eta := by
            rw [K.eta_sq]
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
