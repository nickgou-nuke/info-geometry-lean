import InfoGeometry.Physics.TQFTCobordismKasparovIndex
import InfoGeometry.Algebra.FiniteSpinAlgebra

namespace InfoGeometry.Physics

/-!
Algebraic commutator identities for an idempotent and an odd Dirac element.

This owner records the finite algebraic shadow of a second Chern-character
expression.  It does not claim a cyclic cocycle, an index theorem, or a
Yang--Mills curvature theorem; those require additional differential and
cyclic-cohomological structure.
-/

set_option autoImplicit false

variable {A : Type*} [Ring A] [Algebra ℝ A]

def diracCommutator (D E : A) : A :=
  D * E - E * D

theorem diracCommutator_is_odd
    (Gamma D E : A)
    (hD_odd : Gamma * D = -D * Gamma)
    (hE_even : Gamma * E = E * Gamma) :
    Gamma * diracCommutator D E =
      -(diracCommutator D E * Gamma) := by
  dsimp [diracCommutator]
  calc
    Gamma * (D * E - E * D)
        = Gamma * (D * E) - Gamma * (E * D) := by rw [mul_sub]
    _ = ((Gamma * D) * E) - ((Gamma * E) * D) := by
      simp only [mul_assoc]
    _ = ((-D * Gamma) * E) - ((E * Gamma) * D) := by
      rw [hD_odd, hE_even]
    _ = -((D * E - E * D) * Gamma) := by
      calc
        ((-D * Gamma) * E) - ((E * Gamma) * D)
            = -(D * (Gamma * E)) - E * (Gamma * D) := by
                simp only [mul_assoc, neg_mul]
        _ = -(D * (E * Gamma)) - E * (-D * Gamma) := by
                rw [hE_even, hD_odd]
        _ = -((D * E - E * D) * Gamma) := by
                noncomm_ring

theorem idempotent_commutator_square
    (D E : A)
    (hE : E * E = E) :
    E * diracCommutator D E * diracCommutator D E =
      E * D * E * D * E - E * (D * D) * E := by
  dsimp [diracCommutator]
  have hE_left (X : A) : E * (E * X) = E * X := by
    rw [← mul_assoc, hE]
  have hfirst :
      E * (D * E - E * D) = E * D * E - E * D := by
    simp only [mul_sub, mul_assoc, hE_left]
  rw [← mul_assoc, hfirst, sub_mul, mul_sub, mul_sub]
  have t1 :
      (E * D * E) * (D * E) = E * D * E * D * E := by
    simp only [mul_assoc]
  have t2 :
      (E * D * E) * (E * D) = E * D * E * D := by
    calc
      (E * D * E) * (E * D)
          = E * D * (E * E) * D := by simp only [mul_assoc]
      _ = E * D * E * D := by rw [hE]
  have t3 :
      (E * D) * (D * E) = E * (D * D) * E := by
    simp only [mul_assoc]
  have t4 :
      (E * D) * (E * D) = E * D * E * D := by
    simp only [mul_assoc]
  rw [t1, t2, t3, t4]
  noncomm_ring

def chernCharacterTwo
    (Tr : A →ₗ[ℝ] ℝ) (Gamma D E : A) : ℝ :=
  superTrace Tr Gamma (E * diracCommutator D E * diracCommutator D E)

theorem chernCharacterTwo_reduction
    (Tr : A →ₗ[ℝ] ℝ) (Gamma D E : A)
    (hE : E * E = E) :
    chernCharacterTwo Tr Gamma D E =
      superTrace Tr Gamma
        (E * D * E * D * E - E * (D * D) * E) := by
  dsimp [chernCharacterTwo]
  rw [idempotent_commutator_square D E hE]

end InfoGeometry.Physics
