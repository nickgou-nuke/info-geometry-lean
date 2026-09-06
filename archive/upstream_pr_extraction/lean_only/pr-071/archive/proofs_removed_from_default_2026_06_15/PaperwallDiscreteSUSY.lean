import Mathlib.Algebra.Ring.Basic

/-!
# Discrete Spatial N=1 SUSY and Paperwall Holography

This file formalizes the emergence of an exact discrete spatial Supersymmetry 
algebra derived purely from the geometric properties of a "paperwall" boundary.

Specifically, when a 2D boundary CFT has non-symmorphic chiral glide reflections (`G`),
the operator acts as a discrete "square root" of spatial translation (`T`). Because 
the glide reflection reverses orientation/chirality, it behaves exactly as a 
fermionic supercharge `Q`.
-/

/--
An algebraic structure modeling a discrete space with a grading/parity 
operator `Γ` and a chiral glide reflection `G`.
-/
class GlideSUSY (R : Type) [Ring R] where
  Γ : R
  G : R
  /-- The grading operator is an involution (parity). -/
  grading_sq : Γ * Γ = 1
  /-- The glide reflection is orientation-reversing (odd parity). -/
  glide_odd : Γ * G + G * Γ = 0

namespace GlideSUSY

variable {R : Type} [Ring R] [GlideSUSY R]

/-- The discrete supercharge is defined as the chiral glide reflection. -/
def Q : R := G

/-- The Hamiltonian is the pure lattice translation (G² = T). -/
def H : R := G * G

/--
Lemma: Shifting the glide reflection past the grading operator 
picks up a minus sign.
-/
lemma gamma_g_eq_neg_g_gamma : Γ * G = - (G * Γ) := by
  calc
    Γ * G = Γ * G + G * Γ - G * Γ := by rw [add_sub_cancel_right]
    _ = 0 - G * Γ := by rw [glide_odd]
    _ = - (G * Γ) := by rw [zero_sub]

/-- Translations are bosonic (even) operators: they commute with the grading. -/
theorem H_is_even : Γ * H - H * Γ = 0 := by
  dsimp [H]
  calc
    Γ * (G * G) - (G * G) * Γ
      = (Γ * G) * G - G * G * Γ := by rw [← mul_assoc]
    _ = -(G * Γ) * G - G * G * Γ := by rw [gamma_g_eq_neg_g_gamma]
    _ = -G * (Γ * G) - G * G * Γ := by rw [neg_mul, ← mul_assoc]
    _ = -G * -(G * Γ) - G * G * Γ := by rw [gamma_g_eq_neg_g_gamma]
    _ = G * (G * Γ) - G * G * Γ := by rw [neg_mul_neg]
    _ = (G * G) * Γ - (G * G) * Γ := by rw [← mul_assoc]
    _ = 0 := by rw [sub_self]

/-- The glide reflection acts as a discrete odd supercharge. -/
theorem Q_is_odd : Γ * Q + Q * Γ = 0 := by
  dsimp [Q]
  exact glide_odd

/-- N=1 Superalgebra closure: {Q, Q} = 2H. -/
theorem susy_closure : Q * Q + Q * Q = 2 * H := by
  dsimp [Q, H]
  ring

/-- The supercharge commutes with the Hamiltonian: [Q, H] = 0. -/
theorem Q_H_comm : Q * H - H * Q = 0 := by
  dsimp [Q, H]
  calc
    G * (G * G) - (G * G) * G
      = (G * G) * G - (G * G) * G := by rw [← mul_assoc]
    _ = 0 := by rw [sub_self]

end GlideSUSY
