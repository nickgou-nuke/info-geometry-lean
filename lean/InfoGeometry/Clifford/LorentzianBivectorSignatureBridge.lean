import Mathlib.Tactic.NoncommRing
import InfoGeometry.Algebra.FiniteSpinAlgebra

/-!
# Lorentzian bivector signature bridge

An anticommuting product of Clifford generators can square to either sign.
This finite algebraic distinction is the boost/rotation split inside grade
two; it does not require a matrix realization or an exponential theorem.
-/

namespace InfoGeometry.Clifford.LorentzianBivectorSignatureBridge

variable {A : Type*} [Ring A]

theorem mixed_bivector_sq_one {a b : A}
    (ha : a * a = 1) (hb : b * b = -1)
    (hanti : a * b + b * a = 0) :
    (b * a) * (b * a) = 1 := by
  have hab : a * b = -(b * a) := by
    exact eq_neg_of_add_eq_zero_left hanti
  calc
    (b * a) * (b * a) = b * (a * b) * a := by noncomm_ring
    _ = b * (-(b * a)) * a := by rw [hab]
    _ = -(b * b) * (a * a) := by noncomm_ring
    _ = 1 := by rw [ha, hb]; simp

theorem negative_bivector_sq_neg_one {a b : A}
    (ha : a * a = -1) (hb : b * b = -1)
    (hanti : a * b + b * a = 0) :
    (a * b) * (a * b) = -1 := by
  have hanti' : b * a + a * b = 0 := by
    simpa [add_comm] using hanti
  have hba : b * a = -(a * b) := by
    exact eq_neg_of_add_eq_zero_left hanti'
  calc
    (a * b) * (a * b) = a * (b * a) * b := by noncomm_ring
    _ = a * (-(a * b)) * b := by rw [hba]
    _ = -(a * a) * (b * b) := by noncomm_ring
    _ = -1 := by rw [ha, hb]; simp

theorem positive_bivector_sq_neg_one {a b : A}
    (ha : a * a = 1) (hb : b * b = 1)
    (hanti : a * b + b * a = 0) :
    (a * b) * (a * b) = -1 := by
  calc
    (a * b) * (a * b) = a * (b * a) * b := by noncomm_ring
    _ = a * (-(a * b)) * b := by
      have hba : b * a = -(a * b) := eq_neg_of_add_eq_zero_left (by simpa [add_comm] using hanti)
      rw [hba]
    _ = -((a * a) * (b * b)) := by noncomm_ring
    _ = -1 := by rw [ha, hb]; simp

end InfoGeometry.Clifford.LorentzianBivectorSignatureBridge
