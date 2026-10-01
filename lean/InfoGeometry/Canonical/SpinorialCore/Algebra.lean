import Mathlib

/-!
# Associative algebra underlying the corrected spinorial program

These are ring identities, not spacetime or matter reconstruction claims.
The mixed-sign Clifford bivector is an involution, not a complex structure.
-/

namespace InfoGeometry.Canonical.SpinorialCore

section Ring
variable {A : Type*} [Ring A]

/-- The product of anticommuting generators with squares +1 and -1 squares to +1. -/
theorem mixed_bivector_square (a b : A)
    (ha : a * a = 1) (hb : b * b = -1) (hba : b * a = -(a * b)) :
    (a * b) * (a * b) = 1 := by
  calc
    (a * b) * (a * b) = a * (b * a) * b := by noncomm_ring
    _ = a * (-(a * b)) * b := by rw [hba]
    _ = -((a * a) * (b * b)) := by noncomm_ring
    _ = 1 := by rw [ha, hb]; simp

/-- Inner differential, without identifying it with a manifold differential. -/
def innerDiff (D p : A) : A := D * p - p * D

/-- The grading associated with an idempotent. -/
def cutGrading (p : A) : A := 2 * p - 1

theorem cutGrading_square (p : A) (hp : p * p = p) :
    cutGrading p * cutGrading p = 1 := by
  unfold cutGrading
  calc
    (2 * p - 1) * (2 * p - 1) = 4 * (p * p - p) + 1 := by noncomm_ring
    _ = 1 := by rw [hp]; simp

theorem innerDiff_diagonal_zero (D p : A) (hp : p * p = p) :
    p * innerDiff D p * p = 0 := by
  unfold innerDiff
  calc
    p * (D * p - p * D) * p = p * D * (p * p) - (p * p) * D * p := by
      noncomm_ring
    _ = 0 := by rw [hp]; exact sub_self _

theorem innerDiff_complement_diagonal_zero (D p : A) (hp : p * p = p) :
    (1 - p) * innerDiff D p * (1 - p) = 0 := by
  unfold innerDiff
  calc
    (1 - p) * (D * p - p * D) * (1 - p) =
        D * p - D * (p * p) - p * D + (p * p) * D +
          p * D * (p * p) - (p * p) * D * p := by noncomm_ring
    _ = 0 := by rw [hp]; noncomm_ring

theorem innerDiff_is_odd (D p : A) (hp : p * p = p) :
    cutGrading p * innerDiff D p + innerDiff D p * cutGrading p = 0 := by
  have h : p * innerDiff D p + innerDiff D p * p = innerDiff D p := by
    unfold innerDiff
    calc
      p * (D * p - p * D) + (D * p - p * D) * p =
          D * (p * p) - (p * p) * D := by noncomm_ring
      _ = D * p - p * D := by rw [hp]
  unfold cutGrading
  calc
    (2 * p - 1) * innerDiff D p + innerDiff D p * (2 * p - 1) =
        2 * (p * innerDiff D p + innerDiff D p * p - innerDiff D p) := by
      noncomm_ring
    _ = 0 := by rw [h]; simp

/-- The square of an odd operator commutes with its grading. -/
theorem odd_square_commutes (G d : A) (h : G * d + d * G = 0) :
    G * (d * d) = (d * d) * G := by
  have hgd : G * d = -(d * G) := by
    rw [eq_neg_iff_add_eq_zero]
    exact h
  calc
    G * (d * d) = (G * d) * d := by rw [mul_assoc]
    _ = (-(d * G)) * d := by rw [hgd]
    _ = -(d * (G * d)) := by noncomm_ring
    _ = -(d * (-(d * G))) := by rw [hgd]
    _ = (d * d) * G := by noncomm_ring

theorem innerDiff_square_is_even (D p : A) (hp : p * p = p) :
    cutGrading p * (innerDiff D p * innerDiff D p) =
      (innerDiff D p * innerDiff D p) * cutGrading p :=
  odd_square_commutes _ _ (innerDiff_is_odd D p hp)

end Ring
end InfoGeometry.Canonical.SpinorialCore
