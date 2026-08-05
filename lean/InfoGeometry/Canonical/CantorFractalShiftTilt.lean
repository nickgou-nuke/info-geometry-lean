import Mathlib.Tactic

/-!
# Finite three-branch Toeplitz defect identities

The definitions below use a concrete family of three generators and prove its
finite defect annihilation law directly. No representation packet is added.
-/

namespace InfoGeometry.Fractal

variable {A : Type*} [Ring A] [StarRing A]

def toeplitzDefectP0 (S : Fin 3 → A) : A :=
  1 - (S 0 * star (S 0) +
    S 1 * star (S 1) + S 2 * star (S 2))

def toeplitzTilt (c : Fin 3) : Fin 3 :=
  if c = 0 then 1 else if c = 1 then 2 else 0

def toeplitzTiltOperator (S : Fin 3 → A) (c : Fin 3) : A :=
  S (toeplitzTilt c)

theorem toeplitz_defect_annihilation_0
    (S : Fin 3 → A)
    (isometry : ∀ c, star (S c) * S c = 1)
    (orthogonality : ∀ c d, c ≠ d → star (S c) * S d = 0) :
    star (S 0) * toeplitzDefectP0 S = 0 := by
  dsimp [toeplitzDefectP0]
  rw [mul_sub, mul_one, mul_add, mul_add]
  have h0 : star (S 0) * (S 0 * star (S 0)) = star (S 0) := by
    rw [← mul_assoc, isometry 0, one_mul]
  have h1 : star (S 0) * (S 1 * star (S 1)) = 0 := by
    rw [← mul_assoc, orthogonality 0 1 (by decide), zero_mul]
  have h2 : star (S 0) * (S 2 * star (S 2)) = 0 := by
    rw [← mul_assoc, orthogonality 0 2 (by decide), zero_mul]
  rw [h0, h1, h2]
  simp

end InfoGeometry.Fractal
