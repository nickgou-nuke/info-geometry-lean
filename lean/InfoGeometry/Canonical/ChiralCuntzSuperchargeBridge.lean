import InfoGeometry.Canonical.Cuntz2Isometries
import InfoGeometry.Algebra.FiniteSpinAlgebra

namespace ChiralCuntzSuperchargeBridge

open CuntzAlgebra

/-- The chiral bridge uses the canonical noncommutative Cuntz `O₂` owner. -/
abbrev Cuntz2System (R : Type*) [Ring R] [StarRing R] :=
  _root_.CuntzAlgebra.Cuntz2Isometries R

variable {R : Type*} [Ring R] [StarRing R] (sys : Cuntz2System R)

/-- Right-moving chiral supercharge `Q₊ = S₁ S₂*`. -/
def Q_plus : R := _root_.CuntzAlgebra.S1 sys * star (_root_.CuntzAlgebra.S2 sys)

/-- Left-moving chiral supercharge `Q₋ = S₂ S₁*`. -/
def Q_minus : R := _root_.CuntzAlgebra.S2 sys * star (_root_.CuntzAlgebra.S1 sys)

theorem Q_plus_sq_zero : Q_plus sys * Q_plus sys = 0 := by
  dsimp [Q_plus]
  have h : star (S2 sys) * S1 sys = 0 := by
    have h' := CuntzAlgebra.isometries_ortho sys
    have h'' := congrArg star h'
    simpa [S1, S2] using h''
  calc
    (S1 sys * star (S2 sys)) * (S1 sys * star (S2 sys)) =
        S1 sys * (star (S2 sys) * S1 sys) * star (S2 sys) := by
          simp [mul_assoc]
    _ = 0 := by rw [h, mul_zero, zero_mul]

theorem Q_minus_sq_zero : Q_minus sys * Q_minus sys = 0 := by
  dsimp [Q_minus]
  have h : star (S1 sys) * S2 sys = 0 := CuntzAlgebra.isometries_ortho sys
  calc
    (S2 sys * star (S1 sys)) * (S2 sys * star (S1 sys)) =
        S2 sys * (star (S1 sys) * S2 sys) * star (S1 sys) := by
          simp [mul_assoc]
    _ = 0 := by rw [h, mul_zero, zero_mul]

theorem chiral_susy_anticommutator_eq_one :
    Q_plus sys * Q_minus sys + Q_minus sys * Q_plus sys = 1 := by
  dsimp [Q_plus, Q_minus]
  calc
    (S1 sys * star (S2 sys)) * (S2 sys * star (S1 sys)) +
        (S2 sys * star (S1 sys)) * (S1 sys * star (S2 sys)) =
        S1 sys * (star (S2 sys) * S2 sys) * star (S1 sys) +
          S2 sys * (star (S1 sys) * S1 sys) * star (S2 sys) := by
            simp [mul_assoc]
    _ = S1 sys * star (S1 sys) + S2 sys * star (S2 sys) := by
      have h1 : star (S1 sys) * S1 sys = 1 := CuntzAlgebra.h_isometry1 sys
      have h2 : star (S2 sys) * S2 sys = 1 := CuntzAlgebra.h_isometry2 sys
      rw [h2, h1]
      simp
    _ = 1 := by
      exact CuntzAlgebra.h_range_sum sys

end ChiralCuntzSuperchargeBridge
