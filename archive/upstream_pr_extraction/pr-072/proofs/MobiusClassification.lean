import Mathlib

noncomputable section

namespace Mobius

/-- Discriminant of the fixed-point equation for a 2x2 matrix -/
def mobiusDiscriminant (g : Matrix (Fin 2) (Fin 2) ℝ) : ℝ :=
  Matrix.trace g ^ 2 - 4 * Matrix.det g

def IsEllipticMobius (g : Matrix (Fin 2) (Fin 2) ℝ) : Prop :=
  Matrix.det g = 1 ∧ mobiusDiscriminant g < 0

def IsParabolicMobius (g : Matrix (Fin 2) (Fin 2) ℝ) : Prop :=
  Matrix.det g = 1 ∧ mobiusDiscriminant g = 0 ∧ g ≠ 1 ∧ g ≠ -1

def IsHyperbolicMobius (g : Matrix (Fin 2) (Fin 2) ℝ) : Prop :=
  Matrix.det g = 1 ∧ 0 < mobiusDiscriminant g

theorem fixedPointPolynomial_discriminant
    (g : Matrix (Fin 2) (Fin 2) ℝ) :
    (g 1 1 - g 0 0) ^ 2 + 4 * g 1 0 * g 0 1 =
      Matrix.trace g ^ 2 - 4 * Matrix.det g := by
  have hd : Matrix.det g = g 0 0 * g 1 1 - g 0 1 * g 1 0 := Matrix.det_fin_two g
  have ht : Matrix.trace g = g 0 0 + g 1 1 := by
    dsimp [Matrix.trace]
    rw [Fin.sum_univ_two]
  rw [hd, ht]
  ring

theorem mobius_classification
    (g : Matrix (Fin 2) (Fin 2) ℝ)
    (_hdet : Matrix.det g = 1) :
    mobiusDiscriminant g < 0 ∨
    mobiusDiscriminant g = 0 ∨
    0 < mobiusDiscriminant g := by
  rcases lt_trichotomy (mobiusDiscriminant g) 0 with h | h | h
  · exact Or.inl h
  · exact Or.inr (Or.inl h)
  · exact Or.inr (Or.inr h)

end Mobius
