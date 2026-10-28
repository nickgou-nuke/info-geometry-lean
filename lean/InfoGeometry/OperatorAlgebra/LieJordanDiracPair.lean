import InfoGeometry.OperatorAlgebra.OperatorDiracSchur

/-!
# Algebraic Dirac pairs built from the actual Lie--Jordan superoperators

The gamma actions and both transport directions act on the same full algebra
module. This file does not silently replace those actions by coefficient
matrices, and does not assume that gamma and transport operators commute.
-/

noncomputable section

namespace InfoGeometry.OperatorAlgebra.LieJordanDiracPair

open LieJordanDuality OperatorDiracSchur

variable (R : Type*) [CommRing R] {A : Type*} [Ring A] [Algebra R A]

/-- Sum of gamma-composed inner derivations. -/
def midpoint (g₁ g₂ : Module.End R A) (H₁ H₂ : A) : Module.End R A :=
  g₁ * ad R H₁ + g₂ * ad R H₂

/-- Sum of gamma-composed Jordan multiplications. -/
def perturbation (g₁ g₂ : Module.End R A) (S₁ S₂ : A) : Module.End R A :=
  g₁ * jordan R S₁ + g₂ * jordan R S₂

/-- The positive pair acts by composition, not by a coefficient-only surrogate. -/
def positive (g₁ g₂ : Module.End R A) (H₁ H₂ S₁ S₂ : A) : Module.End R A :=
  g₁ * dualPlus R H₁ S₁ + g₂ * dualPlus R H₂ S₂

def negative (g₁ g₂ : Module.End R A) (H₁ H₂ S₁ S₂ : A) : Module.End R A :=
  g₁ * dualMinus R H₁ S₁ + g₂ * dualMinus R H₂ S₂

/-- Literal evaluation on an algebra element. -/
theorem positive_apply (g₁ g₂ : Module.End R A) (H₁ H₂ S₁ S₂ X : A) :
    positive R g₁ g₂ H₁ H₂ S₁ S₂ X =
      g₁ ((H₁ * X - X * H₁) + (S₁ * X + X * S₁)) +
      g₂ ((H₂ * X - X * H₂) + (S₂ * X + X * S₂)) := rfl

theorem positive_split (g₁ g₂ : Module.End R A) (H₁ H₂ S₁ S₂ : A) :
    positive R g₁ g₂ H₁ H₂ S₁ S₂ =
      midpoint R g₁ g₂ H₁ H₂ + perturbation R g₁ g₂ S₁ S₂ := by
  simp only [positive, midpoint, perturbation, dualPlus, mul_add]
  abel

theorem negative_split (g₁ g₂ : Module.End R A) (H₁ H₂ S₁ S₂ : A) :
    negative R g₁ g₂ H₁ H₂ S₁ S₂ =
      midpoint R g₁ g₂ H₁ H₂ - perturbation R g₁ g₂ S₁ S₂ := by
  simp only [negative, midpoint, perturbation, dualMinus, mul_sub]
  abel

/-- Exact symmetric product of the real superoperators, with no flatness assumption. -/
theorem symmetric_product (g₁ g₂ : Module.End R A) (H₁ H₂ S₁ S₂ : A) :
    positive R g₁ g₂ H₁ H₂ S₁ S₂ * negative R g₁ g₂ H₁ H₂ S₁ S₂ +
      negative R g₁ g₂ H₁ H₂ S₁ S₂ * positive R g₁ g₂ H₁ H₂ S₁ S₂ =
      2 • (midpoint R g₁ g₂ H₁ H₂ * midpoint R g₁ g₂ H₁ H₂ -
        perturbation R g₁ g₂ S₁ S₂ * perturbation R g₁ g₂ S₁ S₂) := by
  rw [positive_split, negative_split]
  exact dual_dirac_symmetric_product _ _

/-- The bracket retains the coupling between the two operator components. -/
theorem bracket (g₁ g₂ : Module.End R A) (H₁ H₂ S₁ S₂ : A) :
    positive R g₁ g₂ H₁ H₂ S₁ S₂ * negative R g₁ g₂ H₁ H₂ S₁ S₂ -
      negative R g₁ g₂ H₁ H₂ S₁ S₂ * positive R g₁ g₂ H₁ H₂ S₁ S₂ =
      -(2 • (midpoint R g₁ g₂ H₁ H₂ * perturbation R g₁ g₂ S₁ S₂ -
        perturbation R g₁ g₂ S₁ S₂ * midpoint R g₁ g₂ H₁ H₂)) := by
  rw [positive_split, negative_split]
  exact dual_dirac_bracket _ _

end InfoGeometry.OperatorAlgebra.LieJordanDiracPair
