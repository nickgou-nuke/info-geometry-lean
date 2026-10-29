/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.OperatorAlgebra.LieJordanEndomorphisms

/-!
# Actual Clifford-weighted operator composition

The input operators act on the full algebra. Clifford coefficients act by
left multiplication, so they need not commute with the Lie--Jordan actions.
The square theorem explicitly retains all four coefficient commutators.
This is a finite/algebraic operator identity, not a differential Lichnerowicz
formula, and it does not supply a connection or a curvature tensor on a manifold.
-/

namespace InfoGeometry.OperatorAlgebra.LieJordan

/-- A ring identity with every coefficient-transport defect retained. -/
theorem clifford_square_with_defects {E : Type*} [Ring E]
    (g₁ g₂ t₁ t₂ : E) (h₁ : g₁ * g₁ = 1) (h₂ : g₂ * g₂ = 1)
    (h₁₂ : g₁ * g₂ + g₂ * g₁ = 0) :
    (g₁ * t₁ + g₂ * t₂) * (g₁ * t₁ + g₂ * t₂) =
      t₁ * t₁ + t₂ * t₂ + g₁ * g₂ * (t₁ * t₂ - t₂ * t₁) +
        g₁ * (t₁ * g₁ - g₁ * t₁) * t₁ +
        g₁ * (t₁ * g₂ - g₂ * t₁) * t₂ +
        g₂ * (t₂ * g₁ - g₁ * t₂) * t₁ +
        g₂ * (t₂ * g₂ - g₂ * t₂) * t₂ := by
  have hswap : g₂ * g₁ = -(g₁ * g₂) := by
    calc
      g₂ * g₁ = (g₁ * g₂ + g₂ * g₁) - g₁ * g₂ := by abel
      _ = -(g₁ * g₂) := by rw [h₁₂, zero_sub]
  calc
    (g₁ * t₁ + g₂ * t₂) * (g₁ * t₁ + g₂ * t₂) =
      (g₁ * g₁) * (t₁ * t₁) + (g₂ * g₂) * (t₂ * t₂) +
        (g₁ * g₂) * (t₁ * t₂) + (g₂ * g₁) * (t₂ * t₁) +
        g₁ * (t₁ * g₁ - g₁ * t₁) * t₁ +
        g₁ * (t₁ * g₂ - g₂ * t₁) * t₂ +
        g₂ * (t₂ * g₁ - g₁ * t₂) * t₁ +
        g₂ * (t₂ * g₂ - g₂ * t₂) * t₂ := by noncomm_ring
    _ = _ := by rw [h₁, h₂, hswap]; noncomm_ring

variable (R : Type*) [CommRing R] {A : Type*} [Ring A] [Algebra R A]

/-- Clifford coefficients composed with operators, not multiplied into their labels. -/
def weighted (Γ₁ Γ₂ : A) (T₁ T₂ : Module.End R A) : Module.End R A :=
  LinearMap.mulLeft R Γ₁ * T₁ + LinearMap.mulLeft R Γ₂ * T₂

@[simp] theorem weighted_apply (Γ₁ Γ₂ : A) (T₁ T₂ : Module.End R A) (X : A) :
    weighted R Γ₁ Γ₂ T₁ T₂ X = Γ₁ * T₁ X + Γ₂ * T₂ X := rfl

def diracPlus (Γ₁ Γ₂ H₁ H₂ S₁ S₂ : A) : Module.End R A :=
  weighted R Γ₁ Γ₂ (plus R H₁ S₁) (plus R H₂ S₂)

def diracMinus (Γ₁ Γ₂ H₁ H₂ S₁ S₂ : A) : Module.End R A :=
  weighted R Γ₁ Γ₂ (minus R H₁ S₁) (minus R H₂ S₂)

/-- The coefficient defect depends on `H + S` on the left, not just on `H`. -/
theorem plus_coefficient_defect (H S Γ : A) :
    plus R H S * LinearMap.mulLeft R Γ - LinearMap.mulLeft R Γ * plus R H S =
      LinearMap.mulLeft R ((H + S) * Γ - Γ * (H + S)) := by
  ext X
  change (H * (Γ * X) - (Γ * X) * H) + (S * (Γ * X) + (Γ * X) * S) -
      Γ * ((H * X - X * H) + (S * X + X * S)) =
    ((H + S) * Γ - Γ * (H + S)) * X
  noncomm_ring

theorem minus_coefficient_defect (H S Γ : A) :
    minus R H S * LinearMap.mulLeft R Γ - LinearMap.mulLeft R Γ * minus R H S =
      LinearMap.mulLeft R ((H - S) * Γ - Γ * (H - S)) := by
  ext X
  change (H * (Γ * X) - (Γ * X) * H) - (S * (Γ * X) + (Γ * X) * S) -
      Γ * ((H * X - X * H) - (S * X + X * S)) =
    ((H - S) * Γ - Γ * (H - S)) * X
  noncomm_ring

/-- Exact square for arbitrary endomorphisms and a noncentral Clifford pair. -/
theorem weighted_square (Γ₁ Γ₂ : A) (T₁ T₂ : Module.End R A)
    (h₁ : Γ₁ * Γ₁ = 1) (h₂ : Γ₂ * Γ₂ = 1)
    (h₁₂ : Γ₁ * Γ₂ + Γ₂ * Γ₁ = 0) :
    weighted R Γ₁ Γ₂ T₁ T₂ * weighted R Γ₁ Γ₂ T₁ T₂ =
      T₁ * T₁ + T₂ * T₂ +
        LinearMap.mulLeft R Γ₁ * LinearMap.mulLeft R Γ₂ * (T₁ * T₂ - T₂ * T₁) +
        LinearMap.mulLeft R Γ₁ *
          (T₁ * LinearMap.mulLeft R Γ₁ - LinearMap.mulLeft R Γ₁ * T₁) * T₁ +
        LinearMap.mulLeft R Γ₁ *
          (T₁ * LinearMap.mulLeft R Γ₂ - LinearMap.mulLeft R Γ₂ * T₁) * T₂ +
        LinearMap.mulLeft R Γ₂ *
          (T₂ * LinearMap.mulLeft R Γ₁ - LinearMap.mulLeft R Γ₁ * T₂) * T₁ +
        LinearMap.mulLeft R Γ₂ *
          (T₂ * LinearMap.mulLeft R Γ₂ - LinearMap.mulLeft R Γ₂ * T₂) * T₂ := by
  have hs₁ : LinearMap.mulLeft R Γ₁ * LinearMap.mulLeft R Γ₁ = 1 := by
    ext X
    change Γ₁ * (Γ₁ * X) = X
    rw [← mul_assoc, h₁, one_mul]
  have hs₂ : LinearMap.mulLeft R Γ₂ * LinearMap.mulLeft R Γ₂ = 1 := by
    ext X
    change Γ₂ * (Γ₂ * X) = X
    rw [← mul_assoc, h₂, one_mul]
  have hs₁₂ : LinearMap.mulLeft R Γ₁ * LinearMap.mulLeft R Γ₂ +
      LinearMap.mulLeft R Γ₂ * LinearMap.mulLeft R Γ₁ = 0 := by
    ext X
    change Γ₁ * (Γ₂ * X) + Γ₂ * (Γ₁ * X) = 0
    rw [← mul_assoc, ← mul_assoc, ← add_mul, h₁₂, zero_mul]
  exact clifford_square_with_defects
    (LinearMap.mulLeft R Γ₁) (LinearMap.mulLeft R Γ₂) T₁ T₂ hs₁ hs₂ hs₁₂

/-- Splitting holds for the actual composed endomorphisms. -/
theorem diracPlus_split (Γ₁ Γ₂ H₁ H₂ S₁ S₂ : A) :
    diracPlus R Γ₁ Γ₂ H₁ H₂ S₁ S₂ =
      weighted R Γ₁ Γ₂ (lieOp R H₁) (lieOp R H₂) +
        weighted R Γ₁ Γ₂ (jordanOp R S₁) (jordanOp R S₂) := by
  unfold diracPlus weighted plus
  simp only [mul_add]
  abel

theorem diracMinus_split (Γ₁ Γ₂ H₁ H₂ S₁ S₂ : A) :
    diracMinus R Γ₁ Γ₂ H₁ H₂ S₁ S₂ =
      weighted R Γ₁ Γ₂ (lieOp R H₁) (lieOp R H₂) -
        weighted R Γ₁ Γ₂ (jordanOp R S₁) (jordanOp R S₂) := by
  unfold diracMinus weighted minus
  simp only [mul_sub]
  abel

/-- The symmetrized product removes mixed terms without assuming commutativity. -/
theorem dirac_anticommutator (Γ₁ Γ₂ H₁ H₂ S₁ S₂ : A) :
    let D := weighted R Γ₁ Γ₂ (lieOp R H₁) (lieOp R H₂)
    let J := weighted R Γ₁ Γ₂ (jordanOp R S₁) (jordanOp R S₂)
    diracPlus R Γ₁ Γ₂ H₁ H₂ S₁ S₂ * diracMinus R Γ₁ Γ₂ H₁ H₂ S₁ S₂ +
      diracMinus R Γ₁ Γ₂ H₁ H₂ S₁ S₂ * diracPlus R Γ₁ Γ₂ H₁ H₂ S₁ S₂ =
      (D * D - J * J) + (D * D - J * J) := by
  dsimp only
  simp only [diracPlus_split, diracMinus_split, mul_add, add_mul, mul_sub, sub_mul]
  abel

/-- The antisymmetrized product measures, rather than discards, the coupling. -/
theorem dirac_commutator (Γ₁ Γ₂ H₁ H₂ S₁ S₂ : A) :
    let D := weighted R Γ₁ Γ₂ (lieOp R H₁) (lieOp R H₂)
    let J := weighted R Γ₁ Γ₂ (jordanOp R S₁) (jordanOp R S₂)
    diracPlus R Γ₁ Γ₂ H₁ H₂ S₁ S₂ * diracMinus R Γ₁ Γ₂ H₁ H₂ S₁ S₂ -
      diracMinus R Γ₁ Γ₂ H₁ H₂ S₁ S₂ * diracPlus R Γ₁ Γ₂ H₁ H₂ S₁ S₂ =
      -((D * J - J * D) + (D * J - J * D)) := by
  dsimp only
  simp only [diracPlus_split, diracMinus_split, mul_add, add_mul, mul_sub, sub_mul]
  abel

end InfoGeometry.OperatorAlgebra.LieJordan
