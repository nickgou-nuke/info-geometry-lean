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

/-- Forward and sign-flipped Clifford-weighted operators in an arbitrary
associative ring. -/
def cliffordDiracForward {E : Type*} [Ring E]
    (g₁ g₂ t₁ t₂ : E) : E := g₁ * t₁ + g₂ * t₂

def cliffordDiracFlipped {E : Type*} [Ring E]
    (g₁ g₂ t₁ t₂ : E) : E := g₁ * t₁ - g₂ * t₂

/-- Lichnerowicz square in an arbitrary associative ring when the Clifford
coefficients commute with both operator directions. -/
theorem clifford_square_of_commuting_coefficients {E : Type*} [Ring E]
    (g₁ g₂ t₁ t₂ : E)
    (h₁ : g₁ * g₁ = 1) (h₂ : g₂ * g₂ = 1)
    (h₁₂ : g₁ * g₂ + g₂ * g₁ = 0)
    (h₁₁ : g₁ * t₁ = t₁ * g₁) (h₁₂' : g₁ * t₂ = t₂ * g₁)
    (h₂₁ : g₂ * t₁ = t₁ * g₂) (h₂₂ : g₂ * t₂ = t₂ * g₂) :
    cliffordDiracForward g₁ g₂ t₁ t₂ * cliffordDiracForward g₁ g₂ t₁ t₂ =
      t₁ * t₁ + t₂ * t₂ + g₁ * g₂ * (t₁ * t₂ - t₂ * t₁) := by
  simpa [cliffordDiracForward, h₁₁, h₁₂', h₂₁, h₂₂] using
    clifford_square_with_defects g₁ g₂ t₁ t₂ h₁ h₂ h₁₂

/-- The hyperbolic wave term, retained as an operator expression. -/
def hyperbolicWaveOperator {E : Type*} [Ring E] (t₁ t₂ : E) : E :=
  t₁ * t₁ - t₂ * t₂

/-- The spin-weighted symmetric cross term. -/
def cliffordJordanStrain {E : Type*} [Ring E] (g₁ g₂ t₁ t₂ : E) : E :=
  (g₁ * g₂) * (t₁ * t₂ + t₂ * t₁)

/-- Exact forward/flipped Clifford cross-products in an arbitrary associative
ring. The four coefficient-transport defects remain explicit, so this does
not require the Clifford coefficients to commute with the directions. -/
theorem hyperbolic_clifford_cross_products_with_defects {E : Type*} [Ring E]
    (g₁ g₂ t₁ t₂ : E)
    (hg₁ : g₁ * g₁ = 1) (hg₂ : g₂ * g₂ = 1)
    (hg₁₂ : g₁ * g₂ + g₂ * g₁ = 0) :
    cliffordDiracForward g₁ g₂ t₁ t₂ * cliffordDiracFlipped g₁ g₂ t₁ t₂ =
        hyperbolicWaveOperator t₁ t₂ - cliffordJordanStrain g₁ g₂ t₁ t₂ +
          g₁ * (t₁ * g₁ - g₁ * t₁) * t₁ -
          g₂ * (t₂ * g₂ - g₂ * t₂) * t₂ -
          g₁ * (t₁ * g₂ - g₂ * t₁) * t₂ +
          g₂ * (t₂ * g₁ - g₁ * t₂) * t₁ ∧
    cliffordDiracFlipped g₁ g₂ t₁ t₂ * cliffordDiracForward g₁ g₂ t₁ t₂ =
        hyperbolicWaveOperator t₁ t₂ + cliffordJordanStrain g₁ g₂ t₁ t₂ +
          g₁ * (t₁ * g₁ - g₁ * t₁) * t₁ -
          g₂ * (t₂ * g₂ - g₂ * t₂) * t₂ +
          g₁ * (t₁ * g₂ - g₂ * t₁) * t₂ -
          g₂ * (t₂ * g₁ - g₁ * t₂) * t₁ := by
  have hSquare₁ : (g₁ * t₁) * (g₁ * t₁) =
      t₁ * t₁ + g₁ * (t₁ * g₁ - g₁ * t₁) * t₁ := by
    calc
      _ = (g₁ * g₁) * (t₁ * t₁) +
          g₁ * (t₁ * g₁ - g₁ * t₁) * t₁ := by noncomm_ring
      _ = _ := by rw [hg₁]; simp
  have hSquare₂ : (g₂ * t₂) * (g₂ * t₂) =
      t₂ * t₂ + g₂ * (t₂ * g₂ - g₂ * t₂) * t₂ := by
    calc
      _ = (g₂ * g₂) * (t₂ * t₂) +
          g₂ * (t₂ * g₂ - g₂ * t₂) * t₂ := by noncomm_ring
      _ = _ := by rw [hg₂]; simp
  have hCross₁₂ : (g₁ * t₁) * (g₂ * t₂) =
      (g₁ * g₂) * (t₁ * t₂) +
        g₁ * (t₁ * g₂ - g₂ * t₁) * t₂ := by noncomm_ring
  have hCross₂₁ : (g₂ * t₂) * (g₁ * t₁) =
      (g₂ * g₁) * (t₂ * t₁) +
        g₂ * (t₂ * g₁ - g₁ * t₂) * t₁ := by noncomm_ring
  have hSwap : g₂ * g₁ = -(g₁ * g₂) :=
    eq_neg_of_add_eq_zero_right hg₁₂
  constructor
  · change (g₁ * t₁ + g₂ * t₂) * (g₁ * t₁ - g₂ * t₂) = _
    calc
      _ = (g₁ * t₁) * (g₁ * t₁) - (g₁ * t₁) * (g₂ * t₂) +
          (g₂ * t₂) * (g₁ * t₁) - (g₂ * t₂) * (g₂ * t₂) := by noncomm_ring
      _ = _ := by
        rw [hSquare₁, hCross₁₂, hCross₂₁, hSquare₂, hSwap]
        simp only [hyperbolicWaveOperator, cliffordJordanStrain, neg_mul, mul_add]
        abel_nf
  · change (g₁ * t₁ - g₂ * t₂) * (g₁ * t₁ + g₂ * t₂) = _
    calc
      _ = (g₁ * t₁) * (g₁ * t₁) + (g₁ * t₁) * (g₂ * t₂) -
          (g₂ * t₂) * (g₁ * t₁) - (g₂ * t₂) * (g₂ * t₂) := by noncomm_ring
      _ = _ := by
        rw [hSquare₁, hCross₁₂, hCross₂₁, hSquare₂, hSwap]
        simp only [hyperbolicWaveOperator, cliffordJordanStrain, neg_mul, mul_add]
        abel_nf

/-- Exact hyperbolic Clifford cross-products. If the Clifford coefficients
commute with the operator directions, the forward/flipped products split into
the wave and Jordan-strain operators. No matrices or commutative operator
carrier are used. -/
theorem hyperbolic_clifford_cross_products {E : Type*} [Ring E]
    (g₁ g₂ t₁ t₂ : E)
    (hg₁ : g₁ * g₁ = 1) (hg₂ : g₂ * g₂ = 1)
    (hg₁₂ : g₁ * g₂ + g₂ * g₁ = 0)
    (h₁₁ : g₁ * t₁ = t₁ * g₁) (h₁₂ : g₁ * t₂ = t₂ * g₁)
    (h₂₁ : g₂ * t₁ = t₁ * g₂) (h₂₂ : g₂ * t₂ = t₂ * g₂) :
    cliffordDiracForward g₁ g₂ t₁ t₂ * cliffordDiracFlipped g₁ g₂ t₁ t₂ =
        hyperbolicWaveOperator t₁ t₂ - cliffordJordanStrain g₁ g₂ t₁ t₂ ∧
    cliffordDiracFlipped g₁ g₂ t₁ t₂ * cliffordDiracForward g₁ g₂ t₁ t₂ =
        hyperbolicWaveOperator t₁ t₂ + cliffordJordanStrain g₁ g₂ t₁ t₂ ∧
    cliffordDiracForward g₁ g₂ t₁ t₂ * cliffordDiracFlipped g₁ g₂ t₁ t₂ +
        cliffordDiracFlipped g₁ g₂ t₁ t₂ * cliffordDiracForward g₁ g₂ t₁ t₂ =
      2 • hyperbolicWaveOperator t₁ t₂ ∧
    cliffordDiracForward g₁ g₂ t₁ t₂ * cliffordDiracFlipped g₁ g₂ t₁ t₂ -
        cliffordDiracFlipped g₁ g₂ t₁ t₂ * cliffordDiracForward g₁ g₂ t₁ t₂ =
      -(2 • cliffordJordanStrain g₁ g₂ t₁ t₂) := by
  have hswap : g₂ * g₁ = -(g₁ * g₂) :=
    eq_neg_of_add_eq_zero_right hg₁₂
  have c₁₁ : t₁ * g₁ = g₁ * t₁ := h₁₁.symm
  have c₁₂ : t₂ * g₁ = g₁ * t₂ := h₁₂.symm
  have c₂₁ : t₁ * g₂ = g₂ * t₁ := h₂₁.symm
  have c₂₂ : t₂ * g₂ = g₂ * t₂ := h₂₂.symm
  have hs₁ : (g₁ * t₁) * (g₁ * t₁) = t₁ * t₁ := by
    calc
      (g₁ * t₁) * (g₁ * t₁) = g₁ * (t₁ * g₁) * t₁ := by noncomm_ring
      _ = g₁ * (g₁ * t₁) * t₁ := by rw [c₁₁]
      _ = (g₁ * g₁) * (t₁ * t₁) := by noncomm_ring
      _ = t₁ * t₁ := by rw [hg₁]; simp
  have hs₂ : (g₂ * t₂) * (g₂ * t₂) = t₂ * t₂ := by
    calc
      (g₂ * t₂) * (g₂ * t₂) = g₂ * (t₂ * g₂) * t₂ := by noncomm_ring
      _ = g₂ * (g₂ * t₂) * t₂ := by rw [c₂₂]
      _ = (g₂ * g₂) * (t₂ * t₂) := by noncomm_ring
      _ = t₂ * t₂ := by rw [hg₂]; simp
  have hcross₁₂ : (g₁ * t₁) * (g₂ * t₂) = (g₁ * g₂) * (t₁ * t₂) := by
    calc
      (g₁ * t₁) * (g₂ * t₂) = g₁ * (t₁ * g₂) * t₂ := by noncomm_ring
      _ = g₁ * (g₂ * t₁) * t₂ := by rw [c₂₁]
      _ = (g₁ * g₂) * (t₁ * t₂) := by noncomm_ring
  have hcross₂₁ : (g₂ * t₂) * (g₁ * t₁) = -(g₁ * g₂) * (t₂ * t₁) := by
    calc
      (g₂ * t₂) * (g₁ * t₁) = g₂ * (t₂ * g₁) * t₁ := by noncomm_ring
      _ = g₂ * (g₁ * t₂) * t₁ := by rw [c₁₂]
      _ = (g₂ * g₁) * (t₂ * t₁) := by noncomm_ring
      _ = -(g₁ * g₂) * (t₂ * t₁) := by rw [hswap, neg_mul]
  have hForward :
      cliffordDiracForward g₁ g₂ t₁ t₂ * cliffordDiracFlipped g₁ g₂ t₁ t₂ =
        hyperbolicWaveOperator t₁ t₂ - cliffordJordanStrain g₁ g₂ t₁ t₂ := by
    change (g₁ * t₁ + g₂ * t₂) * (g₁ * t₁ - g₂ * t₂) = _
    calc
      _ = (g₁ * t₁) * (g₁ * t₁) - (g₂ * t₂) * (g₂ * t₂) -
          ((g₁ * t₁) * (g₂ * t₂) - (g₂ * t₂) * (g₁ * t₁)) := by noncomm_ring
      _ = t₁ * t₁ - t₂ * t₂ -
          ((g₁ * g₂) * (t₁ * t₂) - -(g₁ * g₂) * (t₂ * t₁)) := by
            rw [hs₁, hs₂, hcross₁₂, hcross₂₁]
      _ = hyperbolicWaveOperator t₁ t₂ - cliffordJordanStrain g₁ g₂ t₁ t₂ := by
        simp only [hyperbolicWaveOperator, cliffordJordanStrain, neg_mul]
        noncomm_ring
  have hBackward :
      cliffordDiracFlipped g₁ g₂ t₁ t₂ * cliffordDiracForward g₁ g₂ t₁ t₂ =
        hyperbolicWaveOperator t₁ t₂ + cliffordJordanStrain g₁ g₂ t₁ t₂ := by
    change (g₁ * t₁ - g₂ * t₂) * (g₁ * t₁ + g₂ * t₂) = _
    calc
      _ = (g₁ * t₁) * (g₁ * t₁) - (g₂ * t₂) * (g₂ * t₂) +
          ((g₁ * t₁) * (g₂ * t₂) - (g₂ * t₂) * (g₁ * t₁)) := by noncomm_ring
      _ = t₁ * t₁ - t₂ * t₂ +
          ((g₁ * g₂) * (t₁ * t₂) - -(g₁ * g₂) * (t₂ * t₁)) := by
            rw [hs₁, hs₂, hcross₁₂, hcross₂₁]
      _ = hyperbolicWaveOperator t₁ t₂ + cliffordJordanStrain g₁ g₂ t₁ t₂ := by
        simp only [hyperbolicWaveOperator, cliffordJordanStrain, neg_mul]
        noncomm_ring
  refine ⟨hForward, hBackward, ?_, ?_⟩
  · rw [hForward, hBackward]
    simp only [two_nsmul]
    noncomm_ring
  · rw [hForward, hBackward]
    simp only [two_nsmul]
    noncomm_ring

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

namespace InfoGeometry.OperatorAlgebra.NoncommutativeLichnerowiczCommutant

variable {A : Type*} [Ring A]

/-- Ordered commutator of two operators. -/
def commutator (x y : A) : A := x * y - y * x

/-- Two-direction operator Dirac element. -/
def diracForward (g1 g2 d1 d2 : A) : A := g1 * d1 + g2 * d2

/-- Algebraic Bochner sum of squares. -/
def bochnerLaplacian (d1 d2 : A) : A := d1 * d1 + d2 * d2

/-- Clifford bivector coefficient. -/
def spinBivector (g1 g2 : A) : A := g1 * g2

/-- The quaternion-flipped two-direction Dirac element. -/
def diracFlipped (g1 g2 d1 d2 : A) : A := g1 * d1 - g2 * d2

/-- Hyperbolic difference of squares for two operator directions. -/
def hyperbolicLaplacian (d1 d2 : A) : A := d1 * d1 - d2 * d2

/-- Symmetric operator product used in the Clifford cross term. -/
def anticommutator (x y : A) : A := x * y + y * x

/-- The Lichnerowicz cross-product formula for a Clifford pair and two
directions commuting with both Clifford generators. It holds in every
associative ring and keeps the derivative products in their actual order. -/
theorem hyperbolic_lichnerowicz_cross_products
    {g1 g2 d1 d2 : A}
    (hg1 : g1 * g1 = 1) (hg2 : g2 * g2 = 1)
    (hClifford : g1 * g2 = -(g2 * g1))
    (h11 : g1 * d1 = d1 * g1) (h12 : g1 * d2 = d2 * g1)
    (h21 : g2 * d1 = d1 * g2) (h22 : g2 * d2 = d2 * g2) :
    diracForward g1 g2 d1 d2 * diracFlipped g1 g2 d1 d2 =
        hyperbolicLaplacian d1 d2 - spinBivector g1 g2 * anticommutator d1 d2 ∧
    diracFlipped g1 g2 d1 d2 * diracForward g1 g2 d1 d2 =
        hyperbolicLaplacian d1 d2 + spinBivector g1 g2 * anticommutator d1 d2 ∧
    anticommutator (diracForward g1 g2 d1 d2) (diracFlipped g1 g2 d1 d2) =
        (2 : ℕ) • hyperbolicLaplacian d1 d2 ∧
    commutator (diracForward g1 g2 d1 d2) (diracFlipped g1 g2 d1 d2) =
        -((2 : ℕ) • (spinBivector g1 g2 * anticommutator d1 d2)) := by
  have h11sq : (g1 * d1) * (g1 * d1) = d1 * d1 := by
    calc
      (g1 * d1) * (g1 * d1) = g1 * (d1 * g1) * d1 := by noncomm_ring
      _ = g1 * (g1 * d1) * d1 := by rw [h11]
      _ = (g1 * g1) * (d1 * d1) := by noncomm_ring
      _ = d1 * d1 := by rw [hg1]; simp
  have h22sq : (g2 * d2) * (g2 * d2) = d2 * d2 := by
    calc
      (g2 * d2) * (g2 * d2) = g2 * (d2 * g2) * d2 := by noncomm_ring
      _ = g2 * (g2 * d2) * d2 := by rw [h22]
      _ = (g2 * g2) * (d2 * d2) := by noncomm_ring
      _ = d2 * d2 := by rw [hg2]; simp
  have hcross : (g1 * d1) * (g2 * d2) =
      (g1 * g2) * (d1 * d2) := by
    calc
      (g1 * d1) * (g2 * d2) = g1 * (d1 * g2) * d2 := by noncomm_ring
      _ = g1 * (g2 * d1) * d2 := by rw [h21]
      _ = (g1 * g2) * (d1 * d2) := by noncomm_ring
  have hAnti : g2 * g1 = -(g1 * g2) := by
    have h := congrArg Neg.neg hClifford.symm
    simpa using h
  have hcross' : (g2 * d2) * (g1 * d1) =
      -(g1 * g2) * (d2 * d1) := by
    calc
      (g2 * d2) * (g1 * d1) = g2 * (d2 * g1) * d1 := by noncomm_ring
      _ = g2 * (g1 * d2) * d1 := by rw [h12]
      _ = (g2 * g1) * (d2 * d1) := by noncomm_ring
      _ = -(g1 * g2) * (d2 * d1) := by rw [hAnti]
  have hforward :
      diracForward g1 g2 d1 d2 * diracFlipped g1 g2 d1 d2 =
        hyperbolicLaplacian d1 d2 -
          spinBivector g1 g2 * anticommutator d1 d2 := by
    unfold diracForward diracFlipped hyperbolicLaplacian spinBivector anticommutator
    noncomm_ring [h11sq, h22sq, hcross, hcross']
  have hbackward :
      diracFlipped g1 g2 d1 d2 * diracForward g1 g2 d1 d2 =
        hyperbolicLaplacian d1 d2 +
          spinBivector g1 g2 * anticommutator d1 d2 := by
    unfold diracForward diracFlipped hyperbolicLaplacian spinBivector anticommutator
    noncomm_ring [h11sq, h22sq, hcross, hcross']
  refine ⟨hforward, hbackward, ?_, ?_⟩
  · unfold anticommutator
    rw [hforward, hbackward]
    simp only [two_nsmul]
    abel
  · unfold commutator
    rw [hforward, hbackward]
    simp only [two_nsmul]
    abel

/-- An operator in the joint commutant of the Clifford and derivative
generators. -/
structure InDiracCommutant (C g1 g2 d1 d2 : A) : Prop where
  comm_g1 : commutator C g1 = 0
  comm_g2 : commutator C g2 = 0
  comm_d1 : commutator C d1 = 0
  comm_d2 : commutator C d2 = 0

private theorem commutator_mul {C X Y : A}
    (hX : commutator C X = 0) (hY : commutator C Y = 0) :
    commutator C (X * Y) = 0 := by
  have hCX : C * X = X * C := sub_eq_zero.mp hX
  have hCY : C * Y = Y * C := sub_eq_zero.mp hY
  have h : C * (X * Y) = (X * Y) * C := by
    calc
      C * (X * Y) = (C * X) * Y := by rw [← mul_assoc]
      _ = (X * C) * Y := by rw [hCX]
      _ = X * (C * Y) := by rw [mul_assoc]
      _ = X * (Y * C) := by rw [hCY]
      _ = (X * Y) * C := by rw [mul_assoc]
  unfold commutator
  rw [h, sub_self]

private theorem commutator_add {C X Y : A}
    (hX : commutator C X = 0) (hY : commutator C Y = 0) :
    commutator C (X + Y) = 0 := by
  have hCX : C * X = X * C := sub_eq_zero.mp hX
  have hCY : C * Y = Y * C := sub_eq_zero.mp hY
  unfold commutator
  rw [mul_add, add_mul, hCX, hCY]
  abel

private theorem commutator_sub {C X Y : A}
    (hX : commutator C X = 0) (hY : commutator C Y = 0) :
    commutator C (X - Y) = 0 := by
  have hCX : C * X = X * C := sub_eq_zero.mp hX
  have hCY : C * Y = Y * C := sub_eq_zero.mp hY
  unfold commutator
  rw [mul_sub, sub_mul, hCX, hCY]
  abel

/-- Joint commutation with the Dirac and derivative generators propagates to
the Dirac element, the Bochner sum, the curvature, and the spin-curvature
product in any associative operator ring. -/
theorem commutant_preserves_lichnerowicz_terms
    {C g1 g2 d1 d2 : A}
    (h : InDiracCommutant C g1 g2 d1 d2) :
    commutator C (diracForward g1 g2 d1 d2) = 0 ∧
    commutator C (bochnerLaplacian d1 d2) = 0 ∧
    commutator C (spinBivector g1 g2) = 0 ∧
    commutator C
      (spinBivector g1 g2 * commutator d1 d2) = 0 := by
  have hD : commutator C (diracForward g1 g2 d1 d2) = 0 := by
    unfold diracForward
    exact commutator_add (commutator_mul h.comm_g1 h.comm_d1)
      (commutator_mul h.comm_g2 h.comm_d2)
  have hΔ : commutator C (bochnerLaplacian d1 d2) = 0 := by
    unfold bochnerLaplacian
    exact commutator_add (commutator_mul h.comm_d1 h.comm_d1)
      (commutator_mul h.comm_d2 h.comm_d2)
  have hS : commutator C (spinBivector g1 g2) = 0 := by
    unfold spinBivector
    exact commutator_mul h.comm_g1 h.comm_g2
  have hF : commutator C (commutator d1 d2) = 0 := by
    unfold commutator
    exact commutator_sub (commutator_mul h.comm_d1 h.comm_d2)
      (commutator_mul h.comm_d2 h.comm_d1)
  exact ⟨hD, hΔ, hS, commutator_mul hS hF⟩

end InfoGeometry.OperatorAlgebra.NoncommutativeLichnerowiczCommutant
