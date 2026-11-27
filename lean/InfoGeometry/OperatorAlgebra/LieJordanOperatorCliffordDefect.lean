/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.OperatorAlgebra.LieJordanDualTransport
import Mathlib.Algebra.Algebra.Bilinear
import Mathlib.Tactic.NoncommRing

/-!
# Clifford-weighted operator squares with noncommutative coefficient defects

For a pair of anticommuting involutions acting by left multiplication on an
associative algebra, the square of a weighted sum separates into operator
squares and the mixed commutator, plus the exact defects from moving each
operator past each coefficient.  No centrality assumption is imposed.
This is an algebraic identity on `Module.End`; no differential-geometric
Lichnerowicz formula is asserted.
-/

namespace InfoGeometry.OperatorAlgebra.LieJordanOperatorCliffordDefect

variable {R A : Type*} [CommRing R] [Ring A] [Algebra R A]

/-- The ring-level weighted-square identity, retaining all four coefficient
transport defects. -/
theorem square_with_coefficient_defects {E : Type*} [Ring E]
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

/-- Left coefficient multiplication followed by an operator, summed over two
channels. -/
def leftWeighted (g₁ g₂ : A) (T₁ T₂ : Module.End R A) : Module.End R A :=
  LinearMap.mulLeft R g₁ * T₁ + LinearMap.mulLeft R g₂ * T₂

@[simp] theorem leftWeighted_apply (g₁ g₂ : A) (T₁ T₂ : Module.End R A)
    (x : A) : leftWeighted g₁ g₂ T₁ T₂ x = g₁ * T₁ x + g₂ * T₂ x := rfl

/-- The square of the operator-valued weighted sum, with every failure of an
operator to commute with either coefficient retained explicitly. -/
theorem leftWeighted_square_with_coefficient_defects
    (g₁ g₂ : A) (T₁ T₂ : Module.End R A)
    (h₁ : g₁ * g₁ = 1) (h₂ : g₂ * g₂ = 1)
    (h₁₂ : g₁ * g₂ + g₂ * g₁ = 0) :
    leftWeighted g₁ g₂ T₁ T₂ * leftWeighted g₁ g₂ T₁ T₂ =
      T₁ * T₁ + T₂ * T₂ +
        LinearMap.mulLeft R g₁ * LinearMap.mulLeft R g₂ * (T₁ * T₂ - T₂ * T₁) +
        LinearMap.mulLeft R g₁ *
          (T₁ * LinearMap.mulLeft R g₁ - LinearMap.mulLeft R g₁ * T₁) * T₁ +
        LinearMap.mulLeft R g₁ *
          (T₁ * LinearMap.mulLeft R g₂ - LinearMap.mulLeft R g₂ * T₁) * T₂ +
        LinearMap.mulLeft R g₂ *
          (T₂ * LinearMap.mulLeft R g₁ - LinearMap.mulLeft R g₁ * T₂) * T₁ +
        LinearMap.mulLeft R g₂ *
          (T₂ * LinearMap.mulLeft R g₂ - LinearMap.mulLeft R g₂ * T₂) * T₂ := by
  have hs₁ : LinearMap.mulLeft R g₁ * LinearMap.mulLeft R g₁ = 1 := by
    ext x
    change g₁ * (g₁ * x) = x
    rw [← mul_assoc, h₁, one_mul]
  have hs₂ : LinearMap.mulLeft R g₂ * LinearMap.mulLeft R g₂ = 1 := by
    ext x
    change g₂ * (g₂ * x) = x
    rw [← mul_assoc, h₂, one_mul]
  have hs₁₂ : LinearMap.mulLeft R g₁ * LinearMap.mulLeft R g₂ +
      LinearMap.mulLeft R g₂ * LinearMap.mulLeft R g₁ = 0 := by
    ext x
    change g₁ * (g₂ * x) + g₂ * (g₁ * x) = 0
    rw [← mul_assoc, ← mul_assoc, ← add_mul, h₁₂, zero_mul]
  exact square_with_coefficient_defects
    (LinearMap.mulLeft R g₁) (LinearMap.mulLeft R g₂) T₁ T₂ hs₁ hs₂ hs₁₂

end InfoGeometry.OperatorAlgebra.LieJordanOperatorCliffordDefect
