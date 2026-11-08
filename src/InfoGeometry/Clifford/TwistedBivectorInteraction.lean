import Mathlib
import InfoGeometry.Algebra.FiniteSpinAlgebra

/-!
# Central-sign interaction lemmas

These are theorem-level consequences of an explicitly supplied central
involution.  They do not choose a commuting or anticommuting realization.
-/

namespace InfoGeometry.Clifford.TwistedBivectorInteraction

theorem reverse_relation {A : Type*} [Ring A]
    {B R κ : A}
    (hκsq : κ * κ = 1)
    (hBR : B * R = κ * (R * B)) :
    R * B = κ * (B * R) := by
  have h : κ * (B * R) = R * B := by
    calc
      κ * (B * R) = κ * (κ * (R * B)) := by rw [hBR]
      _ = (κ * κ) * (R * B) := by rw [mul_assoc]
      _ = R * B := by rw [hκsq, one_mul]
  exact h.symm

theorem mixed_product_square {A : Type*} [Ring A]
    {B R κ : A}
    (hκc : ∀ x : A, κ * x = x * κ)
    (hκsq : κ * κ = 1)
    (hBR : B * R = κ * (R * B)) :
    (B * R) * (B * R) = κ * ((B * B) * (R * R)) := by
  have hRB : R * B = κ * (B * R) :=
    reverse_relation hκsq hBR
  calc
    (B * R) * (B * R) = B * (R * B) * R := by noncomm_ring
    _ = B * (κ * (B * R)) * R := by rw [hRB]
    _ = (B * κ) * B * R * R := by noncomm_ring
    _ = (κ * B) * B * R * R := by rw [hκc B]
    _ = κ * ((B * B) * (R * R)) := by noncomm_ring

theorem commutator_formula {A : Type*} [Ring A]
    {B R κ : A}
    (hBR : B * R = κ * (R * B)) :
    B * R - R * B = (κ - 1) * (R * B) := by
  rw [hBR]
  noncomm_ring

theorem anticommutator_formula {A : Type*} [Ring A]
    {B R κ : A}
    (hBR : B * R = κ * (R * B)) :
    B * R + R * B = (κ + 1) * (R * B) := by
  rw [hBR]
  noncomm_ring

theorem commuting_reduction {A : Type*} [Ring A]
    {B R κ : A} (hκ : κ = 1)
    (hBR : B * R = κ * (R * B)) :
    B * R = R * B := by
  rw [hBR, hκ, one_mul]

theorem anticommuting_reduction {A : Type*} [Ring A]
    {B R κ : A} (hκ : κ = -1)
    (hBR : B * R = κ * (R * B)) :
    B * R = -(R * B) := by
  rw [hBR, hκ, neg_mul, one_mul]

end InfoGeometry.Clifford.TwistedBivectorInteraction
