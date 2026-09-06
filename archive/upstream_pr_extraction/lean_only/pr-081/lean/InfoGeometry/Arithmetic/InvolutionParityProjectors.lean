import Mathlib.Tactic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-!
# Algebraic parity projectors for an involution

This file contains the algebraic core of an even/odd decomposition.  It does
not assume an analytic function, a Fourier transform, or a zeta functional
equation.  Those are separate hypotheses that may use this interface.
-/

namespace InfoGeometry.Arithmetic

open scoped Interval

noncomputable section

variable {α R : Type*} [CommRing R]

def evenPart
    (J : α → α) (half : R) (F : α → R) (x : α) : R :=
  half * (F x + F (J x))

def oddPart
    (J : α → α) (half : R) (F : α → R) (x : α) : R :=
  half * (F x - F (J x))

theorem evenPart_invariant
    (J : α → α) (hJ : Function.Involutive J)
    (half : R) (F : α → R) (x : α) :
    evenPart J half F (J x) = evenPart J half F x := by
  simp [evenPart, hJ x]
  ring

theorem oddPart_antiinvariant
    (J : α → α) (hJ : Function.Involutive J)
    (half : R) (F : α → R) (x : α) :
    oddPart J half F (J x) = -oddPart J half F x := by
  simp only [oddPart, hJ x]
  ring

theorem evenPart_add_oddPart
    (J : α → α) (half : R) (hhalf : (2 : R) * half = 1)
    (F : α → R) (x : α) :
    evenPart J half F x + oddPart J half F x = F x := by
  dsimp [evenPart, oddPart]
  calc
    half * (F x + F (J x)) + half * (F x - F (J x)) =
        ((2 : R) * half) * F x := by ring
    _ = F x := by rw [hhalf, one_mul]

theorem evenPart_eq_self_of_invariant
    (J : α → α)
    (half : R) (hhalf : (2 : R) * half = 1)
    (F : α → R) (hInv : ∀ x, F (J x) = F x) :
    evenPart J half F = F := by
  funext x
  dsimp [evenPart]
  rw [hInv x]
  calc
    half * (F x + F x) = ((2 : R) * half) * F x := by ring
    _ = F x := by rw [hhalf, one_mul]

theorem oddPart_eq_zero_of_invariant
    (J : α → α) (half : R) (F : α → R)
    (hInv : ∀ x, F (J x) = F x) :
    oddPart J half F = 0 := by
  funext x
  dsimp [oddPart]
  rw [hInv x, sub_self, mul_zero]

theorem evenPart_eq_zero_of_antiinvariant
    (J : α → α) (half : R) (F : α → R)
    (hAnti : ∀ x, F (J x) = -F x) :
    evenPart J half F = 0 := by
  funext x
  dsimp [evenPart]
  rw [hAnti x, add_neg_cancel, mul_zero]

theorem oddPart_eq_self_of_antiinvariant
    (J : α → α)
    (half : R) (hhalf : (2 : R) * half = 1)
    (F : α → R) (hAnti : ∀ x, F (J x) = -F x) :
    oddPart J half F = F := by
  funext x
  dsimp [oddPart]
  rw [hAnti x, sub_neg_eq_add]
  calc
    half * (F x + F x) = ((2 : R) * half) * F x := by ring
    _ = F x := by rw [hhalf, one_mul]

theorem evenPart_idempotent
    (J : α → α) (hJ : Function.Involutive J)
    (half : R) (hhalf : (2 : R) * half = 1)
    (F : α → R) :
    evenPart J half (evenPart J half F) = evenPart J half F := by
  apply evenPart_eq_self_of_invariant J half hhalf (evenPart J half F)
  intro x
  exact evenPart_invariant J hJ half F x

theorem oddPart_idempotent
    (J : α → α) (hJ : Function.Involutive J)
    (half : R) (hhalf : (2 : R) * half = 1)
    (F : α → R) :
    oddPart J half (oddPart J half F) = oddPart J half F := by
  apply oddPart_eq_self_of_antiinvariant J half hhalf (oddPart J half F)
  intro x
  exact oddPart_antiinvariant J hJ half F x

theorem oddPart_evenPart_zero
    (J : α → α) (hJ : Function.Involutive J)
    (half : R) (F : α → R) :
    oddPart J half (evenPart J half F) = 0 := by
  apply oddPart_eq_zero_of_invariant J half (evenPart J half F)
  intro x
  exact evenPart_invariant J hJ half F x

theorem evenPart_oddPart_zero
    (J : α → α) (hJ : Function.Involutive J)
    (half : R) (F : α → R) :
    evenPart J half (oddPart J half F) = 0 := by
  apply evenPart_eq_zero_of_antiinvariant J half (oddPart J half F)
  intro x
  exact oddPart_antiinvariant J hJ half F x

/-! ## The centered primitive for the reflection `β ↦ 2 - β`

The following is the analytic part of the parity interface.  It assumes only
continuity and reflection invariance of the integrand; no zeta function or
Fourier representation is built into these statements.
-/

def reflection (β : ℝ) : ℝ := 2 - β

@[simp] theorem reflection_involutive : Function.Involutive reflection := by
  intro β
  dsimp [reflection]
  ring

def centeredPrimitive (X : ℝ → ℝ) (β : ℝ) : ℝ :=
  ∫ b in (1 : ℝ)..β, X b

theorem centeredPrimitive_zero (X : ℝ → ℝ) : centeredPrimitive X 1 = 0 := by
  simp [centeredPrimitive]

theorem centeredPrimitive_reflection
    {X : ℝ → ℝ}
    (hX : ∀ β, X (reflection β) = X β)
    (β : ℝ) :
    centeredPrimitive X (reflection β) = -centeredPrimitive X β := by
  rw [centeredPrimitive]
  calc
    (∫ b in (1 : ℝ)..reflection β, X b) =
        ∫ b in β..(1 : ℝ), X (reflection b) := by
      have h := (intervalIntegral.integral_comp_sub_left (f := X)
        (a := β) (b := (1 : ℝ)) (2 : ℝ)).symm
      convert h using 1
      norm_num [reflection]
    _ = ∫ b in β..(1 : ℝ), X b := by
      apply intervalIntegral.integral_congr
      intro b hb
      change X (reflection b) = X b
      exact hX b
    _ = -∫ b in (1 : ℝ)..β, X b := by
      rw [intervalIntegral.integral_symm]

theorem centeredPrimitive_reflection_endpoints
    {X : ℝ → ℝ}
    (hX : ∀ β, X (reflection β) = X β) :
    centeredPrimitive X 0 = -centeredPrimitive X 2 := by
  have h := centeredPrimitive_reflection hX (0 : ℝ)
  norm_num [reflection] at h
  linarith

theorem centeredPrimitive_fixed_center
    {X : ℝ → ℝ}
    (_hX : ∀ β, X (reflection β) = X β) :
    centeredPrimitive X 1 = 0 := by
  exact centeredPrimitive_zero X

theorem centeredPrimitive_odd
    {X : ℝ → ℝ}
    (hX : ∀ β, X (reflection β) = X β) :
    oddPart reflection (1 / 2 : ℝ) (centeredPrimitive X) =
      centeredPrimitive X := by
  apply oddPart_eq_self_of_antiinvariant reflection (1 / 2 : ℝ)
    (by norm_num)
  intro β
  exact centeredPrimitive_reflection hX β

theorem centeredPrimitive_hasDerivAt
    {X : ℝ → ℝ}
    (hX : Continuous X) (β : ℝ) :
    HasDerivAt (centeredPrimitive X) (X β) β := by
  simpa [centeredPrimitive] using
    (intervalIntegral.integral_hasDerivAt_right
      (hX.intervalIntegrable (1 : ℝ) β)
      hX.aestronglyMeasurable.stronglyMeasurableAtFilter
      hX.continuousAt)

end

end InfoGeometry.Arithmetic
