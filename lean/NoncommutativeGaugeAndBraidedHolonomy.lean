/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.OperatorAlgebra.NonabelianSylvesterHolonomy
import Mathlib.Tactic

/-!
# Wilson cocycle in a concrete noncommutative operator unit group

The finite operators and their ordered braiding are owned by
`InfoGeometry.OperatorAlgebra.NonabelianSylvesterHolonomy`. This module reuses
that owner and adds the unit-group lift and general crossed-cocycle results.
The finite witness is specifically in `M₂(M₂(ℤ))`; it is not promoted to a
classification over arbitrary rings.
-/

namespace NoncommutativeGaugeAndBraidedHolonomy

open InfoGeometry.OperatorAlgebra.NonabelianSylvesterHolonomy

abbrev BlockOp := InfoGeometry.OperatorAlgebra.NonabelianSylvesterHolonomy.BlockOp

/-- The finite shift as a unit in the owner module's nested matrix ring. -/
def shiftUnit : BlockOpˣ :=
  ⟨shift, shift, by simpa using shift_sq, by simpa using shift_sq⟩

/-- The vertex clock as a unit in the same operator ring. -/
def vertexClockUnit : BlockOpˣ :=
  ⟨vertexClock, vertexClock, by simpa using vertexClock_sq,
    by simpa using vertexClock_sq⟩

def plaquetteUnit : BlockOpˣ := (vertexClockUnit * shiftUnit) ^ 2

theorem plaquetteUnit_val : (plaquetteUnit : BlockOp) = plaquette := by
  change ((vertexClock * shift : BlockOp) ^ 2) = plaquette
  simp [pow_two, plaquette]

theorem shiftUnit_sq : shiftUnit ^ 2 = 1 := by
  apply Units.ext
  simp [shiftUnit, pow_two, shift_sq]

theorem vertexClockUnit_sq : vertexClockUnit ^ 2 = 1 := by
  apply Units.ext
  simp [vertexClockUnit, pow_two, vertexClock_sq]

/-- The canonical finite block braiding relation holds in the operator unit
group, retaining the full operator-valued plaquette as the phase. -/
theorem operatorUnit_braiding :
    vertexClockUnit * shiftUnit = plaquetteUnit * shiftUnit * vertexClockUnit := by
  apply Units.ext
  simp only [Units.val_mul]
  rw [plaquetteUnit_val]
  exact block_braiding

/-- The phase is not an involution: its second power is detected by the
parabolic block's infinite-order theorem. -/
theorem plaquetteUnit_sq_ne_one : plaquetteUnit ^ 2 ≠ 1 := by
  intro h
  have h₂ : (plaquetteUnit : BlockOp) ^ 2 = plaquette ^ 2 := by
    calc
      (plaquetteUnit : BlockOp) ^ 2 = (plaquetteUnit : BlockOp) * (plaquetteUnit : BlockOp) := by
        simp [pow_two]
      _ = plaquette ^ 2 := by rw [plaquetteUnit_val]; simp [pow_two]
  have hv := congrArg (fun u : BlockOpˣ => (u : BlockOp)) h
  have h₃ : (plaquetteUnit : BlockOp) ^ 2 = 1 := by simpa using hv
  have h₄ : plaquette ^ 2 = 1 := by
    calc
      plaquette ^ 2 = (plaquetteUnit : BlockOp) ^ 2 := by rw [h₂]
      _ = 1 := h₃
  have h₅ := plaquette_infinite_order 2 (by norm_num)
  exact h₅ h₄

section WilsonCocycle

variable {G : Type*} [Group G]

/-- Conjugation action used in the non-Abelian path-ordered cocycle. -/
def conjugateBy (x q : G) : G := x * q * x⁻¹

/-- The ordered Wilson cocycle for repeatedly moving a phase across a shift. -/
def wilsonCocycle (x q : G) : ℕ → G
  | 0 => 1
  | n + 1 => q * conjugateBy x (wilsonCocycle x q n)

/-- Repeated braiding accumulates the conjugated phase rather than the
ordinary power `q ^ n`. -/
theorem braided_pow_law {x z q : G}
    (h : z * x = q * x * z) (n : ℕ) :
    z * x ^ n = wilsonCocycle x q n * x ^ n * z := by
  induction n with
  | zero => simp [wilsonCocycle]
  | succ n ih =>
      calc
        z * x ^ (n + 1) = (z * x) * x ^ n := by rw [pow_succ']; group
        _ = (q * x * z) * x ^ n := by rw [h]
        _ = q * x * (z * x ^ n) := by group
        _ = q * x * (wilsonCocycle x q n * x ^ n * z) := by rw [ih]
        _ = (q * (x * wilsonCocycle x q n * x⁻¹)) * x ^ (n + 1) * z := by
          rw [pow_succ']
          group
        _ = wilsonCocycle x q (n + 1) * x ^ (n + 1) * z := by
          rw [wilsonCocycle, conjugateBy]

/-- The path-ordered phase obeys the non-Abelian crossed-homomorphism law. -/
theorem wilsonCocycle_add (x q : G) (m n : ℕ) :
    wilsonCocycle x q (m + n) =
      wilsonCocycle x q m * conjugateBy (x ^ m) (wilsonCocycle x q n) := by
  induction m with
  | zero => simp [wilsonCocycle, conjugateBy]
  | succ m ih =>
      have hmn : m + 1 + n = (m + n) + 1 := by omega
      rw [hmn, wilsonCocycle, ih, wilsonCocycle]
      have hmul (a b : G) : conjugateBy x (a * b) =
          conjugateBy x a * conjugateBy x b := by
        dsimp [conjugateBy]
        group
      rw [hmul]
      have hcomp :
          conjugateBy x (conjugateBy (x ^ m) (wilsonCocycle x q n)) =
            conjugateBy (x ^ (m + 1)) (wilsonCocycle x q n) := by
        dsimp [conjugateBy]
        rw [pow_succ']
        group
      rw [hcomp, mul_assoc]

/-- If the shift is periodic, the accumulated Wilson cocycle closes at the
same period. -/
theorem wilsonCocycle_eq_one_of_pow_eq_one {x z q : G}
    (h : z * x = q * x * z) {n : ℕ} (hn : x ^ n = 1) :
    wilsonCocycle x q n = 1 := by
  have hpow := braided_pow_law h n
  rw [hn, mul_one, mul_one] at hpow
  calc
    wilsonCocycle x q n = (wilsonCocycle x q n * z) * z⁻¹ := by group
    _ = z * z⁻¹ := by rw [← hpow]
    _ = 1 := mul_inv_cancel z

/-- For an involutive shift, two-step cocycle closure forces conjugation of
the phase to invert it. -/
theorem wilsonCocycle_two_step_inversion {x q : G}
    (hx : x ^ 2 = 1) (hclose : wilsonCocycle x q 2 = 1) :
    x * q * x = q⁻¹ := by
  have hxx : x * x = 1 := by simpa [pow_two] using hx
  have hxi : x⁻¹ = x := by
    calc
      x⁻¹ = x⁻¹ * 1 := by group
      _ = x⁻¹ * (x * x) := by rw [hxx]
      _ = x := by group
  have h₁ : wilsonCocycle x q 2 = q * x * q * x := by
    simp [wilsonCocycle, conjugateBy, hxi, hxx]
    group
  rw [h₁] at hclose
  have h₂ : q * x * q * x = 1 := by simpa using hclose
  have h₃ : x * q * x = q⁻¹ := by
    calc
      x * q * x = (q⁻¹ * q) * (x * q * x) := by group
      _ = q⁻¹ * (q * (x * q * x)) := by group
      _ = q⁻¹ * 1 := by
        have h₄ : q * (x * q * x) = 1 := by
          calc
            q * (x * q * x) = q * x * q * x := by group
            _ = 1 := by simpa using h₂
        rw [h₄]
      _ = q⁻¹ := by group
  exact h₃

end WilsonCocycle

/-- In the unit group of `M₂(M₂(ℤ))`, the two-step Wilson cocycle closes,
even though its plaquette phase itself is not an involution. -/
theorem operatorUnit_wilson_closure :
    wilsonCocycle shiftUnit plaquetteUnit 2 = 1 :=
  wilsonCocycle_eq_one_of_pow_eq_one operatorUnit_braiding shiftUnit_sq

/-- The nested shift conjugates the full noncommutative operator phase to its
inverse, which is the order-two crossed-cocycle relation. -/
theorem operatorUnit_phase_inversion :
    shiftUnit * plaquetteUnit * shiftUnit = plaquetteUnit⁻¹ :=
  wilsonCocycle_two_step_inversion shiftUnit_sq operatorUnit_wilson_closure

end NoncommutativeGaugeAndBraidedHolonomy
