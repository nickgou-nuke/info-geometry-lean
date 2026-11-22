/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Physics.NoncommutativeZornBdGDerivations

/-!
# Exact zero criterion for the noncommutative Zorn pairing action

The pairing action on `diag(D, -D)` is controlled by left multiplication by
`D + D`. Nonzero mass and nonzero pairing data do not, by themselves, imply a
nonzero output: matrix operator rings have nonzero zero divisors. This module
states the exact coordinate criterion and gives a witness in the full matrix
operator ring `M₂(ℤ)`.
-/

namespace InfoGeometry.Physics.BdGPairingZeroDivisorCounterexample

open InfoGeometry.Physics.NoncommutativeZornBdGDerivations

variable {A : Type*} [Ring A]

/-- The Dirac-seed pairing action vanishes precisely when every ordered
coefficient product in its two triplet channels vanishes. No cancellation,
commutativity, or absence-of-zero-divisors hypothesis is assumed. -/
theorem pairingDerivationAction_dirac_seed_eq_zero_iff
    (w₁ w₂ : Fin 3 → A) (D : A) :
    pairingDerivationAction w₁ w₂ D (-D) = ncZornZero ↔
      (∀ i, (D + D) * w₁ i = 0) ∧
      (∀ i, (D + D) * w₂ i = 0) := by
  constructor
  · intro h
    have hu := congrArg NCZorn.u h
    have hv := congrArg NCZorn.v h
    constructor
    · intro i
      simpa [pairingDerivationAction, ncZornZero, sub_neg_eq_add] using
        congrFun hu i
    · intro i
      have hi := congrFun hv i
      change (-D - D) * w₂ i = 0 at hi
      rw [sub_eq_add_neg] at hi
      have hsum : -D + -D = -(D + D) := (neg_add D D).symm
      rw [hsum] at hi
      rw [neg_mul] at hi
      exact neg_eq_zero.mp hi
  · rintro ⟨hu, hv⟩
    apply NCZorn.ext
    · rfl
    · funext i
      simp [pairingDerivationAction, ncZornZero, sub_neg_eq_add, hu i]
    · funext i
      change (-D - D) * w₂ i = 0
      rw [sub_eq_add_neg]
      have hsum : -D + -D = -(D + D) := (neg_add D D).symm
      rw [hsum, neg_mul, hv i, neg_zero]
    · rfl

section MatrixWitness

local notation "M₂" => Matrix (Fin 2) (Fin 2) ℤ

/-- A nonzero matrix operator supported on the first diagonal coordinate. -/
def mass00 : M₂ := ![![1, 0], ![0, 0]]

/-- A nonzero matrix operator supported in the lower-left coordinate. -/
def pair10 : M₂ := ![![0, 0], ![1, 0]]

theorem mass00_ne_zero : mass00 ≠ 0 := by
  intro h
  have h00 := congrFun (congrFun h 0) 0
  norm_num [mass00] at h00

theorem pair10_ne_zero : pair10 ≠ 0 := by
  intro h
  have h10 := congrFun (congrFun h 1) 0
  norm_num [pair10] at h10

/-- A nonzero operator mass and nonzero operator-valued channel can still
produce zero pairing: the mass is a left zero divisor on that channel. -/
theorem nonzero_mass_nonzero_channel_zero_pairing :
    mass00 ≠ 0 ∧ pair10 ≠ 0 ∧
      (mass00 + mass00) * pair10 = 0 := by
  refine ⟨mass00_ne_zero, pair10_ne_zero, ?_⟩
  have hsum : mass00 + mass00 = ![![2, 0], ![0, 0]] := by
    ext i j
    change mass00 i j + mass00 i j = (![![2, 0], ![0, 0]] : M₂) i j
    fin_cases i <;> fin_cases j <;> norm_num [mass00]
  rw [hsum]
  ext i j
  change (∑ k : Fin 2,
      (![![2, 0], ![0, 0]] : M₂) i k * (![![0, 0], ![1, 0]] : M₂) k j) = 0
  fin_cases i <;> fin_cases j <;> norm_num

/-- The corresponding full Zorn pairing action vanishes although both the
Dirac coefficient and one triplet channel are nonzero matrices. -/
theorem nonzero_operator_inputs_can_give_zero_pairing :
    pairingDerivationAction
        (fun i : Fin 3 => if i = 0 then pair10 else 0)
        (fun _ : Fin 3 => 0) mass00 (-mass00) = ncZornZero := by
  apply NCZorn.ext
  · rfl
  · funext i
    fin_cases i
    · have hp := nonzero_mass_nonzero_channel_zero_pairing.2.2
      change (mass00 - -mass00) * pair10 = 0
      rw [sub_neg_eq_add]
      exact hp
    · simp [pairingDerivationAction, ncZornZero]
    · simp [pairingDerivationAction, ncZornZero]
  · funext i
    simp [pairingDerivationAction, ncZornZero]
  · rfl

end MatrixWitness

end InfoGeometry.Physics.BdGPairingZeroDivisorCounterexample
