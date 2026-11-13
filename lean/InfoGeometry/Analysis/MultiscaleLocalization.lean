/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Analysis.PorosityIteration
import Mathlib.Analysis.Normed.Ring.Basic
import Mathlib.Algebra.Order.BigOperators.Group.List

/-!
# Conditional multiscale localization estimates

A one-step energy estimate is an explicit hypothesis. The porosity recurrence
gives a uniform retained fraction, and induction multiplies those losses.
For operators, a native ordered list product retains the multiplication order
and needs actual norm bounds on every factor. No sampling or Fock-space
estimate is inferred from finite algebra or from porosity arithmetic alone.
-/

namespace InfoGeometry.Analysis.MultiscaleLocalization

open PorosityIteration

/-- Iterating a nonnegative one-step factor gives an explicit terminal-energy
bound. The energies need not be nonnegative for this elementary implication. -/
theorem energy_le_pow_mul (E : ℕ → ℝ) {t : ℝ} (ht : 0 ≤ t)
    (n : ℕ) (hstep : ∀ j < n, E j ≤ t * E (j + 1)) :
    E 0 ≤ t ^ n * E n := by
  revert hstep
  induction n with
  | zero => intro _; simp
  | succ n ih =>
    intro hstep
    calc
      E 0 ≤ t ^ n * E n := ih (fun j hj => hstep j (Nat.lt_succ_of_lt hj))
      _ ≤ t ^ n * (t * E (n + 1)) :=
        mul_le_mul_of_nonneg_left (hstep n (Nat.lt_succ_self n)) (pow_nonneg ht n)
      _ = t ^ (n + 1) * E (n + 1) := by rw [pow_succ]; ring

/-- A porosity-dependent one-step estimate gives the uniform geometric
factor `K * (1 - (ν/2)^(2*d))`. A strict contraction still requires that
factor to be less than one. -/
theorem energy_le_uniform_porosity (E : ℕ → ℝ) {ν K : ℝ} {d : ℕ}
    (hν0 : 0 < ν) (hν1 : ν ≤ 1) (hd : 0 < d) (hK : 0 ≤ K)
    (n : ℕ) (hE : ∀ j ≤ n, 0 ≤ E j)
    (hstep : ∀ j < n, E j ≤ K * (1 - remainingPorosity ν j ^ (2 * d)) * E (j + 1)) :
    E 0 ≤ (K * (1 - (ν / 2) ^ (2 * d))) ^ n * E n := by
  have hq := uniformRetainedFraction_mem_Ioo hν0 hν1 hd
  apply energy_le_pow_mul E (mul_nonneg hK hq.1.le) n
  intro j hj
  exact (hstep j hj).trans
    (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left (retainedFraction_le hν0.le hν1 j (2 * d)) hK)
      (hE (j + 1) (Nat.succ_le_of_lt hj)))

/-- A terminal-energy upper bound closes the conditional multiscale estimate. -/
theorem energy_le_uniform_porosity_of_terminal_bound (E : ℕ → ℝ)
    {ν K M : ℝ} {d n : ℕ}
    (hν0 : 0 < ν) (hν1 : ν ≤ 1) (hd : 0 < d) (hK : 0 ≤ K)
    (hE : ∀ j ≤ n, 0 ≤ E j)
    (hstep : ∀ j < n, E j ≤ K * (1 - remainingPorosity ν j ^ (2 * d)) * E (j + 1))
    (hterminal : E n ≤ M) :
    E 0 ≤ (K * (1 - (ν / 2) ^ (2 * d))) ^ n * M := by
  have hq := uniformRetainedFraction_mem_Ioo hν0 hν1 hd
  exact (energy_le_uniform_porosity E hν0 hν1 hd hK n hE hstep).trans
    (mul_le_mul_of_nonneg_left hterminal (pow_nonneg (mul_nonneg hK hq.1.le) n))

/-- Native noncommutative products obey a uniform norm bound. `NormOneClass`
handles the empty product; the ring multiplication need not commute. -/
theorem norm_orderedProduct_le {A : Type*} [NormedRing A] [NormOneClass A]
    (operators : List A) {ρ : ℝ} (hρ : 0 ≤ ρ)
    (h : ∀ T ∈ operators, ‖T‖ ≤ ρ) :
    ‖operators.prod‖ ≤ ρ ^ operators.length := by
  let bound : NNReal := ⟨ρ, hρ⟩
  have hnn : (operators.map nnnorm).prod ≤ bound ^ (operators.map nnnorm).length := by
    apply List.prod_le_pow_length
    intro r hr
    obtain ⟨T, hT, rfl⟩ := List.mem_map.mp hr
    exact h T hT
  have htotal : ‖operators.prod‖₊ ≤ bound ^ operators.length :=
    operators.nnnorm_prod_le.trans (by simpa using hnn)
  exact_mod_cast htotal

/-- A positive-length ordered product of uniformly strict contractions is
itself a strict contraction. The factor bounds are analytic assumptions. -/
theorem norm_orderedProduct_lt_one {A : Type*} [NormedRing A] [NormOneClass A]
    (operators : List A) {ρ : ℝ} (hρ0 : 0 ≤ ρ) (hρ1 : ρ < 1)
    (h : ∀ T ∈ operators, ‖T‖ ≤ ρ) (hne : operators ≠ []) :
    ‖operators.prod‖ < 1 := by
  exact (norm_orderedProduct_le operators hρ0 h).trans_lt
    (pow_lt_one₀ hρ0 hρ1 (Nat.ne_zero_of_lt (List.length_pos_iff.mpr hne)))

end InfoGeometry.Analysis.MultiscaleLocalization
