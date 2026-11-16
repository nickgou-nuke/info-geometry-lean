/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import Mathlib.Basic.Real.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import InfoGeometry.Physics.InformationEnergy.ThermalSpectrum

/-!
# Conservation constraints for information-energy proposals

The variables are real numerical values in fixed consistent units. The source
is Vopson (2022), equations (3)-(10), PDF pages 3-5. A proposed erasure energy
`q` remains supplied data; its identification with stored rest energy is an
additional model hypothesis. The theorems keep that hypothesis visible.

The source's approximate 511 keV labels do not exclude a small energy transfer
to another channel. The obstruction below applies to an exact exhausted
energy budget, not to the existence of four-photon final states.
-/

namespace InfoGeometry.Physics.InformationEnergy.EnergyAccounting

open scoped BigOperators

/-- The proposed information mass is already included in total rest energy. -/
theorem rest_energy_decomposition (physical q c : ℝ) (hc : c ≠ 0) :
    (physical + q / c ^ 2) * c ^ 2 = physical * c ^ 2 + q := by
  field_simp [hc]

/-- For a pair, adding the proposed erasure energy again doubles its contribution. -/
theorem pair_double_counting_gap (physical₁ physical₂ q₁ q₂ c : ℝ) (hc : c ≠ 0) :
    ((physical₁ + q₁ / c ^ 2) * c ^ 2 +
      (physical₂ + q₂ / c ^ 2) * c ^ 2 + q₁ + q₂) -
      (physical₁ * c ^ 2 + physical₂ * c ^ 2 + q₁ + q₂) = q₁ + q₂ := by
  rw [rest_energy_decomposition _ _ _ hc, rest_energy_decomposition _ _ _ hc]
  ring

/-- Positive assigned information energy makes the two pair ledgers inequivalent. -/
theorem double_counted_pair_strictly_larger (physical₁ physical₂ q₁ q₂ c : ℝ)
    (hc : c ≠ 0) (hq : 0 < q₁ + q₂) :
    physical₁ * c ^ 2 + physical₂ * c ^ 2 + q₁ + q₂ <
      (physical₁ + q₁ / c ^ 2) * c ^ 2 +
        (physical₂ + q₂ / c ^ 2) * c ^ 2 + q₁ + q₂ := by
  have hgap := pair_double_counting_gap physical₁ physical₂ q₁ q₂ c hc
  linarith only [hgap, hq]

/-- Once the gamma channel exactly exhausts the input, every nonnegative extra energy is zero. -/
theorem no_extra_energy_of_exhausted_budget {ι : Type*} [Fintype ι]
    (input gamma : ℝ) (extra : ι → ℝ) (hnonneg : ∀ i, 0 ≤ extra i)
    (hbalance : input = gamma + ∑ i, extra i) (hexhausted : gamma = input) :
    ∀ i, extra i = 0 := by
  have hsum : ∑ i, extra i = 0 := by linarith only [hbalance, hexhausted]
  intro i
  have hle : extra i ≤ ∑ j, extra j :=
    Finset.single_le_sum (fun j _ => hnonneg j) (Finset.mem_univ i)
  exact le_antisymm (by simpa [hsum] using hle) (hnonneg i)

/-- Each equal gamma energy is single-particle rest energy minus the per-particle allocation. -/
theorem equal_gamma_energy_with_extra_channel {mass c gamma q : ℝ}
    (hbalance : 2 * mass * c ^ 2 = 2 * gamma + 2 * q) :
    gamma = mass * c ^ 2 - q := by
  linarith only [hbalance]

/-- A heat lower bound and the first-law balance alone do not force stored-energy loss.
The explicit countermodel has heat and supplied work both equal to the bound. -/
theorem heat_bound_does_not_force_internal_energy_loss (bound : ℝ) :
    ¬ (∀ heat work change : ℝ,
      bound ≤ heat → change = work - heat → change < 0) := by
  intro h
  have hzero := h bound bound 0 le_rfl (by ring)
  exact (lt_irrefl (0 : ℝ)) hzero

/-- Any positive photon count can share a positive scalar energy budget equally.
Energy conservation alone therefore does not determine the multiplicity. -/
theorem every_positive_count_realizes_energy (budget : ℝ) (hbudget : 0 < budget)
    (count : ℕ) (hcount : 0 < count) :
    ∃ energy : Fin count → ℝ,
      (∀ i, 0 < energy i) ∧ ∑ i, energy i = budget := by
  have hcountReal : 0 < (count : ℝ) := by exact_mod_cast hcount
  refine ⟨fun _ => budget / count, fun _ => div_pos hbudget hcountReal, ?_⟩
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  field_simp [hcountReal.ne']

/-- Equal photon sharing fixes wavelength only after the emitted energy fraction and count are given. -/
theorem wavelength_of_channel_allocation {energy budget fraction wavelength h c : ℝ}
    (count : ℕ) (hchannel : 0 < fraction * budget)
    (hallocation : (count : ℝ) * energy = fraction * budget)
    (hphoton : energy * wavelength = h * c) :
    wavelength = (count : ℝ) * h * c / (fraction * budget) := by
  apply (eq_div_iff hchannel.ne').mpr
  rw [← hallocation]
  calc
    wavelength * ((count : ℝ) * energy) = (count : ℝ) * (energy * wavelength) := by ring
    _ = (count : ℝ) * h * c := by rw [hphoton]; ring

/-- Equation (11) follows when the entire proposed pair energy is assigned equally
to exactly two photons, together with the photon energy-wavelength relation. -/
theorem paper_wavelength_of_equal_pair_allocation {energy wavelength h c I kB T : ℝ}
    (hI : 0 < I) (hkB : 0 < kB) (hT : 0 < T)
    (hallocation : 2 * energy = 2 * I * kB * T * Real.log 2)
    (hphoton : energy * wavelength = h * c) :
    wavelength = ThermalSpectrum.wavelength h c kB I T := by
  have hlog : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have henergy : energy = I * kB * T * Real.log 2 := by linarith only [hallocation]
  have hden : I * kB * T * Real.log 2 ≠ 0 :=
    ne_of_gt (mul_pos (mul_pos (mul_pos hI hkB) hT) hlog)
  unfold ThermalSpectrum.wavelength
  apply (eq_div_iff hden).mpr
  rw [← henergy, mul_comm]
  exact hphoton

/-- Allowing zero allocation to the IR channel permits positive output in a different channel. -/
theorem zero_ir_allocation_compatible (budget : ℝ) (hbudget : 0 < budget) :
    ∃ infrared other : ℝ, 0 ≤ infrared ∧ 0 < other ∧
      infrared + other = budget ∧ infrared = 0 := by
  exact ⟨0, budget, le_rfl, hbudget, zero_add budget, rfl⟩

end InfoGeometry.Physics.InformationEnergy.EnergyAccounting
