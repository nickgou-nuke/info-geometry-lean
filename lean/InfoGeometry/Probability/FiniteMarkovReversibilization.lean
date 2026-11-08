/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Physics.FiniteStationaryCurrent
import InfoGeometry.Probability.FiniteMarkovWeightedAdjoint

/-!
# Reversible averaging of a stationary finite kernel

Use the existing `Physics.weightedSelfPart`, on the same finite matrix carrier.
Positive stationary weights and stochasticity imply that this average is again
stochastic and has the same stationary weight. Its weighted flux is the average
of the two directed fluxes. Thus it preserves undirected support, not a causal
triangular mask; the latter is subject to `CausalDetailedBalanceObstruction`.
-/

namespace InfoGeometry.Physics

variable {n : Type*} [Fintype n]

omit [Fintype n] in
theorem weightedAdjoint_nonneg (π : n → ℝ) (P : Matrix n n ℝ)
    (hπ : ∀ i, 0 < π i) (hP : ∀ i j, 0 ≤ P i j) (i j : n) :
    0 ≤ weightedAdjoint π P i j :=
  mul_nonneg (mul_nonneg (inv_nonneg.mpr (hπ i).le) (hP j i)) (hπ j).le

theorem weightedAdjoint_row_sum (π : n → ℝ) (P : Matrix n n ℝ)
    (hπ : ∀ i, π i ≠ 0)
    (hstationary : ∀ j, ∑ i, π i * P i j = π j) (i : n) :
    ∑ j, weightedAdjoint π P i j = 1 := by
  calc
    _ = (π i)⁻¹ * ∑ j, π j * P j i := by
      simp only [weightedAdjoint, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j _
      ring
    _ = 1 := by rw [hstationary, inv_mul_cancel₀ (hπ i)]

omit [Fintype n] in
theorem weightedSelfPart_nonneg (π : n → ℝ) (P : Matrix n n ℝ)
    (hπ : ∀ i, 0 < π i) (hP : ∀ i j, 0 ≤ P i j) (i j : n) :
    0 ≤ weightedSelfPart π P i j :=
  mul_nonneg (by norm_num) (add_nonneg (hP i j) (weightedAdjoint_nonneg π P hπ hP i j))

theorem weightedSelfPart_row_sum (π : n → ℝ) (P : Matrix n n ℝ)
    (hπ : ∀ i, π i ≠ 0) (hrow : ∀ i, ∑ j, P i j = 1)
    (hstationary : ∀ j, ∑ i, π i * P i j = π j) (i : n) :
    ∑ j, weightedSelfPart π P i j = 1 := by
  simp only [weightedSelfPart, ← Finset.mul_sum, Finset.sum_add_distrib,
    hrow, weightedAdjoint_row_sum π P hπ hstationary]
  norm_num

omit [Fintype n] in
/-- Weighted edge flux is symmetrized without changing the state carrier. -/
theorem weightedSelfPart_flux (π : n → ℝ) (P : Matrix n n ℝ)
    (hπ : ∀ i, π i ≠ 0) (i j : n) :
    π i * weightedSelfPart π P i j = (π i * P i j + π j * P j i) / 2 := by
  unfold weightedSelfPart weightedAdjoint
  field_simp [hπ i]

omit [Fintype n] in
/-- Averaging retains exactly the union of the two directed supports. -/
theorem weightedSelfPart_eq_zero_iff (π : n → ℝ) (P : Matrix n n ℝ)
    (hπ : ∀ i, 0 < π i) (hP : ∀ i j, 0 ≤ P i j) (i j : n) :
    weightedSelfPart π P i j = 0 ↔ P i j = 0 ∧ P j i = 0 := by
  have hf := weightedSelfPart_flux π P (fun i => (hπ i).ne') i j
  constructor
  · intro hz
    rw [hz, mul_zero] at hf
    have ha := mul_nonneg (hπ i).le (hP i j)
    have hb := mul_nonneg (hπ j).le (hP j i)
    have hleft : π i * P i j = 0 := by linarith
    have hright : π j * P j i = 0 := by linarith
    exact ⟨(mul_eq_zero.mp hleft).resolve_left (hπ i).ne',
      (mul_eq_zero.mp hright).resolve_left (hπ j).ne'⟩
  · rintro ⟨hij, hji⟩
    simp [weightedSelfPart, weightedAdjoint, hij, hji]

theorem weightedSelfPart_detailedBalance [DecidableEq n]
    (π : n → ℝ) (P : Matrix n n ℝ) (hπ : ∀ i, π i ≠ 0) :
    Probability.DetailedBalance π (weightedSelfPart π P) := by
  apply (Probability.detailedBalance_iff_all_edge_currents_zero _ _).mpr
  intro i j
  unfold Probability.stationaryEdgeCurrent
  rw [weightedSelfPart_flux π P hπ, weightedSelfPart_flux π P hπ]
  exact sub_eq_zero.mpr (congrArg (fun x : ℝ => x / 2) (add_comm _ _))

theorem weightedSelfPart_stationary (π : n → ℝ) (P : Matrix n n ℝ)
    (hπ : ∀ i, π i ≠ 0) (hrow : ∀ i, ∑ j, P i j = 1)
    (hstationary : ∀ j, ∑ i, π i * P i j = π j) (j : n) :
    ∑ i, π i * weightedSelfPart π P i j = π j := by
  simp_rw [weightedSelfPart_flux π P hπ]
  rw [← Finset.sum_div, Finset.sum_add_distrib, hstationary,
    ← Finset.mul_sum, hrow, mul_one]
  ring

end InfoGeometry.Physics
