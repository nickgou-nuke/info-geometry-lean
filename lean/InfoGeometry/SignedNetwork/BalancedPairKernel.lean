import Mathlib

namespace InfoGeometry.SignedNetwork.BalancedPairKernel

noncomputable section

variable {C : Type*} [Fintype C]

def positivePart (w : C → ℝ) (a : C) : ℝ := max (w a) 0
def negativePart (w : C → ℝ) (a : C) : ℝ := max (-w a) 0
def positiveMass (w : C → ℝ) : ℝ := ∑ a, positivePart w a

@[simp] theorem positivePart_sub_negativePart (w : C → ℝ) (a : C) :
    positivePart w a - negativePart w a = w a := by
  unfold positivePart negativePart
  rcases le_total 0 (w a) with h | h
  · rw [max_eq_left h, max_eq_right (neg_nonpos.mpr h)]
    ring
  · rw [max_eq_right h, max_eq_left (neg_nonneg.mpr h)]
    ring

theorem positiveMass_eq_negativeMass_of_sum_zero (w : C → ℝ)
    (hw : ∑ a, w a = 0) :
    positiveMass w = ∑ a, negativePart w a := by
  have hparts : ∑ a, (positivePart w a - negativePart w a) = 0 := by
    simpa [positivePart_sub_negativePart] using hw
  change (∑ a, positivePart w a) = ∑ a, negativePart w a
  rw [Finset.sum_sub_distrib] at hparts
  exact sub_eq_zero.mp hparts

theorem positiveMass_zero_of_nonneg (w : C → ℝ)
    (hw : ∀ a, 0 ≤ w a) (hs : ∑ a, w a = 0) :
    positiveMass w = 0 := by
  simp only [positiveMass, positivePart]
  rw [Finset.sum_eq_zero]
  intro a ha
  rw [max_eq_left (hw a)]
  exact Finset.sum_eq_zero_iff_of_nonneg (fun i hi => hw i) |>.mp hs a ha

theorem positivePart_nonneg (w : C → ℝ) (a : C) : 0 ≤ positivePart w a :=
  le_max_right _ _

theorem negativePart_nonneg (w : C → ℝ) (a : C) : 0 ≤ negativePart w a :=
  le_max_right _ _

def pairRate (w : C → ℝ) (a b : C) : ℝ :=
  positivePart w a * negativePart w b / positiveMass w

theorem sum_pairRate_right (w : C → ℝ) (hw : ∑ a, w a = 0)
    (hγ : positiveMass w ≠ 0) (a : C) :
    (∑ b, pairRate w a b) = positivePart w a := by
  calc
    (∑ b, pairRate w a b) =
        positivePart w a * (∑ b, negativePart w b) / positiveMass w := by
      simp [pairRate, Finset.mul_sum, Finset.sum_div]
    _ = positivePart w a * positiveMass w / positiveMass w := by
      rw [← positiveMass_eq_negativeMass_of_sum_zero w hw]
    _ = positivePart w a := mul_div_cancel_right₀ _ hγ

theorem sum_pairRate_left (w : C → ℝ) (hγ : positiveMass w ≠ 0) (b : C) :
    (∑ a, pairRate w a b) = negativePart w b := by
  calc
    (∑ a, pairRate w a b) =
        (∑ a, positivePart w a) * negativePart w b / positiveMass w := by
      simp only [pairRate, Finset.sum_mul, Finset.sum_div]
    _ = negativePart w b := by
      change positiveMass w * negativePart w b / positiveMass w = _
      exact mul_div_cancel_left₀ _ hγ

theorem pairRate_recovers_column (w : C → ℝ) (hw : ∑ a, w a = 0)
    (hγ : positiveMass w ≠ 0) (a : C) :
    (∑ b, pairRate w a b) - (∑ b, pairRate w b a) = w a := by
  rw [sum_pairRate_right w hw hγ, sum_pairRate_left w hγ,
    positivePart_sub_negativePart]

theorem zero_column_of_zero_mass (w : C → ℝ) (hw : ∑ a, w a = 0)
    (hγ : positiveMass w = 0) : ∀ a, w a = 0 := by
  have hn : (∑ a, negativePart w a) = 0 := by
    rw [← positiveMass_eq_negativeMass_of_sum_zero w hw, hγ]
  intro a
  have hp : positivePart w a = 0 := by
    apply (Finset.sum_eq_zero_iff_of_nonneg (fun i hi => positivePart_nonneg w i)).mp
    simpa [positiveMass] using hγ
    exact Finset.mem_univ a
  have hn' : negativePart w a = 0 := by
    exact (Finset.sum_eq_zero_iff_of_nonneg (fun i hi => negativePart_nonneg w i)).mp hn a
      (Finset.mem_univ a)
  have := positivePart_sub_negativePart w a
  rw [hp, hn'] at this
  linarith

theorem pairRate_recovers_column_all (w : C → ℝ) (hw : ∑ a, w a = 0) (a : C) :
    (∑ b, pairRate w a b) - (∑ b, pairRate w b a) = w a := by
  by_cases hγ : positiveMass w = 0
  · have hz := zero_column_of_zero_mass w hw hγ a
    have hpos : ∀ x, positivePart w x = 0 := by
      intro x
      have := zero_column_of_zero_mass w hw hγ x
      unfold positivePart
      rw [this]
      simp
    have hneg : ∀ x, negativePart w x = 0 := by
      intro x
      have := zero_column_of_zero_mass w hw hγ x
      unfold negativePart
      rw [this]
      simp
    simp [pairRate, hγ, hpos, hneg, hz]
  · exact pairRate_recovers_column w hw hγ a

end
end InfoGeometry.SignedNetwork.BalancedPairKernel
