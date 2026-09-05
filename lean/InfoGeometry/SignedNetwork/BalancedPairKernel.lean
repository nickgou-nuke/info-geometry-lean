import Mathlib

/-!
# A finite, exact first-moment signed pair kernel

The real vector `w` is a mass-zero column of a proposed linear generator.
It is not identified with an imaginary part of an arbitrary intertwiner.
The positive and negative children are coupled, and their signs are multiplied
by the parent sign. The theorems identify the first-moment generator; they do
not assert construction or convergence of a stochastic particle process.
-/

noncomputable section

namespace InfoGeometry.SignedNetwork.BalancedPairKernel

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

theorem positivePart_add_negativePart (w : C → ℝ) (a : C) :
    positivePart w a + negativePart w a = |w a| := by
  unfold positivePart negativePart
  rcases le_total 0 (w a) with h | h
  · rw [max_eq_left h, max_eq_right (neg_nonpos.mpr h), abs_of_nonneg h]
    ring
  · rw [max_eq_right h, max_eq_left (neg_nonneg.mpr h), abs_of_nonpos h]
    ring

theorem positivePart_nonneg (w : C → ℝ) (a : C) : 0 ≤ positivePart w a :=
  le_max_right _ _

theorem negativePart_nonneg (w : C → ℝ) (a : C) : 0 ≤ negativePart w a :=
  le_max_right _ _

theorem positiveMass_eq_negativeMass (w : C → ℝ) (hw : ∑ a, w a = 0) :
    positiveMass w = ∑ a, negativePart w a := by
  apply sub_eq_zero.mp
  calc
    positiveMass w - ∑ a, negativePart w a =
        ∑ a, (positivePart w a - negativePart w a) := by
      simp only [positiveMass, Finset.sum_sub_distrib]
    _ = ∑ a, w a := by simp only [positivePart_sub_negativePart]
    _ = 0 := hw

theorem sum_abs_eq_two_positiveMass (w : C → ℝ) (hw : ∑ a, w a = 0) :
    (∑ a, |w a|) = 2 * positiveMass w := by
  calc
    (∑ a, |w a|) = ∑ a, (positivePart w a + negativePart w a) := by
      simp only [positivePart_add_negativePart]
    _ = positiveMass w + ∑ a, negativePart w a := by
      simp only [Finset.sum_add_distrib, positiveMass]
    _ = 2 * positiveMass w := by
      rw [← positiveMass_eq_negativeMass w hw]
      ring

/-- A balanced column with no positive mass is identically zero. -/
theorem zero_column_of_zero_mass (w : C → ℝ) (hw : ∑ a, w a = 0)
    (hγ : positiveMass w = 0) : w = 0 := by
  funext a
  have hp : positivePart w a ≤ positiveMass w :=
    Finset.single_le_sum (fun c _ => positivePart_nonneg w c) (Finset.mem_univ a)
  have hn : negativePart w a ≤ ∑ c, negativePart w c :=
    Finset.single_le_sum (fun c _ => negativePart_nonneg w c) (Finset.mem_univ a)
  rw [← positiveMass_eq_negativeMass w hw, hγ] at hn
  rw [hγ] at hp
  have hp0 : positivePart w a = 0 := le_antisymm hp (positivePart_nonneg w a)
  have hn0 : negativePart w a = 0 := le_antisymm hn (negativePart_nonneg w a)
  have h := positivePart_sub_negativePart w a
  simpa only [hp0, hn0, sub_self, Pi.zero_apply] using h.symm

/-- Pair intensity. The total pair rate is `positiveMass w`, not twice it. -/
def pairRate (w : C → ℝ) (a b : C) : ℝ :=
  positivePart w a * negativePart w b / positiveMass w

theorem pairRate_nonneg (w : C → ℝ) (a b : C) : 0 ≤ pairRate w a b := by
  apply div_nonneg
  · exact mul_nonneg (positivePart_nonneg w a) (negativePart_nonneg w b)
  · exact Finset.sum_nonneg (fun c _ => positivePart_nonneg w c)

theorem sum_pairRate_right (w : C → ℝ) (hw : ∑ a, w a = 0)
    (hγ : positiveMass w ≠ 0) (a : C) :
    (∑ b, pairRate w a b) = positivePart w a := by
  calc
    (∑ b, pairRate w a b) =
        positivePart w a * (∑ b, negativePart w b) / positiveMass w := by
      simp only [pairRate, Finset.mul_sum, Finset.sum_div]
    _ = positivePart w a * positiveMass w / positiveMass w := by
      rw [← positiveMass_eq_negativeMass w hw]
    _ = positivePart w a := mul_div_cancel_right₀ _ hγ

theorem sum_pairRate_left (w : C → ℝ) (hγ : positiveMass w ≠ 0) (b : C) :
    (∑ a, pairRate w a b) = negativePart w b := by
  calc
    (∑ a, pairRate w a b) =
        (∑ a, positivePart w a) * negativePart w b / positiveMass w := by
      simp only [pairRate, Finset.sum_mul, Finset.sum_div]
    _ = negativePart w b := by
      change positiveMass w * negativePart w b / positiveMass w = _
      field_simp [hγ]
      ring

/-- Exact drift of positive children minus negative children. -/
theorem pairRate_recovers_column (w : C → ℝ) (hw : ∑ a, w a = 0)
    (hγ : positiveMass w ≠ 0) (a : C) :
    (∑ b, pairRate w a b) - (∑ b, pairRate w b a) = w a := by
  rw [sum_pairRate_right w hw hγ, sum_pairRate_left w hγ,
    positivePart_sub_negativePart]

theorem total_pairRate (w : C → ℝ) (hw : ∑ a, w a = 0)
    (hγ : positiveMass w ≠ 0) :
    (∑ a, ∑ b, pairRate w a b) = positiveMass w := by
  simp only [sum_pairRate_right w hw hγ, positiveMass]

/-- Conditional pair law, used only when the event rate is nonzero. -/
def pairProbability (w : C → ℝ) (a b : C) : ℝ :=
  pairRate w a b / positiveMass w

theorem pairProbability_nonneg (w : C → ℝ) (a b : C) :
    0 ≤ pairProbability w a b := by
  apply div_nonneg (pairRate_nonneg w a b)
  exact Finset.sum_nonneg (fun c _ => positivePart_nonneg w c)

theorem sum_pairProbability (w : C → ℝ) (hw : ∑ a, w a = 0)
    (hγ : positiveMass w ≠ 0) :
    (∑ a, ∑ b, pairProbability w a b) = 1 := by
  unfold pairProbability
  simp_rw [← Finset.sum_div]
  rw [total_pairRate w hw hγ, div_self hγ]

/-- The first-moment identity also includes the zero-rate case. -/
theorem pairRate_recovers_column_all (w : C → ℝ) (hw : ∑ a, w a = 0) (a : C) :
    (∑ b, pairRate w a b) - (∑ b, pairRate w b a) = w a := by
  by_cases hγ : positiveMass w = 0
  · have hz := zero_column_of_zero_mass w hw hγ
    subst w
    simp [pairRate, positivePart, negativePart, positiveMass]
  · exact pairRate_recovers_column w hw hγ a

/-- Both children inherit the sign of their parent, with opposite relative signs. -/
theorem parent_scaled_first_moment (s : ℝ) (w : C → ℝ)
    (hw : ∑ a, w a = 0) (hγ : positiveMass w ≠ 0) (a : C) :
    s * ((∑ b, pairRate w a b) - (∑ b, pairRate w b a)) = s * w a := by
  rw [pairRate_recovers_column w hw hγ]

/-- Pair events preserve constant observables, irrespective of their destinations. -/
theorem pair_event_constant (s c : ℝ) : s * c + (-s) * c = 0 := by ring

/-- A zero column produces no events under the totalized definition. -/
@[simp] theorem pairRate_zero (a : C) (b : C) : pairRate (fun _ : C => 0) a b = 0 := by
  simp [pairRate, positivePart, negativePart, positiveMass]

end InfoGeometry.SignedNetwork.BalancedPairKernel
