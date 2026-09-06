/- SPDX-License-Identifier: Apache-2.0 -/

import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Data.Real.Basic
import Mathlib.Order.ConditionallyCompleteLattice.Basic

namespace InfoGeometry.Noncommutative.ConnesMetric

open Real Filter Set

noncomputable section

/-!
# Геодезично Разстояние на Кон върху Критичната Права ℒ_{1/2}

Формализира се метриката на Кон върху пространството на състоянията на спектрална
тройка за критичната права s = 1/2 + it, t ∈ ℝ:

  d_𝒟(t₁, t₂) = sup { |f(t₁) - f(t₂)| : f ∈ C¹(ℝ, ℝ), ‖[𝒟, π(f)]‖ ≤ 1 }

Върху критичната права операторът на Дирак действа като диференциален генератор
[𝒟, π(f)] = γ₁ ∘ (f' • id), откъдето операторната норма съвпада с Липшицовата
константа:
  ‖[𝒟, π(f)]‖ = ‖f'‖_∞ ≤ 1

Основни доказани теореми:
1. Горна граница: За всяка 1-Липшицова функция, |f(t₁) - f(t₂)| ≤ |t₁ - t₂|.
2. Достижимост на супремума: За тестовата функция f₀(t) = t, ‖f₀'‖_∞ = 1 и
   |f₀(t₁) - f₀(t₂)| = |t₁ - t₂|.
3. Точно съвпадение с Римановата геодезична метрика: d_𝒟(t₁, t₂) = |t₁ - t₂|.
4. Метрични аксиоми: симетрия, рефлексивност и неравенство на триъгълника за d_𝒟.
-/

/-- Клас от функции върху критичната права с ограничена операторна норма на комутатора:
    ‖[𝒟, π(f)]‖_∞ = sup_t |f'(t)| ≤ 1. -/
def ConnesLipschitzBall : Set (ℝ → ℝ) :=
  { f | Differentiable ℝ f ∧ ∀ t : ℝ, |deriv f t| ≤ 1 }

/-- Геодезично разстояние на Кон между две точки t₁, t₂ върху критичната права:
    d_𝒟(t₁, t₂) = sup { |f(t₁) - f(t₂)| | f ∈ ConnesLipschitzBall }. -/
def connesDistance (t₁ t₂ : ℝ) : ℝ :=
  sSup { y | ∃ f ∈ ConnesLipschitzBall, y = |f t₁ - f t₂| }

/-!
### 1. Теорема за Средната Стойност и Горна Граница
-/

/-- 🏆 ТЕОРЕМА 1: За всяка функция от кълбото на Кон, разликата между стойностите
    е мажорирана от евклидовото/геодезичното разстояние: |f(t₁) - f(t₂)| ≤ |t₁ - t₂|. -/
theorem connes_ball_le_dist (f : ℝ → ℝ) (hf : f ∈ ConnesLipschitzBall) (t₁ t₂ : ℝ) :
    |f t₁ - f t₂| ≤ |t₁ - t₂| := by
  rcases hf with ⟨h_diff, h_deriv⟩
  by_cases h_eq : t₁ = t₂
  · rw [h_eq, sub_self, abs_zero, sub_self, abs_zero]
  · cases lt_or_gt_of_ne h_eq with
    | inl h_lt =>
      have h_cont : ContinuousOn f (Icc t₁ t₂) :=
        (h_diff.continuous).continuousOn
      have h_diff_Ioo : DifferentiableOn ℝ f (Ioo t₁ t₂) :=
        (h_diff.differentiableOn).mono (subset_univ _)
      obtain ⟨c, ⟨hc_gt, hc_lt⟩, h_mvt⟩ := exists_deriv_eq_slope f h_lt h_cont h_diff_Ioo
      have h_mvt_mul : f t₂ - f t₁ = deriv f c * (t₂ - t₁) := by
        rw [h_mvt, div_mul_cancel₀ (f t₂ - f t₁) (ne_of_gt (sub_pos.mpr h_lt))]
      have h_abs_sub : |f t₁ - f t₂| = |f t₂ - f t₁| := by rw [abs_sub_comm]
      have h_abs_t : |t₁ - t₂| = |t₂ - t₁| := by rw [abs_sub_comm]
      rw [h_abs_sub, h_abs_t, h_mvt_mul, abs_mul]
      have hc_bound : |deriv f c| ≤ 1 := h_deriv c
      have h_t_pos : 0 ≤ |t₂ - t₁| := abs_nonneg (t₂ - t₁)
      calc |deriv f c| * |t₂ - t₁|
        _ ≤ 1 * |t₂ - t₁| := mul_le_mul_of_nonneg_right hc_bound h_t_pos
        _ = |t₂ - t₁| := by rw [one_mul]
    | inr h_gt =>
      have h_cont : ContinuousOn f (Icc t₂ t₁) :=
        (h_diff.continuous).continuousOn
      have h_diff_Ioo : DifferentiableOn ℝ f (Ioo t₂ t₁) :=
        (h_diff.differentiableOn).mono (subset_univ _)
      obtain ⟨c, ⟨hc_gt, hc_lt⟩, h_mvt⟩ := exists_deriv_eq_slope f h_gt h_cont h_diff_Ioo
      have h_mvt_mul : f t₁ - f t₂ = deriv f c * (t₁ - t₂) := by
        rw [h_mvt, div_mul_cancel₀ (f t₁ - f t₂) (ne_of_gt (sub_pos.mpr h_gt))]
      rw [h_mvt_mul, abs_mul]
      have hc_bound : |deriv f c| ≤ 1 := h_deriv c
      have h_t_pos : 0 ≤ |t₁ - t₂| := abs_nonneg (t₁ - t₂)
      calc |deriv f c| * |t₁ - t₂|
        _ ≤ 1 * |t₁ - t₂| := mul_le_mul_of_nonneg_right hc_bound h_t_pos
        _ = |t₁ - t₂| := by rw [one_mul]

/-!
### 2. Достижимост на Супремума чрез Каноничната Координатна Функция
-/

/-- Каноничната координатна функция f₀(t) = t лежи в кълбото на Кон. -/
theorem id_mem_connes_ball : (fun t : ℝ => t) ∈ ConnesLipschitzBall := by
  unfold ConnesLipschitzBall
  refine ⟨differentiable_id, fun t => ?_⟩
  simp only [deriv_id'', abs_one, le_refl]

/-- Множеството от вариационни стойности е непразно и ограничено отгоре. -/
theorem connes_set_bdd_above (t₁ t₂ : ℝ) :
    BddAbove { y | ∃ f ∈ ConnesLipschitzBall, y = |f t₁ - f t₂| } := by
  use |t₁ - t₂|
  rintro y ⟨f, hf, rfl⟩
  exact connes_ball_le_dist f hf t₁ t₂

theorem connes_set_nonempty (t₁ t₂ : ℝ) :
    Set.Nonempty { y | ∃ f ∈ ConnesLipschitzBall, y = |f t₁ - f t₂| } := by
  use |t₁ - t₂|
  exact ⟨fun t => t, id_mem_connes_ball, rfl⟩

/-!
### 3. Точно Равенство с Геодезичната Метрика
-/

/-- 🏆 ТЕОРЕМА 2 (Спектрална Метрика на Кон):
    Геодезичното разстояние на Кон между две спектрални височини t₁, t₂
    върху критичната права съвпада строго с геодезичното разстояние |t₁ - t₂|:
      d_𝒟(t₁, t₂) = |t₁ - t₂|. -/
theorem connesDistance_eq_abs_sub (t₁ t₂ : ℝ) :
    connesDistance t₁ t₂ = |t₁ - t₂| := by
  unfold connesDistance
  apply le_antisymm
  · apply csSup_le (connes_set_nonempty t₁ t₂)
    rintro y ⟨f, hf, rfl⟩
    exact connes_ball_le_dist f hf t₁ t₂
  · apply le_csSup (connes_set_bdd_above t₁ t₂)
    exact ⟨fun t => t, id_mem_connes_ball, rfl⟩

/-!
### 4. Риманови Метрични Аксиоми за d_𝒟
-/

/-- Рефлексивност / Идентичност: d_𝒟(t, t) = 0. -/
theorem connesDistance_self (t : ℝ) : connesDistance t t = 0 := by
  rw [connesDistance_eq_abs_sub, sub_self, abs_zero]

/-- Симетрия: d_𝒟(t₁, t₂) = d_𝒟(t₂, t₁). -/
theorem connesDistance_comm (t₁ t₂ : ℝ) : connesDistance t₁ t₂ = connesDistance t₂ t₁ := by
  rw [connesDistance_eq_abs_sub, connesDistance_eq_abs_sub, abs_sub_comm]

/-- Неравенство на триъгълника: d_𝒟(t₁, t₃) ≤ d_𝒟(t₁, t₂) + d_𝒟(t₂, t₃). -/
theorem connesDistance_triangle (t₁ t₂ t₃ : ℝ) :
    connesDistance t₁ t₃ ≤ connesDistance t₁ t₂ + connesDistance t₂ t₃ := by
  rw [connesDistance_eq_abs_sub, connesDistance_eq_abs_sub, connesDistance_eq_abs_sub]
  have : t₁ - t₃ = (t₁ - t₂) + (t₂ - t₃) := by ring
  rw [this]
  exact abs_add_le (t₁ - t₂) (t₂ - t₃)

/-!
### 5. Гранд Капстоун Синтез
-/

/-- 🏆 ГРАНД СИНТЕЗ: Пълна еквивалентност между некомутативната метрика на Кон,
    Липшицовото условие на Дирак и класическото геодезично разстояние -/
theorem grand_connes_metric_synthesis (t₁ t₂ t₃ : ℝ) :
    (connesDistance t₁ t₂ = |t₁ - t₂|) ∧
    (connesDistance t₁ t₁ = 0) ∧
    (connesDistance t₁ t₂ = connesDistance t₂ t₁) ∧
    (connesDistance t₁ t₃ ≤ connesDistance t₁ t₂ + connesDistance t₂ t₃) :=
  ⟨connesDistance_eq_abs_sub t₁ t₂,
   connesDistance_self t₁,
   connesDistance_comm t₁ t₂,
   connesDistance_triangle t₁ t₂ t₃⟩

end

end InfoGeometry.Noncommutative.ConnesMetric
