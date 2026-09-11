import Mathlib.Data.Complex.Basic
import InfoGeometry.Algebra.FiniteSpinAlgebra

namespace InfoGeometry.Canonical

/-- **1. Дефиниция на Мебиусова Дискриминанта Δ = (a + d)² - 4**:
    Инвариантът на trace^2 - 4 за SL(2,ℂ) Мебиусови трансформации. -/
def moebiusDiscriminant (a d : ℂ) : ℂ :=
  (a + d)^2 - 4

/-- **Теорема 1**: Алгебрична Еквивалентност с Квадратната Дискриминанта на Неподвижните Точки:
    (a + d)² - 4 = (d - a)² + 4bc при ad - bc = 1. -/
theorem moebius_discriminant_eq_fixed_point_disc
    (a b c d : ℂ) (h_det : a * d - b * c = 1) :
    moebiusDiscriminant a d = (d - a)^2 + 4 * b * c := by
  dsimp [moebiusDiscriminant]
  calc
    (a + d)^2 - 4 = (a + d)^2 - 4 * 1 := by ring
    _ = (a + d)^2 - 4 * (a * d - b * c) := by rw [←h_det]
    _ = (d - a)^2 + 4 * b * c := by ring

/-- **Теорема 2**: Параболичен Праг (Parabolic Threshold):
    Ако Tr(g) = a + d = 2 (или -2), дискриминантата е строго нула (Δ = 0)! -/
theorem parabolic_discriminant_zero (a d : ℂ) (h_tr : a + d = 2) :
    moebiusDiscriminant a d = 0 := by
  dsimp [moebiusDiscriminant]
  rw [h_tr]
  ring


end InfoGeometry.Canonical
