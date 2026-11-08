import Mathlib.Topology.Compactification.OnePoint.ProjectiveLine
import InfoGeometry.Algebra.FiniteSpinAlgebra
import Mathlib.Analysis.Complex.Basic

open Matrix OnePoint
open scoped Projectivization

namespace InfoGeometry

noncomputable def rep : OnePoint ℂ → ℂ × ℂ
| ∞ => (1, 0)
| (c : ℂ) => (c, 1)

noncomputable def delta (a b : OnePoint ℂ) : ℂ :=
  (rep b).1 * (rep a).2 - (rep b).2 * (rep a).1

noncomputable def crossRatio (z1 z2 z3 z4 : OnePoint ℂ) : OnePoint ℂ :=
  let num := delta z1 z3 * delta z2 z4
  let den := delta z2 z3 * delta z1 z4
  if den = 0 then ∞ else (num / den : ℂ)

noncomputable def factor (g : GL (Fin 2) ℂ) : OnePoint ℂ → ℂ
| ∞ => if g 1 0 = 0 then g 0 0 else g 1 0
| (k : ℂ) => if g 1 0 * k + g 1 1 = 0 then g 0 0 * k + g 0 1 else g 1 0 * k + g 1 1

lemma factor_ne_zero (g : GL (Fin 2) ℂ) (z : OnePoint ℂ) : factor g z ≠ 0 := by
  cases z <;> dsimp [factor]
  · split_ifs with h
    · have hdet : g.1.det ≠ 0 := g.det_ne_zero
      rw [det_fin_two] at hdet
      intro h0
      rw [h0, h] at hdet
      simp at hdet
    · exact h
  · rename_i k
    split_ifs with h
    · have hdet : g.1.det ≠ 0 := g.det_ne_zero
      rw [det_fin_two] at hdet
      intro h0
      have h1 : g 0 0 * (g 1 0 * k + g 1 1) - g 1 0 * (g 0 0 * k + g 0 1) = g 0 0 * g 1 1 - g 0 1 * g 1 0 := by ring
      rw [h, h0] at h1
      simp at h1
      exact hdet h1.symm
    · exact h

lemma rep_smul (g : GL (Fin 2) ℂ) (z : OnePoint ℂ) :
    factor g z • rep (g • z) = g.1 • rep z := by
  cases z <;> dsimp [factor]
  · by_cases h : g 1 0 = 0
    · simp only [smul_infty_eq_ite, h, if_true]
      ext
      · simp [rep, Matrix.fin_two_smul_prod]
      · simp [rep, Matrix.fin_two_smul_prod, h]
    · simp only [smul_infty_eq_ite, h, if_false]
      ext
      · simp [rep, Matrix.fin_two_smul_prod]
        exact mul_div_cancel₀ _ h
      · simp [rep, Matrix.fin_two_smul_prod]
  · rename_i k
    by_cases h : g 1 0 * k + g 1 1 = 0
    · simp only [smul_some_eq_ite, h, if_true]
      ext
      · simp [rep, Matrix.fin_two_smul_prod]
      · simp [rep, Matrix.fin_two_smul_prod, h]
    · simp only [smul_some_eq_ite, h, if_false]
      ext
      · simp [rep, Matrix.fin_two_smul_prod]
        exact mul_div_cancel₀ _ h
      · simp [rep, Matrix.fin_two_smul_prod]

lemma delta_smul_vec (c d : ℂ) (a b : ℂ × ℂ) :
    (d • b).1 * (c • a).2 - (d • b).2 * (c • a).1 = c * d * (b.1 * a.2 - b.2 * a.1) := by
  dsimp; ring

lemma delta_matrix (M : Matrix (Fin 2) (Fin 2) ℂ) (a b : ℂ × ℂ) :
    (M • b).1 * (M • a).2 - (M • b).2 * (M • a).1 = M.det * (b.1 * a.2 - b.2 * a.1) := by
  simp [Matrix.fin_two_smul_prod, det_fin_two]; ring

lemma delta_smul (g : GL (Fin 2) ℂ) (z1 z2 : OnePoint ℂ) :
    factor g z1 * factor g z2 * delta (g • z1) (g • z2) = g.1.det * delta z1 z2 := by
  have h := delta_matrix g.1 (rep z1) (rep z2)
  rw [← rep_smul g z1, ← rep_smul g z2] at h
  have h2 := delta_smul_vec (factor g z1) (factor g z2) (rep (g • z1)) (rep (g • z2))
  unfold delta
  rw [← h2, h]

theorem crossRatio_smul (g : GL (Fin 2) ℂ) (z1 z2 z3 z4 : OnePoint ℂ) :
    crossRatio (g • z1) (g • z2) (g • z3) (g • z4) = crossRatio z1 z2 z3 z4 := by
  dsimp [crossRatio]
  have h13 := delta_smul g z1 z3
  have h24 := delta_smul g z2 z4
  have h23 := delta_smul g z2 z3
  have h14 := delta_smul g z1 z4
  set N1 := delta (g • z1) (g • z3) * delta (g • z2) (g • z4)
  set D1 := delta (g • z2) (g • z3) * delta (g • z1) (g • z4)
  set N := delta z1 z3 * delta z2 z4
  set D := delta z2 z3 * delta z1 z4
  set F := factor g z1 * factor g z2 * factor g z3 * factor g z4
  set Det2 := g.1.det * g.1.det
  have hF : F ≠ 0 := by
    refine mul_ne_zero (mul_ne_zero (mul_ne_zero (factor_ne_zero g z1) (factor_ne_zero g z2)) (factor_ne_zero g z3)) (factor_ne_zero g z4)
  have hdet2 : Det2 ≠ 0 := mul_ne_zero g.det_ne_zero g.det_ne_zero
  have hN : F * N1 = Det2 * N := by
    calc F * N1 = (factor g z1 * factor g z3 * delta (g • z1) (g • z3)) * (factor g z2 * factor g z4 * delta (g • z2) (g • z4)) := by ring
         _ = (g.1.det * delta z1 z3) * (g.1.det * delta z2 z4) := by rw [h13, h24]
         _ = Det2 * N := by ring
  have hD : F * D1 = Det2 * D := by
    calc F * D1 = (factor g z2 * factor g z3 * delta (g • z2) (g • z3)) * (factor g z1 * factor g z4 * delta (g • z1) (g • z4)) := by ring
         _ = (g.1.det * delta z2 z3) * (g.1.det * delta z1 z4) := by rw [h23, h14]
         _ = Det2 * D := by ring
  have hD_eq : D1 = 0 ↔ D = 0 := by
    constructor
    · intro h
      have H : Det2 * D = 0 := by
        calc Det2 * D = F * D1 := hD.symm
             _ = F * 0 := by rw [h]
             _ = 0 := mul_zero F
      exact (mul_eq_zero.mp H).resolve_left hdet2
    · intro h
      have H : F * D1 = 0 := by
        calc F * D1 = Det2 * D := hD
             _ = Det2 * 0 := by rw [h]
             _ = 0 := mul_zero Det2
      exact (mul_eq_zero.mp H).resolve_left hF
  by_cases hD0 : D = 0
  · have hD10 : D1 = 0 := hD_eq.mpr hD0
    simp [hD0, hD10]
  · have hD10 : D1 ≠ 0 := mt hD_eq.mp hD0
    simp [hD0, hD10]
    have hN_comm : N1 * F = Det2 * N := by rw [mul_comm N1 F, hN]
    have hD_comm : D1 * F = Det2 * D := by rw [mul_comm D1 F, hD]
    have hN1 : N1 = (Det2 * N) / F := eq_div_iff_mul_eq hF |>.mpr hN_comm
    have hD1 : D1 = (Det2 * D) / F := eq_div_iff_mul_eq hF |>.mpr hD_comm
    rw [hN1, hD1, div_div_div_cancel_right₀ hF, mul_div_mul_left _ _ hdet2]

end InfoGeometry
