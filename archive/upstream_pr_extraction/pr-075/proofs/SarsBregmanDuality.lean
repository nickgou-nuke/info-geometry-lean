import Mathlib

noncomputable section

namespace SarsBregmanDuality

open Real

def modularSurprisal (u : ℝ) : ℝ := Real.exp u - 1 - u

def expBregman (x y : ℝ) : ℝ := Real.exp x - Real.exp y - Real.exp y * (x - y)

def burgBregman (z w : ℝ) : ℝ := z / w - Real.log (z / w) - 1

def itakuraSaitoToOne (z : ℝ) : ℝ := z - Real.log z - 1

theorem modularSurprisal_nonneg (u : ℝ) : 0 ≤ modularSurprisal u := by
  unfold modularSurprisal
  linarith [Real.add_one_le_exp u]

theorem modularSurprisal_zero : modularSurprisal 0 = 0 := by
  norm_num [modularSurprisal]

theorem expBregman_factor (x y : ℝ) :
    expBregman x y = Real.exp y * modularSurprisal (x - y) := by
  unfold expBregman modularSurprisal
  have h : Real.exp x = Real.exp y * Real.exp (x - y) := by
    rw [Real.exp_sub]
    field_simp [Real.exp_ne_zero y]
  rw [h]
  ring

theorem expBregman_nonneg (x y : ℝ) : 0 ≤ expBregman x y := by
  rw [expBregman_factor]
  exact mul_nonneg (le_of_lt (Real.exp_pos y)) (modularSurprisal_nonneg (x - y))

theorem burg_exp_coordinate (x y : ℝ) :
    burgBregman (Real.exp x) (Real.exp y) = modularSurprisal (x - y) := by
  unfold burgBregman modularSurprisal
  have hdiv : Real.exp x / Real.exp y = Real.exp (x - y) := by
    rw [Real.exp_sub]
  rw [hdiv, Real.log_exp]
  ring

theorem burg_exp_nonneg (x y : ℝ) : 0 ≤ burgBregman (Real.exp x) (Real.exp y) := by
  rw [burg_exp_coordinate]
  exact modularSurprisal_nonneg (x - y)

theorem itakura_exp_coordinate (x : ℝ) :
    itakuraSaitoToOne (Real.exp x) = modularSurprisal x := by
  unfold itakuraSaitoToOne modularSurprisal
  rw [Real.log_exp]
  ring

theorem itakura_exp_nonneg (x : ℝ) : 0 ≤ itakuraSaitoToOne (Real.exp x) := by
  rw [itakura_exp_coordinate]
  exact modularSurprisal_nonneg x

def diag2 (a b : ℝ) : Matrix (Fin 2) (Fin 2) ℝ := !![a, 0; 0, b]

def quad2 (A : Matrix (Fin 2) (Fin 2) ℝ) (v : Fin 2 → ℝ) : ℝ :=
  v 0 * (A 0 0 * v 0 + A 0 1 * v 1) + v 1 * (A 1 0 * v 0 + A 1 1 * v 1)

def IsPSD2 (A : Matrix (Fin 2) (Fin 2) ℝ) : Prop := ∀ v : Fin 2 → ℝ, 0 ≤ quad2 A v

theorem diag2_psd_of_nonneg {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) : IsPSD2 (diag2 a b) := by
  intro v
  unfold quad2 diag2
  simp
  nlinarith [mul_self_nonneg (v 0), mul_self_nonneg (v 1)]

def bregmanDualDiag (x0 y0 x1 y1 : ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  diag2 (burgBregman (Real.exp x0) (Real.exp y0))
        (burgBregman (Real.exp x1) (Real.exp y1))

theorem bregmanDualDiag_psd (x0 y0 x1 y1 : ℝ) : IsPSD2 (bregmanDualDiag x0 y0 x1 y1) := by
  apply diag2_psd_of_nonneg <;> exact burg_exp_nonneg _ _

theorem bregmanDualDiag_vacuum_zero : bregmanDualDiag 0 0 0 0 = 0 := by
  have h : burgBregman 1 1 = 0 := by norm_num [burgBregman]
  ext i j <;> fin_cases i <;> fin_cases j <;> simp [bregmanDualDiag, diag2, h]

inductive CrossDomainEdge where
  | qft_modular_to_itakura_saito
  | bregman_coordinate_isomorphism
  | stabilizes_krein_entropy
  deriving DecidableEq, Repr

def edgeName : CrossDomainEdge → String
  | CrossDomainEdge.qft_modular_to_itakura_saito => "qft_modular_to_itakura_saito"
  | CrossDomainEdge.bregman_coordinate_isomorphism => "bregman_coordinate_isomorphism"
  | CrossDomainEdge.stabilizes_krein_entropy => "stabilizes_krein_entropy"

theorem bregman_duality_kernel :
    (∀ x y : ℝ, expBregman x y = Real.exp y * modularSurprisal (x - y)) ∧
    (∀ x y : ℝ, 0 ≤ expBregman x y) ∧
    (∀ x y : ℝ, burgBregman (Real.exp x) (Real.exp y) = modularSurprisal (x - y)) ∧
    (∀ x y : ℝ, 0 ≤ burgBregman (Real.exp x) (Real.exp y)) ∧
    (∀ x : ℝ, itakuraSaitoToOne (Real.exp x) = modularSurprisal x) ∧
    (∀ x0 y0 x1 y1 : ℝ, IsPSD2 (bregmanDualDiag x0 y0 x1 y1)) ∧
    bregmanDualDiag 0 0 0 0 = 0 ∧
    edgeName CrossDomainEdge.qft_modular_to_itakura_saito = "qft_modular_to_itakura_saito" ∧
    edgeName CrossDomainEdge.bregman_coordinate_isomorphism = "bregman_coordinate_isomorphism" ∧
    edgeName CrossDomainEdge.stabilizes_krein_entropy = "stabilizes_krein_entropy" := by
  exact ⟨expBregman_factor, expBregman_nonneg, burg_exp_coordinate, burg_exp_nonneg,
    itakura_exp_coordinate, bregmanDualDiag_psd, bregmanDualDiag_vacuum_zero, rfl, rfl, rfl⟩

end SarsBregmanDuality

end noncomputable section
