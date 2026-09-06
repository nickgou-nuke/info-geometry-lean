import Mathlib

noncomputable section

namespace SarsItakuraModular

open Real

def modularSurprisal (x : ℝ) : ℝ := Real.exp x - 1 - x

def itakuraSaitoToOne (z : ℝ) : ℝ := z - Real.log z - 1

theorem itakura_exp_coordinate (x : ℝ) :
    itakuraSaitoToOne (Real.exp x) = modularSurprisal x := by
  unfold itakuraSaitoToOne modularSurprisal
  rw [Real.log_exp]
  ring

theorem modularSurprisal_nonneg (x : ℝ) :
    0 ≤ modularSurprisal x := by
  unfold modularSurprisal
  calc
    0 ≤ Real.exp x - (x + 1) := sub_nonneg.mpr (Real.add_one_le_exp x)
    _ = Real.exp x - 1 - x := by ring

theorem itakura_exp_nonneg (x : ℝ) :
    0 ≤ itakuraSaitoToOne (Real.exp x) := by
  rw [itakura_exp_coordinate]
  exact modularSurprisal_nonneg x

theorem modularSurprisal_zero : modularSurprisal 0 = 0 := by
  norm_num [modularSurprisal]

theorem itakura_exp_zero : itakuraSaitoToOne (Real.exp 0) = 0 := by
  rw [itakura_exp_coordinate, modularSurprisal_zero]

def diag2 (a b : ℝ) : Matrix (Fin 2) (Fin 2) ℝ := !![a, 0; 0, b]

def quad2 (A : Matrix (Fin 2) (Fin 2) ℝ) (v : Fin 2 → ℝ) : ℝ :=
  v 0 * (A 0 0 * v 0 + A 0 1 * v 1) + v 1 * (A 1 0 * v 0 + A 1 1 * v 1)

def IsPSD2 (A : Matrix (Fin 2) (Fin 2) ℝ) : Prop := ∀ v : Fin 2 → ℝ, 0 ≤ quad2 A v

theorem diag2_psd_of_nonneg {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) : IsPSD2 (diag2 a b) := by
  intro v
  unfold quad2 diag2
  simp
  have hv0 : 0 ≤ (v 0) * (v 0) := mul_self_nonneg (v 0)
  have hv1 : 0 ≤ (v 1) * (v 1) := mul_self_nonneg (v 1)
  have h0 : 0 ≤ a * ((v 0) * (v 0)) := mul_nonneg ha hv0
  have h1 : 0 ≤ b * ((v 1) * (v 1)) := mul_nonneg hb hv1
  have hsum : 0 ≤ a * ((v 0) * (v 0)) + b * ((v 1) * (v 1)) := add_nonneg h0 h1
  rw [← mul_assoc (v 0) a (v 0), mul_comm (v 0) a, mul_assoc a (v 0) (v 0),
    ← mul_assoc (v 1) b (v 1), mul_comm (v 1) b, mul_assoc b (v 1) (v 1)]
  exact hsum

def modularItakuraDiag (x0 x1 : ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  diag2 (itakuraSaitoToOne (Real.exp x0)) (itakuraSaitoToOne (Real.exp x1))

theorem modularItakuraDiag_psd (x0 x1 : ℝ) :
    IsPSD2 (modularItakuraDiag x0 x1) := by
  apply diag2_psd_of_nonneg
  · apply itakura_exp_nonneg
  · apply itakura_exp_nonneg

theorem modularItakuraDiag_vacuum_zero : modularItakuraDiag 0 0 = 0 := by
  have h : itakuraSaitoToOne 1 = 0 := by norm_num [itakuraSaitoToOne]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [modularItakuraDiag, diag2, h]

inductive InfoGeometryEdge where
  | exponential_coordinate_transform
  | bregman_dual
  | stabilizes_modular_flow
  deriving DecidableEq, Repr

def edgeName : InfoGeometryEdge → String
  | InfoGeometryEdge.exponential_coordinate_transform => "exp_coordinate_transform"
  | InfoGeometryEdge.bregman_dual => "bregman_dual"
  | InfoGeometryEdge.stabilizes_modular_flow => "stabilizes_modular_flow"

end SarsItakuraModular

end noncomputable section
