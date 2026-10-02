import Mathlib.Data.Real.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Data.Matrix.Basic
import Mathlib.Tactic

namespace InfoGeometry.Computation.BayesianTuringCantor

open Real Matrix

section TuringTape

def CantorTape := ℕ → Bool

structure CylinderObservation where
  depth : ℕ
  pattern : Fin depth → Bool

def satisfies_cylinder (tape : CantorTape) (obs : CylinderObservation) : Prop :=
  ∀ i : Fin obs.depth, tape i.val = obs.pattern i

noncomputable def uniform_prior_measure (obs : CylinderObservation) : ℝ :=
  (1 / 2) ^ obs.depth

end TuringTape

section BayesianUpdate

variable (P Q : CylinderObservation → ℝ)

noncomputable def log_RN_derivative (P Q : CylinderObservation → ℝ) (obs : CylinderObservation) : ℝ :=
  Real.log (P obs / Q obs)

theorem log_RN_increment_cocycle
    (P Q R : CylinderObservation → ℝ) (obs : CylinderObservation)
    (hP : 0 < P obs) (hQ : 0 < Q obs) (hR : 0 < R obs) :
    log_RN_derivative P R obs = log_RN_derivative P Q obs + log_RN_derivative Q R obs := by
  dsimp [log_RN_derivative]
  have h_add : Real.log (P obs / Q obs) + Real.log (Q obs / R obs) = 
      Real.log ((P obs / Q obs) * (Q obs / R obs)) := by
    rw [← Real.log_mul (div_ne_zero (ne_of_gt hP) (ne_of_gt hQ)) (div_ne_zero (ne_of_gt hQ) (ne_of_gt hR))]
  rw [h_add]
  have h_cancel : (P obs / Q obs) * (Q obs / R obs) = P obs / R obs := by
    have hQ_ne : Q obs ≠ 0 := ne_of_gt hQ
    calc
      (P obs / Q obs) * (Q obs / R obs) = (P obs * Q obs) / (Q obs * R obs) := by ring
      _ = (Q obs * P obs) / (Q obs * R obs) := by ring
      _ = P obs / R obs := mul_div_mul_left (P obs) (R obs) hQ_ne
  rw [h_cancel]

end BayesianUpdate

section OrthogonalityToDefect

def nilpotent_ghost (ε : ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  !![0, ε; 0, 0]

def bayesian_dilation (β : ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  !![β, 0; 0, β]

def matrix_inner_product (A B : Matrix (Fin 2) (Fin 2) ℝ) : ℝ :=
  Matrix.trace (Aᵀ * B)

theorem bayesian_update_is_orthogonal_to_defect (β ε : ℝ) :
    matrix_inner_product (bayesian_dilation β) (nilpotent_ghost ε) = 0 := by
  dsimp [matrix_inner_product, bayesian_dilation, nilpotent_ghost, Matrix.trace, Matrix.transpose_apply, Matrix.mul_apply]
  simp [Fin.sum_univ_succ]

theorem learning_commutes_with_defect (β ε : ℝ) :
    bayesian_dilation β * nilpotent_ghost ε = nilpotent_ghost ε * bayesian_dilation β := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [bayesian_dilation, nilpotent_ghost, Matrix.mul_apply, Fin.sum_univ_succ] <;> ring

end OrthogonalityToDefect

end InfoGeometry.Computation.BayesianTuringCantor
