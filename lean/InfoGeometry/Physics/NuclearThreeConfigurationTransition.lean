/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Physics.NuclearThreeConfiguration
import InfoGeometry.Physics.NuclearRealKreinObservables
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith

/-!
# A normalized operator readout of the three-configuration model

The real probe is the actual continuous operator `diag(kappa,-kappa,0)`.
Its dark and bright external states are reconstructed through the existing
graph maps at two distinct energy arguments. The closed strength formula is
derived from the owned effective operator and both induced Gram norms.
No nuclear multipole assignment or angular-momentum reduction is inferred.
-/

noncomputable section

namespace InfoGeometry.Physics.NuclearThreeConfigurationTransition

open scoped Matrix
open InfoGeometry.Physics.NuclearThreeConfiguration
open InfoGeometry.Physics.NuclearEffectiveObservables

def darkModel : ModelSpace := WithLp.toLp 2 ![1, -1]
def brightModel : ModelSpace := WithLp.toLp 2 ![1, 1]

/-- The calibrated real probe acts on the actual configuration carrier. -/
def probe (κ : ℝ) : ConfigurationSpace →L[ℝ] ConfigurationSpace :=
  matrixMap !![κ, 0, 0; 0, -κ, 0; 0, 0, 0]

@[simp] theorem probe_apply (κ : ℝ) (x : ConfigurationSpace) :
    probe κ x = WithLp.toLp 2 ![κ * x 0, -κ * x 1, 0] := by
  ext i
  fin_cases i <;> simp [probe, Matrix.mulVec, dotProduct, Fin.sum_univ_succ]

theorem probe_adjoint (κ : ℝ) : (probe κ).adjoint = probe κ := by
  rw [probe, matrixMap_adjoint]
  congr 1
  ext i j
  fin_cases i <;> fin_cases j <;> rfl

theorem darkModel_ne_zero : darkModel ≠ 0 := by
  intro h
  have h0 := congrArg (fun x : ModelSpace => x 0) h
  norm_num [darkModel] at h0

theorem brightModel_ne_zero : brightModel ≠ 0 := by
  intro h
  have h0 := congrArg (fun x : ModelSpace => x 0) h
  norm_num [brightModel] at h0

@[simp] theorem graphMap_dark (c g E : ℝ) :
    graphMap c g E darkModel = WithLp.toLp 2 ![1, -1, 0] := by
  simp [graphMap_apply, darkModel]

@[simp] theorem graphMap_bright (c g E : ℝ) :
    graphMap c g E brightModel = WithLp.toLp 2 ![1, 1, 2 * g / (E - c)] := by
  ext i
  fin_cases i <;> simp [graphMap_apply, brightModel] <;> ring

/-- The antisymmetric retained vector decouples from the third configuration. -/
theorem dark_eigen_equation (a c g : ℝ) :
    hamiltonian a c g (graphMap c g a darkModel) =
      a • graphMap c g a darkModel := by
  ext i
  fin_cases i <;> simp [hamiltonian_apply, darkModel]

/-- The bright eigen-equation is an equation of full reconstructed states. -/
theorem bright_eigen_equation_iff (a c g E : ℝ) (hE : E ≠ c) :
    hamiltonian a c g (graphMap c g E brightModel) =
        E • graphMap c g E brightModel ↔
      (a - E) * (c - E) = 2 * g ^ 2 := by
  have hd : E - c ≠ 0 := sub_ne_zero.mpr hE
  constructor
  · intro h
    have h0 := congrArg (fun x : ConfigurationSpace => x 0) h
    simp [hamiltonian_apply, brightModel] at h0
    field_simp [hd] at h0
    nlinarith
  · intro h
    ext i
    fin_cases i <;> simp [hamiltonian_apply, brightModel] <;>
      field_simp [hd] <;> nlinarith [h]

theorem metricWeight_dark (c g E : ℝ) :
    metricWeight (graphMap c g E) darkModel = 2 := by
  rw [metricWeight_eq_norm_sq, graphMap_dark, EuclideanSpace.real_norm_sq_eq]
  norm_num [Fin.sum_univ_succ]

theorem metricWeight_bright (c g E : ℝ) :
    metricWeight (graphMap c g E) brightModel =
      2 + 4 * g ^ 2 / (E - c) ^ 2 := by
  rw [metricWeight_eq_norm_sq, graphMap_bright, EuclideanSpace.real_norm_sq_eq]
  simp [Fin.sum_univ_succ, div_pow, mul_pow] <;> ring

theorem metricWeight_bright_pos (c g E : ℝ) :
    0 < metricWeight (graphMap c g E) brightModel :=
  metricWeight_pos _ (graphMap_injective c g E) brightModel_ne_zero

theorem probe_graph_bright (a c g E κ : ℝ) :
    probe κ (graphMap c g E brightModel) = κ • graphMap c g a darkModel := by
  ext i
  fin_cases i <;> simp [probe_apply, darkModel, brightModel]

/-- The observable sandwich is evaluated with the two graph embeddings. -/
theorem effective_matrix_element (a c g E κ : ℝ) :
    inner ℝ brightModel
        (effectiveOperator (graphMap c g a) (graphMap c g E) (probe κ) darkModel) =
      2 * κ := by
  rw [inner_effectiveOperator,
    ← (probe κ).adjoint_inner_left (graphMap c g a darkModel)
      (graphMap c g E brightModel),
    probe_adjoint, probe_graph_bright a,
    real_inner_smul_left, real_inner_self_eq_norm_sq,
    ← metricWeight_eq_norm_sq, metricWeight_dark]
  ring

/-- This readout is defined by normalized states and an actual operator,
rather than by the rational formula derived below. -/
def measuredStrength (a c g E κ : ℝ) : ℝ :=
  (inner ℝ (normalizedState (graphMap c g E) brightModel)
    (probe κ (normalizedState (graphMap c g a) darkModel))) ^ 2

theorem measuredStrength_eq_gram_ratio (a c g E κ : ℝ) :
    measuredStrength a c g E κ =
      (2 * κ) ^ 2 / ((2 + 4 * g ^ 2 / (E - c) ^ 2) * 2) := by
  have h := normalized_transition_strength (𝕜 := ℝ)
    (graphMap c g a) (graphMap c g E) (probe κ) darkModel brightModel
  simpa only [measuredStrength, Real.norm_eq_abs, sq_abs, effective_matrix_element,
    metricWeight_dark, metricWeight_bright] using h

/-- The measured scalar law follows from the normalized operator readout. -/
theorem measuredStrength_closed_form (a c g E κ : ℝ) (hE : E ≠ c) :
    measuredStrength a c g E κ =
      κ ^ 2 * (E - c) ^ 2 / ((E - c) ^ 2 + 2 * g ^ 2) := by
  have hd : E - c ≠ 0 := sub_ne_zero.mpr hE
  have hd2 : 0 < (E - c) ^ 2 := sq_pos_of_ne_zero hd
  have hden : (E - c) ^ 2 + 2 * g ^ 2 ≠ 0 := by
    nlinarith [sq_nonneg g]
  have hweight : 2 + 4 * g ^ 2 / (E - c) ^ 2 ≠ 0 := by
    rw [← metricWeight_bright]
    exact ne_of_gt (metricWeight_bright_pos c g E)
  rw [measuredStrength_eq_gram_ratio]
  field_simp [hd, hden, hweight] <;> ring

end InfoGeometry.Physics.NuclearThreeConfigurationTransition
