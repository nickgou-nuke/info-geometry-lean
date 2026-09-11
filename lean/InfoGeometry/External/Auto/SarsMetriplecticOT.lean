import Mathlib.Tactic
import InfoGeometry.Algebra.FiniteSpinAlgebra

noncomputable section

namespace SarsMetriplecticOT

open Real

def modularSurprisal (r : ℝ) : ℝ := Real.exp r - 1 - r

def fenchelExpGapLogDensity (x u : ℝ) : ℝ :=
  Real.exp x + Real.exp u * u - Real.exp u - x * Real.exp u

def burgBregmanExp (x u : ℝ) : ℝ :=
  Real.exp (x - u) - (x - u) - 1

theorem modularSurprisal_nonneg (r : ℝ) :
    0 ≤ modularSurprisal r := by
  unfold modularSurprisal
  calc
    0 ≤ Real.exp r - (r + 1) := sub_nonneg.mpr (Real.add_one_le_exp r)
    _ = Real.exp r - 1 - r := by ring

theorem modularSurprisal_zero : modularSurprisal 0 = 0 := by
  norm_num [modularSurprisal]

theorem fenchel_gap_factor (x u : ℝ) :
    fenchelExpGapLogDensity x u = Real.exp u * modularSurprisal (x - u) := by
  unfold fenchelExpGapLogDensity modularSurprisal
  have h : Real.exp x = Real.exp u * Real.exp (x - u) := by
    rw [Real.exp_sub]
    field_simp [Real.exp_ne_zero u]
  rw [h]
  ring

theorem fenchel_gap_nonneg (x u : ℝ) :
    0 ≤ fenchelExpGapLogDensity x u := by
  rw [fenchel_gap_factor]
  exact mul_nonneg (le_of_lt (Real.exp_pos u)) (modularSurprisal_nonneg (x - u))

theorem burg_equals_modular (x u : ℝ) :
    burgBregmanExp x u = modularSurprisal (x - u) := by
  unfold burgBregmanExp modularSurprisal
  ring

theorem burg_nonneg (x u : ℝ) :
    0 ≤ burgBregmanExp x u := by
  rw [burg_equals_modular]
  exact modularSurprisal_nonneg (x - u)

theorem fenchel_vacuum_zero : fenchelExpGapLogDensity 0 0 = 0 := by
  rw [fenchel_gap_factor]
  norm_num [modularSurprisal]

theorem burg_vacuum_zero : burgBregmanExp 0 0 = 0 := by
  rw [burg_equals_modular, sub_self, modularSurprisal_zero]

structure MetriplecticSystem (Obs : Type*) where
  poisson : Obs → Obs → ℝ
  metric : Obs → Obs → ℝ
  H : Obs
  S : Obs
  poisson_skew : ∀ A B, poisson A B = - poisson B A
  metric_symm : ∀ A B, metric A B = metric B A
  metric_psd : ∀ A, 0 ≤ metric A A
  energy_metric_degenerate : ∀ A, metric H A = 0
  entropy_poisson_degenerate : ∀ A, poisson S A = 0

theorem metriplectic_energy_metric_zero {Obs : Type*}
    (M : MetriplecticSystem Obs) (A : Obs) :
    M.metric M.H A = 0 := M.energy_metric_degenerate A

theorem metriplectic_entropy_poisson_zero {Obs : Type*}
    (M : MetriplecticSystem Obs) (A : Obs) :
    M.poisson M.S A = 0 := M.entropy_poisson_degenerate A

theorem metriplectic_entropy_production_nonneg {Obs : Type*}
    (M : MetriplecticSystem Obs) :
    0 ≤ M.metric M.S M.S := M.metric_psd M.S

inductive FlowConcept where
  | Metriplectic_Evolution
  | WeylSystem
  | Wasserstein_Gradient_Flow
  | Itakura_Saito_Divergence
  | Legendre_Fenchel_Duality
  deriving DecidableEq, Repr

inductive FlowEdge where
  | symplectic_part
  | metric_part
  | minimizes_distortion
  | generated_by
  | stabilizes_vacuum
  deriving DecidableEq, Repr

def edgeHolds : FlowConcept → FlowEdge → FlowConcept → Bool
  | FlowConcept.Metriplectic_Evolution, FlowEdge.symplectic_part, FlowConcept.WeylSystem => true
  | FlowConcept.Metriplectic_Evolution, FlowEdge.metric_part, FlowConcept.Wasserstein_Gradient_Flow => true
  | FlowConcept.Wasserstein_Gradient_Flow, FlowEdge.minimizes_distortion, FlowConcept.Itakura_Saito_Divergence => true
  | FlowConcept.Itakura_Saito_Divergence, FlowEdge.generated_by, FlowConcept.Legendre_Fenchel_Duality => true
  | FlowConcept.Legendre_Fenchel_Duality, FlowEdge.stabilizes_vacuum, FlowConcept.Metriplectic_Evolution => true
  | _, _, _ => false

end SarsMetriplecticOT

end noncomputable section
