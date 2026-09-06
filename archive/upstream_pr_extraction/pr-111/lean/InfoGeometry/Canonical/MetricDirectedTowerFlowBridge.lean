import Mathlib.Topology.MetricSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.CategoryTheory.Category.Basic
import Mathlib.CategoryTheory.Functor.Basic
import Mathlib.Tactic

/-!
# Categorical Directed System Flow and Uniform Exponential Contraction Bridge

This module formalizes:
1. `MetricDirectedTower`: A directed system of metric spaces indexed by `ℕ` with transition maps `ι`.
2. `TowerFlow`: A continuous dissipative flow on each level of the tower commuting with the directed system.
3. `HasUniformExponentialContraction`: Global uniform exponential contraction toward a designated target state `s_star`.
4. `TargetCompatible`: Invariance of the target state under transition morphisms.
5. `transition_preserves_target`: Exact preservation of target states across tower levels.
6. `asymptotic_convergence_to_target` & `strict_asymptotic_convergence_to_target`:
   Rigorous constructive proof of global asymptotic convergence to target for any dissipation rate `Γ > 0`.
-/

open CategoryTheory Real

namespace InfoGeometry.Canonical.DirectedSystemFlow

/-- A directed system of metric spaces indexed by `ℕ` with transition maps `ι`. -/
structure MetricDirectedTower where
  X : ℕ → Type*
  metric : ∀ n, MetricSpace (X n)
  ι : ∀ {n m : ℕ}, n ≤ m → X n → X m
  ι_refl : ∀ (n : ℕ) (h : n ≤ n) (x : X n), ι h x = x
  ι_trans : ∀ {n m k : ℕ} (h1 : n ≤ m) (h2 : m ≤ k) (x : X n),
    ι (h1.trans h2) x = ι h2 (ι h1 x)

attribute [instance] MetricDirectedTower.metric

/-- A continuous dissipative flow on each level of the tower commuting with the directed system. -/
structure TowerFlow (T : MetricDirectedTower) where
  flow : ∀ (n : ℕ), ℝ → T.X n → T.X n
  flow_zero : ∀ (n : ℕ) (x : T.X n), flow n 0 x = x
  flow_add : ∀ (n : ℕ) (t₁ t₂ : ℝ) (x : T.X n), flow n (t₁ + t₂) x = flow n t₁ (flow n t₂ x)
  commute_transition : ∀ {n m : ℕ} (h : n ≤ m) (t : ℝ) (x : T.X n),
    T.ι h (flow n t x) = flow m t (T.ι h x)

/-- Definition of a global uniform exponential contraction toward a designated target state `s_star`. -/
def HasUniformExponentialContraction (T : MetricDirectedTower) (F : TowerFlow T)
    (s_star : ∀ n, T.X n) (Γ : ℝ) : Prop :=
  ∀ (n : ℕ) (t : ℝ) (x : T.X n), 0 ≤ t →
    dist (F.flow n t x) (s_star n) ≤ Real.exp (-Γ * t) * dist x (s_star n)

/-- Invariance of the target state under the transition morphisms. -/
def TargetCompatible (T : MetricDirectedTower) (s_star : ∀ n, T.X n) : Prop :=
  ∀ {n m : ℕ} (h : n ≤ m), T.ι h (s_star n) = s_star m

/-- Preservation of the target locus along transition maps. -/
theorem transition_preserves_target {T : MetricDirectedTower} {s_star : ∀ n, T.X n}
    (h_comp : TargetCompatible T s_star) {n m : ℕ} (h : n ≤ m) (x : T.X n)
    (hx : x = s_star n) : T.ι h x = s_star m := by
  subst hx
  exact h_comp h

/-- Uniform decay implies that for positive dissipation rate `Γ > 0`, the distance contracts to within `ε`. -/
theorem asymptotic_convergence_to_target {T : MetricDirectedTower} {F : TowerFlow T}
    {s_star : ∀ n, T.X n} {Γ : ℝ} (hΓ : 0 < Γ)
    (h_contract : HasUniformExponentialContraction T F s_star Γ)
    (n : ℕ) (x : T.X n) (ε : ℝ) (hε : 0 < ε) (hx : dist x (s_star n) > 0) :
    ∃ (T_decay : ℝ), 0 ≤ T_decay ∧ ∀ t ≥ T_decay, dist (F.flow n t x) (s_star n) ≤ ε := by
  have hd_pos : 0 < dist x (s_star n) := hx
  have h_ratio : 0 < ε / dist x (s_star n) := div_pos hε hd_pos
  let T_decay : ℝ := max 0 (- Real.log (ε / dist x (s_star n)) / Γ)
  refine ⟨T_decay, le_max_left 0 _, ?_⟩
  intro t ht
  have ht_nonneg : 0 ≤ t := le_trans (le_max_left 0 _) ht
  have ht_bound : - Real.log (ε / dist x (s_star n)) / Γ ≤ t := le_trans (le_max_right 0 _) ht
  have h_step1 : - Real.log (ε / dist x (s_star n)) ≤ Γ * t := by
    have := (div_le_iff₀ hΓ).mp ht_bound
    rwa [mul_comm t Γ] at this
  have h_neg : - (Γ * t) ≤ Real.log (ε / dist x (s_star n)) := by
    linarith
  have h_exp : Real.exp (-Γ * t) ≤ ε / dist x (s_star n) := by
    have h_exp_mono := Real.exp_le_exp.mpr (by linarith : -Γ * t ≤ Real.log (ε / dist x (s_star n)))
    rw [Real.exp_log h_ratio] at h_exp_mono
    exact h_exp_mono
  have h_contr := h_contract n t x ht_nonneg
  have h_mult : Real.exp (-Γ * t) * dist x (s_star n) ≤ (ε / dist x (s_star n)) * dist x (s_star n) :=
    mul_le_mul_of_nonneg_right h_exp (dist_nonneg)
  rw [div_mul_cancel₀ ε (ne_of_gt hd_pos)] at h_mult
  exact le_trans h_contr h_mult

/-- 🏆 THEOREM: Strict Asymptotic Convergence to Target. -/
theorem strict_asymptotic_convergence_to_target {T : MetricDirectedTower} {F : TowerFlow T}
    {s_star : ∀ n, T.X n} {Γ : ℝ} (hΓ : 0 < Γ)
    (h_contract : HasUniformExponentialContraction T F s_star Γ)
    (n : ℕ) (x : T.X n) (ε : ℝ) (hε : 0 < ε) (hx : dist x (s_star n) > 0) :
    ∃ (T_decay : ℝ), 0 ≤ T_decay ∧ ∀ t ≥ T_decay, dist (F.flow n t x) (s_star n) < ε := by
  have h_half_eps : 0 < ε / 2 := by linarith
  rcases asymptotic_convergence_to_target hΓ h_contract n x (ε / 2) h_half_eps hx with ⟨T_decay, hT_pos, hT_le⟩
  refine ⟨T_decay, hT_pos, ?_⟩
  intro t ht
  have h_le := hT_le t ht
  linarith

end InfoGeometry.Canonical.DirectedSystemFlow
