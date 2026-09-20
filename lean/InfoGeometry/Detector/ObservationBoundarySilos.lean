import Mathlib.Data.Real.Basic
import Mathlib.Tactic

namespace DetectorGeometry.ObservationBoundarySilos

section ObservationBoundary

def continuousLevel (x μ : ℝ) : ℝ := x * μ

def observedLevel (n : ℕ) (μ : ℝ) : ℝ := (n : ℝ) * μ

theorem observation_preserves_level_at_integer (n : ℕ) (μ : ℝ) :
    observedLevel n μ = continuousLevel n μ := by
  rfl

theorem first_observed_gap (μ : ℝ) :
    observedLevel 1 μ - observedLevel 0 μ = μ := by
  simp [observedLevel]

theorem first_observed_gap_positive (μ : ℝ) (hμ : 0 < μ) :
    0 < observedLevel 1 μ - observedLevel 0 μ := by
  rw [first_observed_gap]
  exact hμ

end ObservationBoundary

section SubstrateIndependence

noncomputable def informationMetric (s N : ℝ) : ℝ := s / N

noncomputable def squareRootPullback (s x : ℝ) : ℝ :=
  informationMetric s (x ^ 2) * (2 * x) ^ 2

theorem pullback_is_constant (s x : ℝ) (hx : x ≠ 0) :
    squareRootPullback s x = 4 * s := by
  simp only [squareRootPullback, informationMetric]
  have hx2 : x ^ 2 ≠ 0 := pow_ne_zero 2 hx
  field_simp [hx2]
  ring

theorem substrate_comparison (s₁ s₂ x : ℝ) (hx : x ≠ 0) :
    squareRootPullback s₁ x - squareRootPullback s₂ x = 4 * (s₁ - s₂) := by
  rw [pullback_is_constant s₁ x hx, pullback_is_constant s₂ x hx]
  ring

end SubstrateIndependence

section VacuumBoundary

theorem zero_boundary_intercept (a b : ℝ)
    (hzero : (fun x : ℝ => a * x + b) 0 = 0) : b = 0 := by
  simpa using hzero

end VacuumBoundary

section CausalPoset

inductive Archetype
  | observationBoundary
  | substrateIndependence
  deriving DecidableEq, Repr

def rank : Archetype → Nat
  | .observationBoundary => 145
  | .substrateIndependence => 146

def causallyPrecedes (a b : Archetype) : Prop := rank a ≤ rank b

theorem causal_refl (a : Archetype) : causallyPrecedes a a := le_rfl

theorem causal_trans {a b c : Archetype} :
    causallyPrecedes a b → causallyPrecedes b c → causallyPrecedes a c := by
  exact Nat.le_trans

theorem causal_antisymm {a b : Archetype} :
    causallyPrecedes a b → causallyPrecedes b a → a = b := by
  intro hab hba
  cases a <;> cases b <;> simp [causallyPrecedes, rank] at hab hba ⊢

theorem canonical_chain :
    causallyPrecedes .observationBoundary .substrateIndependence := by
  norm_num [causallyPrecedes, rank]

end CausalPoset

end DetectorGeometry.ObservationBoundarySilos
