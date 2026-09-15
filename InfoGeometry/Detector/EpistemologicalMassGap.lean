import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Data.Real.Basic
import Mathlib.Tactic

namespace DetectorGeometry.EpistemologicalMassGap

section MassGap

def energyLevel (n : ℕ) (μ : ℝ) : ℝ := (n : ℝ) * μ

theorem first_gap (μ : ℝ) :
    energyLevel 1 μ - energyLevel 0 μ = μ := by
  simp [energyLevel]

theorem mass_gap_positive (μ : ℝ) (hμ : 0 < μ) :
    0 < energyLevel 1 μ - energyLevel 0 μ := by
  rw [first_gap]
  exact hμ

end MassGap

section Transmutation

noncomputable def dynamicalMassGap (k W : ℝ) : ℝ := Real.sqrt (k * W)

noncomputable def canonicalSlope (k W : ℝ) : ℝ :=
  (dynamicalMassGap k W)⁻¹

theorem transmutation_properties (k W : ℝ) (hk : 0 < k) (hW : 0 < W) :
    0 < dynamicalMassGap k W ∧
    0 < canonicalSlope k W ∧
    dynamicalMassGap k W * canonicalSlope k W = 1 := by
  have hkw : 0 < k * W := mul_pos hk hW
  have hμ : 0 < Real.sqrt (k * W) := Real.sqrt_pos.mpr hkw
  have hμne : Real.sqrt (k * W) ≠ 0 := ne_of_gt hμ
  refine ⟨hμ, inv_pos.mpr hμ, ?_⟩
  simp [dynamicalMassGap, canonicalSlope, hμne]

end Transmutation

section MetricFlattening

noncomputable def fisherMetric (s N : ℝ) : ℝ := s / N

noncomputable def pullbackMetric (s x : ℝ) : ℝ := fisherMetric s (x ^ 2) * (2 * x) ^ 2

theorem metric_flattening (s x : ℝ) (hx : x ≠ 0) :
    pullbackMetric s x = 4 * s := by
  simp only [pullbackMetric, fisherMetric]
  have hx2 : x ^ 2 ≠ 0 := pow_ne_zero 2 hx
  field_simp [hx2]
  ring

end MetricFlattening

section Vacuum

theorem zero_intercept (a b : ℝ) (hvac : (fun x : ℝ => a * x + b) 0 = 0) :
    b = 0 := by
  simpa using hvac

theorem unified_invariant (s k W a b : ℝ) (hs : 0 < s) (hk : 0 < k)
    (hW : 0 < W) (hvac : (fun x : ℝ => a * x + b) 0 = 0) :
    0 < dynamicalMassGap k W ∧
    (∀ x, x ≠ 0 → pullbackMetric s x = 4 * s) ∧
    b = 0 := by
  have htrans := transmutation_properties k W hk hW
  refine ⟨htrans.1, ?_, zero_intercept a b hvac⟩
  intro x hx
  exact metric_flattening s x hx

end Vacuum

section CausalPoset

inductive Archetype
  | scaleFreeField
  | measurementGap
  | dimensionalTransmutation
  | substrateMetric
  | susyVacuum
  deriving DecidableEq, Repr

def rank : Archetype → Nat
  | .scaleFreeField => 147
  | .measurementGap => 148
  | .dimensionalTransmutation => 149
  | .substrateMetric => 150
  | .susyVacuum => 151

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
    causallyPrecedes .scaleFreeField .measurementGap ∧
    causallyPrecedes .measurementGap .dimensionalTransmutation ∧
    causallyPrecedes .dimensionalTransmutation .substrateMetric ∧
    causallyPrecedes .substrateMetric .susyVacuum := by
  norm_num [causallyPrecedes, rank]

end CausalPoset

end DetectorGeometry.EpistemologicalMassGap
