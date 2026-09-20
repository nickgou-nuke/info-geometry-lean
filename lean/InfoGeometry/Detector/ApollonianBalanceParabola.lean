import Mathlib.Data.Real.Basic
import Mathlib.Tactic

namespace DetectorGeometry.ApollonianBalanceParabola

section Parabola

def singleObserved (N₀ K ε : ℝ) : ℝ := N₀ * ε * (1 - K * ε)

def coincidenceRate (N₀ K ε : ℝ) : ℝ := N₀ * K * ε ^ 2

theorem pole_one (N₀ K : ℝ) : singleObserved N₀ K 0 = 0 := by
  simp [singleObserved]

noncomputable def criticalEfficiency (K : ℝ) : ℝ := 1 / K

theorem pole_two (N₀ K : ℝ) (hK : K ≠ 0) :
    singleObserved N₀ K (criticalEfficiency K) = 0 := by
  simp only [singleObserved, criticalEfficiency]
  rw [mul_one_div_cancel hK, sub_self, mul_zero]

noncomputable def balancePoint (K : ℝ) : ℝ := 1 / (2 * K)

theorem balance_midpoint (K : ℝ) (hK : K ≠ 0) :
    balancePoint K = (1 / 2) * criticalEfficiency K := by
  simp only [balancePoint, criticalEfficiency]
  field_simp [hK]

theorem vertex_form (N₀ K ε : ℝ) (hK : K ≠ 0) :
    singleObserved N₀ K ε = N₀ / (4 * K) -
      N₀ * K * (ε - balancePoint K) ^ 2 := by
  simp only [singleObserved, balancePoint]
  field_simp [hK]
  ring

theorem equipartition_at_balance (N₀ K : ℝ) (hK : K ≠ 0) :
    singleObserved N₀ K (balancePoint K) =
        coincidenceRate N₀ K (balancePoint K) ∧
    singleObserved N₀ K (balancePoint K) = N₀ / (4 * K) := by
  constructor <;> simp only [singleObserved, coincidenceRate, balancePoint]
  · field_simp [hK]
    ring
  · field_simp [hK]
    ring

end Parabola

section CrossRatio

noncomputable def crossRatio (K ε : ℝ) : ℝ := (K * ε) / (1 - K * ε)

theorem crossRatio_at_balance (K : ℝ) (hK : K ≠ 0) :
    crossRatio K (balancePoint K) = 1 := by
  simp only [crossRatio, balancePoint]
  field_simp [hK]
  ring

theorem crossRatio_count_ratio (N₀ K ε : ℝ)
    (hsingle : singleObserved N₀ K ε ≠ 0) :
    crossRatio K ε = coincidenceRate N₀ K ε / singleObserved N₀ K ε := by
  have hN₀ : N₀ ≠ 0 := by
    intro h
    apply hsingle
    simp [singleObserved, h]
  have hε : ε ≠ 0 := by
    intro h
    apply hsingle
    simp [singleObserved, h]
  have hfactor : 1 - K * ε ≠ 0 := by
    intro h
    apply hsingle
    simp [singleObserved, h]
  simp only [crossRatio, coincidenceRate, singleObserved]
  field_simp [hN₀, hε, hfactor]

end CrossRatio

section CausalPoset

inductive Archetype
  | vacuumPole
  | summingPole
  | equipartitionPeak
  | crossRatio
  deriving DecidableEq, Repr

def rank : Archetype → Nat
  | .vacuumPole => 152
  | .summingPole => 153
  | .equipartitionPeak => 154
  | .crossRatio => 155

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
    causallyPrecedes .vacuumPole .summingPole ∧
    causallyPrecedes .summingPole .equipartitionPeak ∧
    causallyPrecedes .equipartitionPeak .crossRatio := by
  norm_num [causallyPrecedes, rank]

end CausalPoset

end DetectorGeometry.ApollonianBalanceParabola
