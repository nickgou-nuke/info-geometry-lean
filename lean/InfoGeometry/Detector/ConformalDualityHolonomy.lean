import Mathlib.Data.Real.Basic
import Mathlib.Tactic

namespace DetectorGeometry.ConformalDualityHolonomy

section FunctionalDuality

def normSingles (x : ℝ) : ℝ := x * (1 - x)

def reflectionMap (x : ℝ) : ℝ := 1 - x

theorem reflection_involution (x : ℝ) :
    reflectionMap (reflectionMap x) = x := by
  simp [reflectionMap]

theorem normSingles_reflection (x : ℝ) :
    normSingles (reflectionMap x) = normSingles x := by
  simp [normSingles, reflectionMap]
  ring

theorem reflection_fixed_iff (x : ℝ) :
    reflectionMap x = x ↔ x = 1 / 2 := by
  simp only [reflectionMap]
  constructor
  · intro h
    linarith
  · intro h
    rw [h]
    norm_num

theorem normSingles_vertex_form (x : ℝ) :
    normSingles x = 1 / 4 - (x - 1 / 2) ^ 2 := by
  simp [normSingles]
  ring

end FunctionalDuality

section BaselCapacity

noncomputable def normPrimitive (x : ℝ) : ℝ := x ^ 2 / 2 - x ^ 3 / 3

theorem normalized_capacity : normPrimitive 1 - normPrimitive 0 = 1 / 6 := by
  norm_num [normPrimitive]

noncomputable def baselCapacityConstant : ℝ := 1 / 6

theorem capacity_is_basel_constant :
    normPrimitive 1 - normPrimitive 0 = baselCapacityConstant := by
  exact normalized_capacity

end BaselCapacity

section PhysicalDuality

def physicalSingles (k ε : ℝ) : ℝ := ε * (1 - k * ε)

noncomputable def physicalDual (k ε : ℝ) : ℝ := 1 / k - ε

theorem physicalSingles_reflection (k ε : ℝ) (hk : k ≠ 0) :
    physicalSingles k (physicalDual k ε) = physicalSingles k ε := by
  simp only [physicalSingles, physicalDual]
  have hcancel : k * (1 / k) = 1 := mul_one_div_cancel hk
  calc
    (1 / k - ε) * (1 - k * (1 / k - ε)) =
        (1 / k - ε) * (k * ε) := by rw [show 1 - k * (1 / k - ε) = k * ε by
          calc
            1 - k * (1 / k - ε) = 1 - (k * (1 / k) - k * ε) := by ring
            _ = 1 - (1 - k * ε) := by rw [hcancel]
            _ = k * ε := by ring]
    _ = ε * (1 - k * ε) := by
      have hcancel' : (1 / k) * k = 1 := one_div_mul_cancel hk
      calc
        (1 / k - ε) * (k * ε) = (1 / k * k) * ε - k * ε ^ 2 := by ring
        _ = 1 * ε - k * ε ^ 2 := by rw [hcancel']
        _ = ε * (1 - k * ε) := by ring

theorem physicalDual_fixed_iff (k ε : ℝ) (hk : k ≠ 0) :
    physicalDual k ε = ε ↔ ε = 1 / (2 * k) := by
  simp only [physicalDual]
  constructor
  · intro h
    have htwice : 2 * ε = 1 / k := by linarith
    calc
      ε = (2 * ε) / 2 := by ring
      _ = (1 / k) / 2 := by rw [htwice]
      _ = 1 / (2 * k) := by ring
  · intro h
    rw [h]
    field_simp [hk]
    ring

theorem vertex_deviation (k δ : ℝ) (hk : k ≠ 0) :
    physicalSingles k (1 / (2 * k) + δ) =
      1 / (4 * k) - k * δ ^ 2 := by
  dsimp [physicalSingles]
  field_simp [hk]
  ring

end PhysicalDuality

section CausalPoset

inductive Archetype
  | reflectionDuality
  | criticalFixedPoint
  | baselCapacity
  | physicalDuality
  | selfDualManifold
  deriving DecidableEq, Repr

def rank : Archetype → Nat
  | .reflectionDuality => 165
  | .criticalFixedPoint => 166
  | .baselCapacity => 167
  | .physicalDuality => 168
  | .selfDualManifold => 169

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
    causallyPrecedes .reflectionDuality .criticalFixedPoint ∧
    causallyPrecedes .criticalFixedPoint .baselCapacity ∧
    causallyPrecedes .baselCapacity .physicalDuality ∧
    causallyPrecedes .physicalDuality .selfDualManifold := by
  norm_num [causallyPrecedes, rank]

end CausalPoset

end DetectorGeometry.ConformalDualityHolonomy
