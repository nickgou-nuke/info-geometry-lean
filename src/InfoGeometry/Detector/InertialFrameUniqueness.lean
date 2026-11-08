/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/

import Mathlib.Data.Real.Basic
import Mathlib.Tactic
import InfoGeometry.OperatorAlgebra.PeirceSpine.Tetraktys

namespace DetectorGeometry.InertialFrameUniqueness

section GeneralizedConnection

noncomputable def christoffelPower (p x : ℝ) : ℝ := (p - 2) / (2 * x)

noncomputable def christoffelAlpha (α x : ℝ) : ℝ :=
  (1 - 2 * α) / (2 * α * x)

theorem power_alpha_equivalence (α x : ℝ) (hα : α ≠ 0) (hx : x ≠ 0) :
    christoffelPower (1 / α) x = christoffelAlpha α x := by
  simp only [christoffelPower, christoffelAlpha]
  field_simp [hα, hx]

end GeneralizedConnection

section UniqueInertial

theorem unique_inertial_power (p : ℝ) :
    (∀ x : ℝ, 0 < x → christoffelPower p x = 0) ↔ p = 2 := by
  constructor
  · intro h
    have h1 := h 1 zero_lt_one
    simp only [christoffelPower] at h1
    have hn : p - 2 = 0 := (div_eq_zero_iff.mp h1).resolve_right (by norm_num)
    linarith
  · intro hp x hx
    simp [christoffelPower, hp]

theorem unique_inertial_alpha (α : ℝ) (hα : 0 < α) :
    (∀ x : ℝ, 0 < x → christoffelAlpha α x = 0) ↔ α = 1 / 2 := by
  constructor
  · intro h
    have h1 := h 1 zero_lt_one
    simp only [christoffelAlpha] at h1
    have hden : 2 * α * 1 ≠ 0 := by positivity
    have hn : 1 - 2 * α = 0 := (div_eq_zero_iff.mp h1).resolve_right hden
    linarith
  · intro ha x hx
    simp [christoffelAlpha, ha]

end UniqueInertial

section Acceleration

def accelerationFactor (α : ℝ) : ℝ := 2 * α * (2 * α - 1)

theorem acceleration_zero_iff (α : ℝ) (hα : 0 < α) :
    accelerationFactor α = 0 ↔ α = 1 / 2 := by
  simp only [accelerationFactor]
  have hne : 2 * α ≠ 0 := by positivity
  constructor
  · intro h
    have hsecond : 2 * α - 1 = 0 :=
      (mul_eq_zero.mp h).resolve_left hne
    linarith
  · intro h
    rw [h]
    norm_num

theorem square_root_is_inertial :
    (∀ x : ℝ, 0 < x → christoffelAlpha (1 / 2) x = 0) ∧
    accelerationFactor (1 / 2) = 0 := by
  refine ⟨(unique_inertial_alpha (1 / 2) (by norm_num)).mpr rfl, ?_⟩
  norm_num [accelerationFactor]

end Acceleration

section CausalPoset

inductive Archetype
  | powerChart
  | metricPullback
  | connection
  | uniqueInertial
  | accelerationAnnihilation
  deriving DecidableEq, Repr

def rank : Archetype → Nat
  | .powerChart => 185
  | .metricPullback => 186
  | .connection => 187
  | .uniqueInertial => 188
  | .accelerationAnnihilation => 189

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
    causallyPrecedes .powerChart .metricPullback ∧
    causallyPrecedes .metricPullback .connection ∧
    causallyPrecedes .connection .uniqueInertial ∧
    causallyPrecedes .uniqueInertial .accelerationAnnihilation := by
  norm_num [causallyPrecedes, rank]

end CausalPoset

section NonCommutativeOperatorRealization

open InfoGeometry.OperatorAlgebra.PeirceSpine

variable {B : Type*} [Ring B]

/-- Non-commutative operator realization mapping each `InertialFrameUniqueness.Archetype`
node to its canonical Peirce operator in `[Ring B]`. -/
def inertialFrameOperator (P A C X : B) : Archetype → B
  | .powerChart => genPhi P A C
  | .metricPullback => genPhi P A C * genPhi P A C
  | .connection => InfoGeometry.OperatorAlgebra.PeirceSpine.comm (genV P A C) (genPhi P A C)
  | .uniqueInertial => invS P * evenGrade P X * invS P
  | .accelerationAnnihilation => conePlus P A * conePlus P A

/-- **Theorem (Non-Commutative Operator Inertial-Frame Identities over `[Ring B]`)**:
For any idempotent `P * P = P` in a non-commutative ring `[Ring B]`, the quadratic
metric pullback satisfies `Φ² = V`, the connection commutator `[V, Φ] = 0` vanishes,
the inertial even-grade frame is fixed by `S`, and the null-cone acceleration `a₊² = 0`
vanishes identically. -/
theorem inertialFrame_operator_identities {P : B} (hP : P * P = P) (A C X : B) :
    inertialFrameOperator P A C X .metricPullback = genV P A C ∧
    inertialFrameOperator P A C X .connection = 0 ∧
    inertialFrameOperator P A C X .uniqueInertial = evenGrade P X ∧
    inertialFrameOperator P A C X .accelerationAnnihilation = 0 := by
  dsimp only [inertialFrameOperator]
  refine ⟨?_, ?_, ?_, ?_⟩ <;> peirce_nf hP

end NonCommutativeOperatorRealization

end DetectorGeometry.InertialFrameUniqueness
