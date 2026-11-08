/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/

import Mathlib.Data.Real.Basic
import Mathlib.Tactic
import InfoGeometry.OperatorAlgebra.PeirceSpine.Tetraktys

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

section NonCommutativeOperatorRealization

open InfoGeometry.OperatorAlgebra.PeirceSpine

variable {B : Type*} [Ring B]

/-- Non-commutative operator realization mapping each `ObservationBoundarySilos.Archetype`
node to its canonical Peirce operator in `[Ring B]`. -/
def observationBoundaryOperator (P A C X : B) : Archetype → B
  | .observationBoundary => peirce11 P X * peirce00 P X
  | .substrateIndependence => InfoGeometry.OperatorAlgebra.PeirceSpine.comm (genV P A C) (genPhi P A C)

/-- **Theorem (Non-Commutative Operator Boundary Silo Identities over `[Ring B]`)**:
For any idempotent `P * P = P` in a non-commutative ring `[Ring B]`, the two diagonal
Peirce silos `P X P` and `(1 - P) X (1 - P)` are mutually orthogonal and the quadratic
substrate operator `V = Φ²` commutes with `Φ`. -/
theorem observationBoundary_operator_identities {P : B} (hP : P * P = P) (A C X : B) :
    observationBoundaryOperator P A C X .observationBoundary = 0 ∧
    peirce00 P X * peirce11 P X = 0 ∧
    observationBoundaryOperator P A C X .substrateIndependence = 0 ∧
    genPhi P A C * genPhi P A C = genV P A C := by
  dsimp only [observationBoundaryOperator]
  refine ⟨?_, ?_, ?_, ?_⟩ <;> peirce_nf hP

end NonCommutativeOperatorRealization

end DetectorGeometry.ObservationBoundarySilos
