/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/

import InfoGeometry.Lie.E10HyperbolicSignature
import InfoGeometry.OperatorAlgebra.PeirceSpine.Tetraktys

/-!
# E₁₀ quadratic-form witness and scope

The affine E₉ null vector, perturbed in the extending direction, gives a
negative value for the E₁₀ Cartan quadratic form. Together with a positive
simple-coordinate direction, this proves indefiniteness. It does not by itself
prove Lorentzian signature or the strict hyperbolic-subdiagram criterion.
-/

namespace InfoGeometry.Lie.E10TimelikeWitness

open InfoGeometry.Lie.E10
open InfoGeometry.Lie.E10Hyperbolic

/-- Dependency nodes for the timelike-witness argument and its stronger
downstream classification goals. -/
inductive Archetype
  | e10CartanData
  | affineE9NullRoot
  | extendingNode
  | timelikePerturbation
  | negativeQuadraticValue
  | lorentzianSignature
  | strictHyperbolicity
  deriving DecidableEq, Repr

/-- Rank of a node in the causal dependency chain. -/
def Archetype.rank : Archetype → ℕ
  | .e10CartanData => 0
  | .affineE9NullRoot => 1
  | .extendingNode => 2
  | .timelikePerturbation => 3
  | .negativeQuadraticValue => 4
  | .lorentzianSignature => 5
  | .strictHyperbolicity => 6

/-- The causal poset is the order induced by dependency rank. -/
instance : PartialOrder Archetype where
  le a b := a.rank ≤ b.rank
  le_refl a := Nat.le_refl _
  le_trans _ _ _ := Nat.le_trans
  le_antisymm := by
    intro a b hab hba
    cases a <;> cases b <;> simp_all [Archetype.rank]

/-- The extracted archetypes are linearly ordered by the proof dependencies. -/
theorem causal_archetype_chain :
    Archetype.e10CartanData ≤ .affineE9NullRoot ∧
    Archetype.affineE9NullRoot ≤ .extendingNode ∧
    Archetype.extendingNode ≤ .timelikePerturbation ∧
    Archetype.timelikePerturbation ≤ .negativeQuadraticValue ∧
    Archetype.negativeQuadraticValue ≤ .lorentzianSignature ∧
    Archetype.lorentzianSignature ≤ .strictHyperbolicity := by
  decide

/-- The proposed E₁₀ vector is a strict negative direction of the Cartan form. -/
theorem timelikeRoot_has_negative_quadratic_value :
    cartanQuadraticForm timelikeRoot < 0 := by
  rw [e10_is_hyperbolic]
  norm_num

/-- A simple-coordinate vector has positive Cartan quadratic value. -/
def positiveVector : Fin 10 → ℤ := fun i => if i = 0 then 1 else 0

theorem positiveVector_quadratic_value :
    cartanQuadraticForm positiveVector = 2 := by
  decide

/-- The E₁₀ Cartan quadratic form takes both positive and negative values. -/
theorem cartanQuadraticForm_has_both_signs :
    (∃ v : Fin 10 → ℤ, cartanQuadraticForm v < 0) ∧
    (∃ v : Fin 10 → ℤ, 0 < cartanQuadraticForm v) := by
  exact ⟨⟨timelikeRoot, timelikeRoot_has_negative_quadratic_value⟩,
    ⟨positiveVector, by rw [positiveVector_quadratic_value]; norm_num⟩⟩

/-! ### Non-Commutative Operator Realization of `E10TimelikeWitness.Archetype` over `[Ring B]` -/

section NonCommutativeOperatorRealization

open InfoGeometry.OperatorAlgebra.PeirceSpine

variable {B : Type*} [Ring B]

/-- Non-commutative operator realization mapping each `E10TimelikeWitness.Archetype` node
to its canonical Peirce operator in `[Ring B]`. -/
def e10TimelikeArchetypeOperator (P A C : B) : Archetype → B
  | .e10CartanData => invS P
  | .affineE9NullRoot => conePlus P A
  | .extendingNode => coneMinus P C
  | .timelikePerturbation => genJ P A C
  | .negativeQuadraticValue => genJ P A C * genJ P A C
  | .lorentzianSignature => genPhi P A C * genPhi P A C + genJ P A C * genJ P A C
  | .strictHyperbolicity => InfoGeometry.OperatorAlgebra.PeirceSpine.comm (genPhi P A C) (genJ P A C)

/-- **Theorem (Non-Commutative Operator Identities across `E10TimelikeWitness.Archetype`)**:
For any idempotent `P * P = P` in a non-commutative ring `[Ring B]`, the affine null-root
operator `a₊` is square-zero (`a₊² = 0`), the timelike perturbation `J = a₊ - c₋` has
negative operator square `J² = -V` opposite to the spacelike generator `Φ² = V` so that
`Φ² + J² = 0`, and the owner convention gives the hyperbolic commutator
`[Φ, J] = -2 Σ`. -/
theorem e10TimelikeArchetype_operator_identities {P : B} (hP : P * P = P) (A C : B) :
    e10TimelikeArchetypeOperator P A C .e10CartanData *
      e10TimelikeArchetypeOperator P A C .e10CartanData = 1 ∧
    e10TimelikeArchetypeOperator P A C .affineE9NullRoot *
      e10TimelikeArchetypeOperator P A C .affineE9NullRoot = 0 ∧
    e10TimelikeArchetypeOperator P A C .extendingNode *
      e10TimelikeArchetypeOperator P A C .extendingNode = 0 ∧
    e10TimelikeArchetypeOperator P A C .negativeQuadraticValue = -genV P A C ∧
    e10TimelikeArchetypeOperator P A C .lorentzianSignature = 0 ∧
    e10TimelikeArchetypeOperator P A C .strictHyperbolicity = -((2 : ℤ) • genSig P A C) := by
  dsimp only [e10TimelikeArchetypeOperator]
  have hS := (archetype_A2_peirce_cartan_grading_and_tangent_closure (P := P) hP A C).1
  have hPlus := (archetype_A3_nilpotent_cones_and_tetraktys_table (P := P) hP A C).1
  have hMinus := (archetype_A3_nilpotent_cones_and_tetraktys_table (P := P) hP A C).2.1
  have hJ := (archetype_A3_nilpotent_cones_and_tetraktys_table (P := P) hP A C).2.2.2.1
  have hNull := (archetype_A3_nilpotent_cones_and_tetraktys_table (P := P) hP A C).2.2.2.2.1
  have hBracket := (archetype_A7_so12_lie_brackets_and_cubic_inversions (P := P) hP A C).1
  exact ⟨hS, hPlus, hMinus, hJ, hNull, hBracket⟩

end NonCommutativeOperatorRealization

end InfoGeometry.Lie.E10TimelikeWitness
