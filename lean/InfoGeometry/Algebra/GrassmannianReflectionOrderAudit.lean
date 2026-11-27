/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Algebra.HuaBergmanZornExtensions
import Mathlib.LinearAlgebra.Matrix.Notation

/-!
# Ordered reflection products in the idempotent Grassmannian chart

The chart points are the existing Peirce translates `P - N₊` and `P + N₋`.
This owner records the order-sensitive reflection products and a finite matrix
witness refuting the reversed-sign formula in the incoming draft. These are
ring identities; no metric, angle, topology, or manifold structure is asserted.
-/

namespace PureNonCommutativeOperatorSpine

variable {B : Type*} [Ring B]

/-- Reflection associated with the upper translated idempotent. -/
def upperChartReflection (P A : B) : B := invS (P - conePlus P A)

/-- Reflection associated with the lower translated idempotent. -/
def lowerChartReflection (P C : B) : B := invS (P + coneMinus P C)

/-- The ordered product of the upper and lower chart reflections. -/
theorem upper_lower_reflection_product {P : B} (hP : P * P = P) (A C : B) :
    upperChartReflection P A * lowerChartReflection P C =
      1 + 2 * genJ P A C - 2 * genSig P A C - 2 * genV P A C := by
  simp only [upperChartReflection, lowerChartReflection, invS, genJ, genSig,
    genV, comm, anticomm, conePlus, coneMinus]
  noncomm_ring [hP, P_assoc hP]

/-- Reversing the reflection order reverses the signs of `J` and `Sigma`. -/
theorem lower_upper_reflection_product {P : B} (hP : P * P = P) (A C : B) :
    lowerChartReflection P C * upperChartReflection P A =
      1 - 2 * genJ P A C + 2 * genSig P A C - 2 * genV P A C := by
  simp only [upperChartReflection, lowerChartReflection, invS, genJ, genSig,
    genV, comm, anticomm, conePlus, coneMinus]
  noncomm_ring [hP, P_assoc hP]

/-- The symmetric reflection product is order-independent and depends on `V`. -/
theorem reflection_anticommutator {P : B} (hP : P * P = P) (A C : B) :
    upperChartReflection P A * lowerChartReflection P C +
        lowerChartReflection P C * upperChartReflection P A =
      2 * (1 - 2 * genV P A C) := by
  rw [upper_lower_reflection_product hP, lower_upper_reflection_product hP]
  noncomm_ring

/-- The commutator is order-sensitive; its sign is `J - Sigma` in this order. -/
theorem reflection_commutator {P : B} (hP : P * P = P) (A C : B) :
    upperChartReflection P A * lowerChartReflection P C -
        lowerChartReflection P C * upperChartReflection P A =
      4 * (genJ P A C - genSig P A C) := by
  rw [upper_lower_reflection_product hP, lower_upper_reflection_product hP]
  noncomm_ring

/-! ## Concrete counterexample to the draft's ordered product and commutator signs

The witness uses genuine noncommuting `2 × 2` integer matrices, not a scalar
or diagonal specialization. -/

abbrev ReflectionWitness := Matrix (Fin 2) (Fin 2) ℤ

def reflectionWitnessP : ReflectionWitness := Matrix.single 0 0 1
def reflectionWitnessA : ReflectionWitness := Matrix.single 0 1 1
def reflectionWitnessC : ReflectionWitness := Matrix.single 1 0 1

/-- The proposed forward formula in the draft is false for this idempotent and
these noncommuting off-diagonal chart directions. -/
theorem draft_forward_reflection_formula_counterexample :
    reflectionWitnessP * reflectionWitnessP = reflectionWitnessP ∧
      upperChartReflection reflectionWitnessP reflectionWitnessA *
          lowerChartReflection reflectionWitnessP reflectionWitnessC ≠
        1 - 2 * genJ reflectionWitnessP reflectionWitnessA reflectionWitnessC +
          2 * genSig reflectionWitnessP reflectionWitnessA reflectionWitnessC -
          2 * genV reflectionWitnessP reflectionWitnessA reflectionWitnessC := by
  decide

/-- The draft's commutator sign is also false in the same noncommuting matrix
example. The corrected generic identity is `4 * (J - Sigma)`. -/
theorem draft_reflection_commutator_sign_counterexample :
    upperChartReflection reflectionWitnessP reflectionWitnessA *
          lowerChartReflection reflectionWitnessP reflectionWitnessC -
        lowerChartReflection reflectionWitnessP reflectionWitnessC *
          upperChartReflection reflectionWitnessP reflectionWitnessA ≠
      4 * (genSig reflectionWitnessP reflectionWitnessA reflectionWitnessC -
        genJ reflectionWitnessP reflectionWitnessA reflectionWitnessC) := by
  decide

/-- Explicit `2 × 2` integer matrix non-commutativity witness for `ReflectionWitness`. -/
theorem reflectionWitness_noncomm_exists :
    ∃ A B : Matrix (Fin 2) (Fin 2) ℤ, A * B ≠ B * A :=
  ⟨reflectionWitnessP, reflectionWitnessA, by decide⟩

end PureNonCommutativeOperatorSpine
