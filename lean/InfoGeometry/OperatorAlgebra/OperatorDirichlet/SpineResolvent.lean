/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.OperatorAlgebra.OperatorDirichlet.Resolvent
import InfoGeometry.OperatorAlgebra.PeirceSpine.Tetraktys
import InfoGeometry.OperatorAlgebra.PeirceSpine.ChiralEulerFactors

/-!
# Resolvents of the Peirce generators

The resolvent identities of `OperatorDirichlet.Resolvent` applied to the
Peirce spine of an idempotent `P`:

* `N₊`, `N₋` square to zero, so `(1 - N_±)⁻¹ = 1 + N_±`;
* `Φ² = V` and `J² = -V`, so the resolvents of `Φ`, `J` are obtained from those
  of `z² - V` and `z² + V`. The characteristic value is the operator `V`.
-/

namespace InfoGeometry.OperatorAlgebra.OperatorDirichlet

open InfoGeometry.OperatorAlgebra.PeirceSpine

variable {R B : Type*} [CommRing R] [Ring B] [Algebra R B] {P : B} (hP : P * P = P)
include hP

theorem conePlus_resolvent (A : B) :
    (1 - conePlus P A) * (1 + conePlus P A) = 1 ∧ (1 + conePlus P A) * (1 - conePlus P A) = 1 := by
  have h := conePlus_mul_conePlus hP A A
  constructor <;> noncomm_ring [h]

theorem coneMinus_resolvent (C : B) :
    (1 - coneMinus P C) * (1 + coneMinus P C) = 1 ∧
      (1 + coneMinus P C) * (1 - coneMinus P C) = 1 := by
  have h := coneMinus_mul_coneMinus hP C C
  constructor <;> noncomm_ring [h]

/-- Resolvent of `Φ` from the unit `z² - V`. -/
theorem genPhi_resolvent (A C : B) (z : R) (u : Bˣ)
    (hu : (u : B) = algebraMap R B (z * z) - genV P A C) :
    (algebraMap R B z - genPhi P A C) * ((algebraMap R B z + genPhi P A C) * ↑u⁻¹) = 1 ∧
    ((algebraMap R B z + genPhi P A C) * ↑u⁻¹) * (algebraMap R B z - genPhi P A C) = 1 :=
  resolvent_of_charPoly_unit (archetype_A3_nilpotent_cones_and_tetraktys_table hP A C).2.2.1
    z u hu

/-- Resolvent of `J` from the unit `z² + V`. -/
theorem genJ_resolvent (A C : B) (z : R) (u : Bˣ)
    (hu : (u : B) = algebraMap R B (z * z) - -genV P A C) :
    (algebraMap R B z - genJ P A C) * ((algebraMap R B z + genJ P A C) * ↑u⁻¹) = 1 ∧
    ((algebraMap R B z + genJ P A C) * ↑u⁻¹) * (algebraMap R B z - genJ P A C) = 1 :=
  resolvent_of_charPoly_unit (archetype_A3_nilpotent_cones_and_tetraktys_table hP A C).2.2.2.1
    z u hu

/-- The ordered chiral Euler factors provide the characteristic unit needed
for the two-sided resolvent of `Φ` at spectral parameter `1`. -/
theorem genPhi_chiral_euler_resolvent {R : Type*} [CommRing R] [Algebra R B]
    (A C : B) (u : Bˣ)
    (hu : (u : B) =
      (1 - qgtPlus P A C) * (1 - qgtMinus P A C)) :
    (1 - genPhi P A C) * ((1 + genPhi P A C) * ↑u⁻¹) = 1 ∧
    ((1 + genPhi P A C) * ↑u⁻¹) * (1 - genPhi P A C) = 1 := by
  have hEuler := chiralEuler_factorizations hP A C
  have hu' : (u : B) = algebraMap R B (1 * 1) - genV P A C := by
    calc
      (u : B) = (1 - qgtPlus P A C) * (1 - qgtMinus P A C) := hu
      _ = zetaFactor P A C := hEuler.1
      _ = algebraMap R B (1 * 1) - genV P A C := by simp [zetaFactor]
  simpa using genPhi_resolvent hP A C 1 u hu'

/-- The ordered positive chiral factors provide the characteristic unit
needed for the two-sided resolvent of `J` at spectral parameter `1`. -/
theorem genJ_chiral_zetaPlus_resolvent {R : Type*} [CommRing R] [Algebra R B]
    (A C : B) (u : Bˣ)
    (hu : (u : B) =
      (1 + qgtPlus P A C) * (1 + qgtMinus P A C)) :
    (1 - genJ P A C) * ((1 + genJ P A C) * ↑u⁻¹) = 1 ∧
    ((1 + genJ P A C) * ↑u⁻¹) * (1 - genJ P A C) = 1 := by
  have hEuler := chiralEuler_factorizations hP A C
  have hu' : (u : B) = algebraMap R B (1 * 1) - -genV P A C := by
    calc
      (u : B) = (1 + qgtPlus P A C) * (1 + qgtMinus P A C) := hu
      _ = zetaPlusFactor P A C := hEuler.2.1
      _ = algebraMap R B (1 * 1) - -genV P A C := by
        simp [zetaPlusFactor]
  simpa using genJ_resolvent hP A C 1 u hu'

end InfoGeometry.OperatorAlgebra.OperatorDirichlet
