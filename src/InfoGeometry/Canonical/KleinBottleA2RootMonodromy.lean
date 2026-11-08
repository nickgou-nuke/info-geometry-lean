import Mathlib
import InfoGeometry.Algebra.FiniteSpinAlgebra

/-!
# Finite Klein-bottle monodromy on the three-colour fibre

The cyclic colour transport and the orientation-reversing reflection are
explicit linear operators on `Fin 3 → K`.  Their relations give the concrete
`D₃ ≃ S₃` quotient of the Klein-bottle relation with cubic translation.
-/

namespace InfoGeometry.Canonical

variable {K : Type*} [CommRing K]

abbrev A2ColourFiber (K : Type*) := Fin 3 → K

def a2Cycle : A2ColourFiber K →ₗ[K] A2ColourFiber K where
  toFun v := ![v 2, v 0, v 1]
  map_add' v w := by
    funext i
    fin_cases i <;> simp
  map_smul' c v := by
    funext i
    fin_cases i <;> simp

def a2Reflection : A2ColourFiber K →ₗ[K] A2ColourFiber K where
  toFun v := ![v 0, v 2, v 1]
  map_add' v w := by
    funext i
    fin_cases i <;> simp
  map_smul' c v := by
    funext i
    fin_cases i <;> simp

@[simp] theorem a2Cycle_apply (v : A2ColourFiber K) (i : Fin 3) :
    a2Cycle v i = ![v 2, v 0, v 1] i := rfl

theorem a2Cycle_cube :
    (a2Cycle (K := K)).comp ((a2Cycle (K := K)).comp (a2Cycle (K := K))) =
      LinearMap.id := by
  apply LinearMap.ext
  intro v
  funext i
  fin_cases i <;> rfl

theorem a2Reflection_square :
    (a2Reflection (K := K)).comp (a2Reflection (K := K)) =
      LinearMap.id := by
  apply LinearMap.ext
  intro v
  funext i
  fin_cases i <;> rfl

theorem a2Reflection_conj_cycle :
    (a2Reflection (K := K)).comp
        ((a2Cycle (K := K)).comp (a2Reflection (K := K))) =
      (a2Cycle (K := K)).comp (a2Cycle (K := K)) := by
  apply LinearMap.ext
  intro v
  funext i
  fin_cases i <;> rfl

theorem a2Cycle_reflection_cycle :
    (a2Cycle (K := K)).comp
        ((a2Reflection (K := K)).comp (a2Cycle (K := K))) =
      (a2Reflection (K := K)) := by
  apply LinearMap.ext
  intro v
  funext i
  fin_cases i <;> rfl

end InfoGeometry.Canonical
