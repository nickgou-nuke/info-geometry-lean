import InfoGeometry.Canonical.KleinBottleA2RootMonodromy
import InfoGeometry.Algebra.FiniteSpinAlgebra

/-!
# The `A₂` root fibre inside the three-colour fibre

The root plane is the kernel of the coordinate-sum functional.  The cyclic
transport and reflection preserve this submodule, so the Klein-bottle
monodromy restricts to the genuine `A₂` root local system.
-/

namespace InfoGeometry.Canonical

variable {K : Type*} [CommRing K]

def a2RootSubmodule : Submodule K (A2ColourFiber K) where
  carrier := {v | v 0 + v 1 + v 2 = 0}
  zero_mem' := by simp
  add_mem' := by
    intro v w hv hw
    dsimp at hv hw ⊢
    linear_combination hv + hw
  smul_mem' := by
    intro c v hv
    dsimp at hv ⊢
    simpa [smul_eq_mul, mul_add] using congrArg (fun z => c * z) hv

def a2RootCycle : a2RootSubmodule (K := K) →ₗ[K] a2RootSubmodule (K := K) where
  toFun v := ⟨a2Cycle v.1, by
    change v.1 2 + v.1 0 + v.1 1 = 0
    have hv : v.1 0 + v.1 1 + v.1 2 = 0 := v.property
    linear_combination hv⟩
  map_add' v w := by ext i; fin_cases i <;> simp
  map_smul' c v := by ext i; fin_cases i <;> simp

def a2RootReflection : a2RootSubmodule (K := K) →ₗ[K] a2RootSubmodule (K := K) where
  toFun v := ⟨a2Reflection v.1, by
    change v.1 0 + v.1 2 + v.1 1 = 0
    have hv : v.1 0 + v.1 1 + v.1 2 = 0 := v.property
    linear_combination hv⟩
  map_add' v w := by ext i; fin_cases i <;> simp
  map_smul' c v := by ext i; fin_cases i <;> simp

theorem a2RootCycle_cube :
    (a2RootCycle (K := K)).comp ((a2RootCycle (K := K)).comp (a2RootCycle (K := K))) =
      LinearMap.id := by
  apply LinearMap.ext
  intro v
  apply Subtype.ext
  change a2Cycle (a2Cycle (a2Cycle v.1)) = v.1
  have h := congrArg (fun T : A2ColourFiber K →ₗ[K] A2ColourFiber K => T v.1)
    (a2Cycle_cube (K := K))
  simpa [LinearMap.comp_apply] using h

theorem a2RootReflection_square :
    (a2RootReflection (K := K)).comp (a2RootReflection (K := K)) =
      LinearMap.id := by
  apply LinearMap.ext
  intro v
  apply Subtype.ext
  change a2Reflection (a2Reflection v.1) = v.1
  have h := congrArg (fun T : A2ColourFiber K →ₗ[K] A2ColourFiber K => T v.1)
    (a2Reflection_square (K := K))
  simpa [LinearMap.comp_apply] using h

theorem a2RootReflection_conj_cycle :
    (a2RootReflection (K := K)).comp
        ((a2RootCycle (K := K)).comp (a2RootReflection (K := K))) =
      (a2RootCycle (K := K)).comp (a2RootCycle (K := K)) := by
  apply LinearMap.ext
  intro v
  apply Subtype.ext
  change a2Reflection (a2Cycle (a2Reflection v.1)) =
    a2Cycle (a2Cycle v.1)
  have h := congrArg (fun T : A2ColourFiber K →ₗ[K] A2ColourFiber K => T v.1)
    (a2Reflection_conj_cycle (K := K))
  simpa [LinearMap.comp_apply] using h

end InfoGeometry.Canonical
