import Mathlib.Algebra.Module.LinearMap.Basic
import Mathlib

/-!
# InfoGeometry.Canonical.CARVacuumContraction

Concrete CAR vacuum contraction lemmas on a state `v`.

This file proves:

* single-mode contraction:
  if `A ∘ C + C ∘ A = c • id` and `A v = 0`, then `A (C v) = c • v`;
* bounded finite-sum lift over a `Finset` of modes.
-/

namespace CARVacuumContraction

open scoped BigOperators

variable {𝕜 V ι : Type*}
variable [CommRing 𝕜] [AddCommGroup V] [Module 𝕜 V]

/--
Single-mode CAR vacuum contraction.
-/
theorem car_vacuum_contraction
    (A C : V →ₗ[𝕜] V)
    (c : 𝕜)
    (h_car : A.comp C + C.comp A = c • (LinearMap.id : V →ₗ[𝕜] V))
    (v : V)
    (h_vac : A v = 0) :
    A (C v) = c • v := by
  have h_eval : (A.comp C + C.comp A) v = (c • (LinearMap.id : V →ₗ[𝕜] V)) v := by
    simpa using congrArg (fun F : V →ₗ[𝕜] V => F v) h_car
  rw [LinearMap.add_apply, LinearMap.comp_apply, LinearMap.comp_apply] at h_eval
  rw [LinearMap.smul_apply, LinearMap.id_apply] at h_eval
  rw [h_vac, LinearMap.map_zero, add_zero] at h_eval
  exact h_eval

/--
Bounded finite-sum CAR contraction on a vacuum state.

Each mode `i` contributes `c i • v` provided:
* modewise CAR: `(A i) ∘ (C i) + (C i) ∘ (A i) = c i • id`;
* vacuum annihilation: `(A i) v = 0`.
-/
theorem car_vacuum_contraction_sum
    [DecidableEq ι]
    (S : Finset ι)
    (A C : ι → V →ₗ[𝕜] V)
    (c : ι → 𝕜)
    (v : V)
    (h_car :
      ∀ i ∈ S,
        (A i).comp (C i) + (C i).comp (A i) = (c i) • (LinearMap.id : V →ₗ[𝕜] V))
    (h_vac : ∀ i ∈ S, A i v = 0) :
    (Finset.sum S (fun i => (A i).comp (C i))) v = (Finset.sum S c) • v := by
  calc
    (Finset.sum S (fun i => (A i).comp (C i))) v
        = Finset.sum S (fun i => ((A i).comp (C i)) v) := by
            simp
    _ = Finset.sum S (fun i => (c i) • v) := by
          refine Finset.sum_congr rfl ?_
          intro i hi
          simpa using
            car_vacuum_contraction (A i) (C i) (c i) (h_car i hi) v (h_vac i hi)
    _ = (Finset.sum S c) • v := by
          simpa using (Finset.sum_smul (s := S) (f := c) (x := v)).symm

end CARVacuumContraction
