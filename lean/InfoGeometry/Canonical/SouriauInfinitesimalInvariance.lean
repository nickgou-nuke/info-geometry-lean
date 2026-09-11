import Mathlib.Tactic
import InfoGeometry.Algebra.FiniteSpinAlgebra

/-!
# InfoGeometry.Canonical.SouriauInfinitesimalInvariance

Infinitesimal modular invariance in the endomorphism Lie algebra.

No wrappers. No `sorry`.
-/

namespace InfoGeometry.Canonical.SouriauInfinitesimalInvariance

variable {𝕜 V : Type*}
variable [Field 𝕜] [AddCommGroup V] [Module 𝕜 V]

/--
Vanishing commutator is equivalent to commutation under composition.
-/
theorem infinitesimal_modular_flow_invariant
    (K A : V →ₗ[𝕜] V) :
    K.comp A - A.comp K = 0 ↔ K.comp A = A.comp K := by
  constructor
  · intro h
    exact sub_eq_zero.mp h
  · intro h
    simp [h]

/--
Commutation with `K` implies commutation with `K²` (composition square).
-/
theorem infinitesimal_modular_power_invariant
    (K A : V →ₗ[𝕜] V) (h : K.comp A = A.comp K) :
    (K.comp K).comp A = A.comp (K.comp K) := by
  calc
    (K.comp K).comp A = K.comp (K.comp A) := by rw [LinearMap.comp_assoc]
    _ = K.comp (A.comp K) := by rw [h]
    _ = (K.comp A).comp K := by rw [LinearMap.comp_assoc]
    _ = (A.comp K).comp K := by rw [h]
    _ = A.comp (K.comp K) := by rw [LinearMap.comp_assoc]

end InfoGeometry.Canonical.SouriauInfinitesimalInvariance
