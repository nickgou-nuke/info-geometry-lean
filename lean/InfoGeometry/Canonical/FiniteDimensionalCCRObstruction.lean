import Mathlib.LinearAlgebra.Trace
import Mathlib.LinearAlgebra.FiniteDimensional.Basic

namespace InfoGeometry.Canonical.FiniteDimensionalCCRObstruction

/-!
The finite-dimensional CCR obstruction in coordinate-free form.  This is the
same trace argument as the matrix theorem, but it applies to arbitrary finite
endomorphism algebras and does not choose a basis.
-/

variable {K V : Type*} [Field K] [CharZero K]
  [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Nontrivial V]

theorem no_scalar_commutator_one
    (f g : Module.End K V)
    (h : f * g - g * f = 1) : False := by
  have ht := congrArg (LinearMap.trace K V) h
  rw [map_sub, LinearMap.trace_mul_comm, sub_self, LinearMap.trace_one] at ht
  have hpos : 0 < Module.finrank K V := Module.finrank_pos
  have hne : (Module.finrank K V : K) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt hpos)
  exact hne ht.symm

theorem no_nonzero_scalar_commutator
    (f g : Module.End K V) (c : K) (hc : c ≠ 0)
    (h : f * g - g * f = algebraMap K (Module.End K V) c) : False := by
  have ht := congrArg (LinearMap.trace K V) h
  rw [map_sub, LinearMap.trace_mul_comm, sub_self] at ht
  have hscalar : algebraMap K (Module.End K V) c = c • (1 : Module.End K V) := by
    simp [Algebra.smul_def]
  rw [hscalar, map_smul, LinearMap.trace_one] at ht
  have hpos : 0 < Module.finrank K V := Module.finrank_pos
  have hdim : (Module.finrank K V : K) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt hpos)
  have : c * (Module.finrank K V : K) = 0 := by simpa using ht
  exact hc ((mul_eq_zero.mp this).resolve_right hdim)

end InfoGeometry.Canonical.FiniteDimensionalCCRObstruction
