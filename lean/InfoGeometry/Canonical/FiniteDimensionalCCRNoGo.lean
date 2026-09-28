import Mathlib.LinearAlgebra.Trace

/-!
# Finite-dimensional obstruction to a scalar commutator

The trace of a commutator of endomorphisms is zero.  In characteristic zero,
the trace of a nonzero scalar multiple of the identity on a nonzero finite-
dimensional space is nonzero.  This gives the abstract obstruction underlying
the repository's concrete finite-matrix CCR results.
-/

namespace InfoGeometry.Canonical.FiniteDimensionalCCRNoGo

/-- On a nonzero finite-dimensional vector space over a characteristic-zero
field, an endomorphism commutator cannot equal a nonzero scalar multiple of
the identity. -/
theorem commutator_ne_scalar_smul_one
    {K V : Type*} [Field K] [CharZero K]
    [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Nontrivial V]
    (f g : Module.End K V) (c : K) (hc : c ≠ 0) :
    f * g - g * f ≠ c • (1 : Module.End K V) := by
  intro h
  have htrace := congrArg (LinearMap.trace K V) h
  have hcomm : LinearMap.trace K V (f * g - g * f) = 0 := by
    rw [map_sub, LinearMap.trace_mul_comm, sub_self]
  have hscalar :
      LinearMap.trace K V (c • (1 : Module.End K V)) =
        c * (Module.finrank K V : K) := by
    rw [map_smul, LinearMap.trace_id]
    simp
  rw [hcomm, hscalar] at htrace
  have hdim : (Module.finrank K V : K) ≠ 0 := by
    exact_mod_cast (Module.finrank_pos (R := K) (M := V))
  exact (mul_ne_zero hc hdim) htrace.symm

/-- In particular, an exact scalar commutation relation on a nonzero
finite-dimensional characteristic-zero space has zero scalar coefficient. -/
theorem scalar_eq_zero_of_commutator_eq
    {K V : Type*} [Field K] [CharZero K]
    [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Nontrivial V]
    (f g : Module.End K V) (c : K)
    (h : f * g - g * f = c • (1 : Module.End K V)) : c = 0 := by
  by_contra hc
  exact commutator_ne_scalar_smul_one f g c hc h

end InfoGeometry.Canonical.FiniteDimensionalCCRNoGo
