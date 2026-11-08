import InfoGeometry.Canonical.RealHomologyCohomologyDictionary

/-!
# Fixed observables and the index-one Drazin projector

For a finite real space of observables, if `I - T` has an index-one Drazin
inverse, then the fixed observables of `T` (the harmonic vectors for `T`) are
exactly the range of the complementary Drazin projector. This is an algebraic
subspace identity. It does not identify stationary distributions for a Markov
chain, and it does not assert convergence of powers or Cesàro averages.
-/

namespace InfoGeometry.Experimental.DrazinMarkovFixedSubmodule

open InfoGeometry.Canonical.Drazin
open InfoGeometry.Canonical.Drazin.IsDrazinInverse
open InfoGeometry.Canonical.RealHomologyCohomologyDictionary

/-- For a linear endomorphism `T` of a finite real space of observables, the
fixed-vector equation `T x = x` is equivalent to membership in the range of
the complementary Drazin projector of `I - T`, provided `I - T` has an
index-one Drazin inverse. -/
theorem fixedVector_iff_mem_complementaryProjection_range
    {n : ℕ}
    (T D : Module.End ℝ (Fin n → ℝ))
    (hD : IsDrazinInverse (1 - T) D 1)
    (x : Fin n → ℝ) :
    T x = x ↔
      x ∈ LinearMap.range
        (IsDrazinInverse.complementaryProjection (1 - T) D) := by
  rw [complementaryProjection_range_eq_moduleEndDrazinNullCycles hD x]
  have hNull :
      IsModuleEndDrazinNullCycle (1 - T) 1 x ↔ x - T x = 0 := by
    simp [IsModuleEndDrazinNullCycle, pow_one, LinearMap.sub_apply,
      Module.End.one_apply]
  rw [hNull]
  constructor
  · intro hT
    rw [hT]
    simp
  · intro h
    exact (sub_eq_zero.mp h).symm

end InfoGeometry.Experimental.DrazinMarkovFixedSubmodule
