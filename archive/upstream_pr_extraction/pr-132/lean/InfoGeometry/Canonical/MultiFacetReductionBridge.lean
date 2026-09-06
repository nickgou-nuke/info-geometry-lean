import InfoGeometry.Algebra.TriFacetSpectralPowers

namespace InfoGeometry.Canonical.MultiFacetReductionBridge

open scoped Matrix

variable {R : Type*} [Ring R]

/-- Canonical bridge for the m-facet spectral reduction theorem. -/
theorem O_pow_reduction (O : R) (m : ℕ) (h_deg : O ^ m = O) (k : ℕ) :
    O ^ (m + k) = O ^ (k + 1) :=
  Audit.O_pow_reduction O m h_deg k

end InfoGeometry.Canonical.MultiFacetReductionBridge
