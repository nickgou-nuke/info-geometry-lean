import InfoGeometry.Canonical.HestenesBivectorCarrier

open CliffordAlgebra InfoGeometry.Canonical.CliffordParity InfoGeometry.Canonical.HestenesBivectorCarrier HasVolumeElement

variable {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]
variable (Q : QuadraticForm R M) [HasVolumeElement R M Q] [HasSpacetimeBasis Q]

lemma basisBivector_mul_omega (i : Fin 6) : basisBivector Q i * Omega (Q := Q) ∈ Bivector13 Q := by
  exact InfoGeometry.Canonical.HestenesBivectorCarrier.basisBivector_mul_omega Q i
