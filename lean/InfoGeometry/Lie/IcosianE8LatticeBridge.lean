import InfoGeometry.Canonical.IcosianE8LatticeBridge
import InfoGeometry.Algebra.FiniteSpinAlgebra

/-!
# Icosian Realization of the $E_8$ Lattice

This module forwards to the canonical owner implementation in
`InfoGeometry.Canonical.IcosianE8LatticeBridge`.
-/

namespace InfoGeometry.Lie.IcosianE8LatticeBridge

export InfoGeometry.Canonical.IcosianE8LatticeBridge (
  IcosianE8GeneratingFamily
  icosianE8Embedding
  icosianE8GeneratorMatrix
  icosianE8Generator_linearIndependent
  icosianE8Generator_span
  IcosianGeneratedLattice
  icosianE8Gram
  CanonicalE8Gram
  CanonicalE8Lattice
  icosianE8Gram_eq_canonical
  icosianE8LatticeEquiv
)

end InfoGeometry.Lie.IcosianE8LatticeBridge
