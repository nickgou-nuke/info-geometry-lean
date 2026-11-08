import InfoGeometry.Canonical.RicciMongeAmpere
import InfoGeometry.Algebra.FiniteSpinAlgebra

namespace InfoGeometry.Topology

universe u

export InfoGeometry.Canonical.RicciMongeAmpere
  (RicciFlow IsRicciFixedPoint)

/-- A placeholder structure for a Connected Sum of two manifolds. -/
structure ConnectedSum (M₁ M₂ : Type u) where
  /-- The resulting manifold type. -/
  ResultType : Type u

end InfoGeometry.Topology
