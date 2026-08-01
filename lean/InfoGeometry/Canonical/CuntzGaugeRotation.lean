import InfoGeometry.Canonical.ToeplitzCuntzVacuumBridge

namespace InfoGeometry.Canonical

open ToeplitzCuntzVacuumBridge

variable {R : Type*} [CommRing R] [StarRing R]

/-- The currently certified gauge layer is the identity action.

The existing carrier stores generators as elements of the coefficient ring,
but has no scalar-action/centrality interface for a genuine `U(2)` mixing.
This owner therefore exposes the honest base case; a nontrivial rotation
should be added after that richer interface is introduced. -/
def identityCuntzGauge (g : ToeplitzCuntzGenerators R) : ToeplitzCuntzGenerators R := g

theorem identityCuntzGauge_preserves_relations (g : ToeplitzCuntzGenerators R) :
    star (identityCuntzGauge g).V1 * (identityCuntzGauge g).V1 = 1 ∧
    star (identityCuntzGauge g).V2 * (identityCuntzGauge g).V2 = 1 ∧
    star (identityCuntzGauge g).V1 * (identityCuntzGauge g).V2 = 0 ∧
    star (identityCuntzGauge g).V2 * (identityCuntzGauge g).V1 = 0 := by
  exact ⟨g.V1_isometry, g.V2_isometry,
    g.V1_V2_orthogonal, g.V2_V1_orthogonal⟩

end InfoGeometry.Canonical
