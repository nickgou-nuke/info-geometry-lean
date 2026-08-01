import InfoGeometry.Canonical.ToeplitzCuntzVacuumBridge

namespace InfoGeometry.Canonical

open ToeplitzCuntzVacuumBridge

variable {R : Type*} [CommRing R] [StarRing R]

/-- The identity gauge action on a Cuntz generator pair.

This owner deliberately records only the scalar-free action that is justified by
the existing `ToeplitzCuntzGenerators` interface.  A genuine `U(2)` action
requires an ambient algebra with a specified scalar action and star-compatible
coefficients, which is a separate extension. -/
def identityGauge (g : ToeplitzCuntzGenerators R) : ToeplitzCuntzGenerators R := g

theorem identityGauge_isometry_relations (g : ToeplitzCuntzGenerators R) :
    star (identityGauge g).V1 * (identityGauge g).V1 = 1 ∧
    star (identityGauge g).V2 * (identityGauge g).V2 = 1 ∧
    star (identityGauge g).V1 * (identityGauge g).V2 = 0 ∧
    star (identityGauge g).V2 * (identityGauge g).V1 = 0 := by
  exact ⟨g.V1_isometry, g.V2_isometry,
    g.V1_V2_orthogonal, g.V2_V1_orthogonal⟩

theorem identityGauge_preserves_cuntz_relations (g : ToeplitzCuntzGenerators R) :
    identityGauge g = g := rfl

end InfoGeometry.Canonical
