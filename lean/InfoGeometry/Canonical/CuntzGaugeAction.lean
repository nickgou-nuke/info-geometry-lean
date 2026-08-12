import InfoGeometry.Canonical.ToeplitzCuntzVacuumBridge

namespace InfoGeometry.Canonical

open ToeplitzCuntzVacuumBridge

variable {R : Type*} [CommRing R] [StarRing R]

/-- The identity gauge action on a Cuntz generator pair.

Nontrivial normalized rotations are owned by
`CuntzGaugeRotationNative`; this compatibility owner records the identity
case without duplicating the rotation algebra. -/
theorem toeplitzCuntzGenerators_isometry_relations
    (g : ToeplitzCuntzGenerators R) :
      star g.V1 * g.V1 = 1 ∧
      star g.V2 * g.V2 = 1 ∧
      star g.V1 * g.V2 = 0 ∧
      star g.V2 * g.V1 = 0 := by
    exact ⟨g.V1_isometry, g.V2_isometry,
      g.V1_V2_orthogonal, g.V2_V1_orthogonal⟩

end InfoGeometry.Canonical
