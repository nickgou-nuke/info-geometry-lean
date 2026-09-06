import Mathlib
import InfoGeometry.Canonical.ToeplitzCuntzVacuumBridge

namespace InfoGeometry.Canonical

open ToeplitzCuntzVacuumBridge

variable {R : Type*} [CommRing R] [StarRing R]

structure SelfAdjointNormalizedPairNative (R : Type*) [CommRing R] [StarRing R] where
  a : R
  b : R
  star_a : star a = a
  star_b : star b = b
  normalized : a * a + b * b = 1

def nativeRotationV1 (r : SelfAdjointNormalizedPairNative R)
    (g : ToeplitzCuntzGenerators R) : R := r.a * g.V1 + r.b * g.V2

def nativeRotationV2 (r : SelfAdjointNormalizedPairNative R)
    (g : ToeplitzCuntzGenerators R) : R := -(r.b * g.V1) + r.a * g.V2

theorem nativeRotationV1_isometry (r : SelfAdjointNormalizedPairNative R)
    (g : ToeplitzCuntzGenerators R) :
    star (nativeRotationV1 r g) * nativeRotationV1 r g = 1 := by
  simp [nativeRotationV1, r.star_a, r.star_b]
  linear_combination
    r.a * r.b * g.V1_V2_orthogonal +
    r.a * r.b * g.V2_V1_orthogonal +
    r.a ^ 2 * g.V1_isometry +
    r.b ^ 2 * g.V2_isometry + r.normalized

theorem nativeRotationV2_isometry (r : SelfAdjointNormalizedPairNative R)
    (g : ToeplitzCuntzGenerators R) :
    star (nativeRotationV2 r g) * nativeRotationV2 r g = 1 := by
  simp [nativeRotationV2, r.star_a, r.star_b]
  linear_combination
    -(r.a * r.b) * g.V1_V2_orthogonal -
    (r.a * r.b) * g.V2_V1_orthogonal +
    r.b ^ 2 * g.V1_isometry +
    r.a ^ 2 * g.V2_isometry + r.normalized

theorem nativeRotationV1_V2_orthogonal (r : SelfAdjointNormalizedPairNative R)
    (g : ToeplitzCuntzGenerators R) :
    star (nativeRotationV1 r g) * nativeRotationV2 r g = 0 := by
  simp [nativeRotationV1, nativeRotationV2, r.star_a, r.star_b]
  linear_combination
    -(r.a * r.b) * g.V1_isometry +
    (r.a * r.b) * g.V2_isometry +
    r.a ^ 2 * g.V1_V2_orthogonal -
    r.b ^ 2 * g.V2_V1_orthogonal

theorem nativeRotationV2_V1_orthogonal (r : SelfAdjointNormalizedPairNative R)
    (g : ToeplitzCuntzGenerators R) :
    star (nativeRotationV2 r g) * nativeRotationV1 r g = 0 := by
  simp [nativeRotationV1, nativeRotationV2, r.star_a, r.star_b]
  linear_combination
    -(r.a * r.b) * g.V1_isometry +
    (r.a * r.b) * g.V2_isometry -
    r.b ^ 2 * g.V1_V2_orthogonal +
    r.a ^ 2 * g.V2_V1_orthogonal

def nativeRotatedCuntzGenerators (r : SelfAdjointNormalizedPairNative R)
    (g : ToeplitzCuntzGenerators R) : ToeplitzCuntzGenerators R where
  V1 := nativeRotationV1 r g
  V2 := nativeRotationV2 r g
  V1_isometry := nativeRotationV1_isometry r g
  V2_isometry := nativeRotationV2_isometry r g
  V1_V2_orthogonal := nativeRotationV1_V2_orthogonal r g
  V2_V1_orthogonal := nativeRotationV2_V1_orthogonal r g

theorem nativeRotatedCuntzGenerators_relations
    (r : SelfAdjointNormalizedPairNative R) (g : ToeplitzCuntzGenerators R) :
    star (nativeRotatedCuntzGenerators r g).V1 *
        (nativeRotatedCuntzGenerators r g).V1 = 1 ∧
    star (nativeRotatedCuntzGenerators r g).V2 *
        (nativeRotatedCuntzGenerators r g).V2 = 1 ∧
    star (nativeRotatedCuntzGenerators r g).V1 *
        (nativeRotatedCuntzGenerators r g).V2 = 0 ∧
    star (nativeRotatedCuntzGenerators r g).V2 *
        (nativeRotatedCuntzGenerators r g).V1 = 0 :=
  ⟨nativeRotationV1_isometry r g, nativeRotationV2_isometry r g,
    nativeRotationV1_V2_orthogonal r g, nativeRotationV2_V1_orthogonal r g⟩

end InfoGeometry.Canonical
