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
  rw [nativeRotationV1, star_add, star_mul, star_mul, r.star_a, r.star_b]
  ring_nf
  have h1 : star g.V1 * r.a * r.b * g.V2 = r.a * r.b * (star g.V1 * g.V2) := by
    ring
  have h2 : star g.V1 * r.a ^ 2 * g.V1 = r.a ^ 2 * (star g.V1 * g.V1) := by
    ring
  have h3 : r.a * star g.V2 * r.b * g.V1 = r.a * r.b * (star g.V2 * g.V1) := by
    ring
  have h4 : star g.V2 * r.b ^ 2 * g.V2 = r.b ^ 2 * (star g.V2 * g.V2) := by
    ring
  rw [h1, h2, h3, h4, g.V1_isometry, g.V2_isometry,
    g.V1_V2_orthogonal, g.V2_V1_orthogonal]
  simpa [pow_two, add_comm] using r.normalized

theorem nativeRotationV2_isometry (r : SelfAdjointNormalizedPairNative R)
    (g : ToeplitzCuntzGenerators R) :
    star (nativeRotationV2 r g) * nativeRotationV2 r g = 1 := by
  rw [nativeRotationV2, star_add, star_neg, star_mul, star_mul, r.star_a, r.star_b]
  ring_nf
  have h1 : -(star g.V1 * r.b * r.a * g.V2) = -(r.a * r.b * (star g.V1 * g.V2)) := by
    ring
  have h2 : star g.V1 * r.b ^ 2 * g.V2 = r.b ^ 2 * (star g.V1 * g.V2) := by
    ring
  have h3 : r.b * star g.V2 * r.a * g.V2 = r.a * r.b * (star g.V2 * g.V2) := by
    ring
  have h4 : star g.V2 * r.a ^ 2 * g.V1 = r.a ^ 2 * (star g.V2 * g.V1) := by
    ring
  rw [h1, h2, h3, h4, g.V1_isometry, g.V2_isometry,
    g.V1_V2_orthogonal, g.V2_V1_orthogonal]
  simpa [pow_two, add_comm] using r.normalized

theorem nativeRotationV1_V2_orthogonal (r : SelfAdjointNormalizedPairNative R)
    (g : ToeplitzCuntzGenerators R) :
    star (nativeRotationV1 r g) * nativeRotationV2 r g = 0 := by
  rw [nativeRotationV1, nativeRotationV2, star_add, star_mul, star_mul, r.star_a, r.star_b]
  ring_nf
  have h1 : star g.V1 * r.a * r.b * g.V1 = r.a * r.b * (star g.V1 * g.V1) := by
    ring
  have h2 : star g.V1 * r.a ^ 2 * g.V2 = r.a ^ 2 * (star g.V1 * g.V2) := by
    ring
  have h3 : r.a * star g.V2 * r.b * g.V2 = r.a * r.b * (star g.V2 * g.V2) := by
    ring
  have h4 : star g.V2 * r.b ^ 2 * g.V1 = r.b ^ 2 * (star g.V2 * g.V1) := by
    ring
  rw [h1, h2, h3, h4, g.V1_isometry, g.V2_isometry,
    g.V1_V2_orthogonal, g.V2_V1_orthogonal]
  simp

theorem nativeRotationV2_V1_orthogonal (r : SelfAdjointNormalizedPairNative R)
    (g : ToeplitzCuntzGenerators R) :
    star (nativeRotationV2 r g) * nativeRotationV1 r g = 0 := by
  rw [nativeRotationV2, nativeRotationV1, star_add, star_neg, star_mul, star_mul, r.star_a, r.star_b]
  ring_nf
  have h1 : -(star g.V1 * r.b * r.a * g.V1) = -(r.a * r.b * (star g.V1 * g.V1)) := by
    ring
  have h2 : star g.V1 * r.b ^ 2 * g.V1 = r.b ^ 2 * (star g.V1 * g.V1) := by
    ring
  have h3 : r.b * star g.V2 * r.a * g.V1 = r.a * r.b * (star g.V2 * g.V1) := by
    ring
  have h4 : star g.V2 * r.a ^ 2 * g.V2 = r.a ^ 2 * (star g.V2 * g.V2) := by
    ring
  rw [h1, h2, h3, h4, g.V1_isometry, g.V2_isometry,
    g.V1_V2_orthogonal, g.V2_V1_orthogonal]
  simp

def nativeRotatedCuntzGenerators (r : SelfAdjointNormalizedPairNative R)
    (g : ToeplitzCuntzGenerators R) : ToeplitzCuntzGenerators R where
  V1 := nativeRotationV1 r g
  V2 := nativeRotationV2 r g
  V1_isometry := nativeRotationV1_isometry r g
  V2_isometry := nativeRotationV2_isometry r g
  V1_V2_orthogonal := nativeRotationV1_V2_orthogonal r g
  V2_V1_orthogonal := nativeRotationV2_V1_orthogonal r g

end InfoGeometry.Canonical
