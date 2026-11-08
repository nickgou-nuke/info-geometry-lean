import Mathlib.Algebra.Group.Defs
import InfoGeometry.Canonical.KleinPresentedGroup

/-!
# Central-involution relation at the Klein presentation boundary

This module proves the exact group-theoretic relation needed when a generator
maps to a central involution. It does not define a Pin group, a frame bundle,
a geometric lift, or a classification of Pin structures on a surface. Those
require a specified extension map to the orthogonal group and bundle data.
-/

namespace InfoGeometry.Topology.KleinPinStructures

/-- If `z` is central and has square one, conjugation by any group element
fixes each of `1` and `z`, both of which are their own inverses. -/
theorem conjugate_central_involution_is_inverse
    {G : Type*} [Group G] (a z b : G)
    (hz : z * z = 1)
    (hz_central : ∀ g : G, z * g = g * z)
    (hb : b = 1 ∨ b = z) :
    a * b * a⁻¹ = b⁻¹ := by
  rcases hb with hb | hb
  · rw [hb]
    simp
  · rw [hb]
    calc
      a * z * a⁻¹ = z * a * a⁻¹ := by rw [hz_central]
      _ = z := by simp
      _ = z⁻¹ := by
        exact eq_inv_of_mul_eq_one_left hz

end InfoGeometry.Topology.KleinPinStructures
