import InfoGeometry.Canonical.D6GlideSectorBundle
import InfoGeometry.Algebra.FiniteSpinAlgebra

/-!
# D6 symmetry on the finite Klein glide quotient

This owner closes the seam between the finite Klein glide quotient and the
six-mode dihedral label action.  The quotient, sector rotation, and sector
reflection are inherited from their native owners; this file only exposes
their combined dihedral packet.
-/

namespace InfoGeometry.Canonical.D6KleinGlideDihedralBridge

open InfoGeometry.Canonical.D6SixModeAction
open InfoGeometry.Canonical.D6GlideSectorBundle
open InfoGeometry.Canonical.D6HexTiledKleinBottleQuotient

theorem quotientSectorRotate_sixth
    (q : D6KleinSectorBundle) :
    quotientSectorRotate (6 : D6Index) q = q := by
  refine Quotient.inductionOn q ?_
  intro p
  rcases p with ⟨s, p⟩
  change Quotient.mk' (s + (6 : D6Index), p) = Quotient.mk' (s, p)
  have h6 : (6 : D6Index) = 0 := ZMod.natCast_self 6
  rw [h6, add_zero]

theorem d6Klein_glide_dihedral_packet
    (q : D6KleinSectorBundle) :
    (∀ k l : D6Index,
      quotientSectorRotate (k + l) q =
        quotientSectorRotate l (quotientSectorRotate k q)) ∧
      quotientSectorRotate (6 : D6Index) q = q ∧
      quotientSectorReflect (quotientSectorReflect q) = q ∧
      (∀ k : D6Index,
        quotientSectorReflect (quotientSectorRotate k
          (quotientSectorReflect q)) = quotientSectorRotate (-k) q) := by
  refine ⟨?_, quotientSectorRotate_sixth q,
    quotientSectorReflect_involutive q, ?_⟩
  · intro k l
    exact quotientSectorRotate_add k l q
  · intro k
    exact quotientSectorReflect_conjugates_rotate k q

theorem d6Klein_glide_sectorMap_packet
    (s : D6Index)
    (p : D6HexTiledKleinBottleQuotient.TorusCell) :
    sectorMap s (glide p) = sectorMap s p ∧
      quotientSectorRotate 0 (sectorMap s p) = sectorMap s p ∧
      quotientSectorReflect (sectorMap s p) = sectorMap (-s) p := by
  exact ⟨sectorMap_glide s p,
    by simpa using quotientSectorRotate_map 0 s p,
    quotientSectorReflect_map s p⟩

end InfoGeometry.Canonical.D6KleinGlideDihedralBridge
