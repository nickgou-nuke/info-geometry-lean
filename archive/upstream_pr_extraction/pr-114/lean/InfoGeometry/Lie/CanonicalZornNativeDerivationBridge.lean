import InfoGeometry.Algebra.NonAssocDerivation
import InfoGeometry.Lie.CanonicalZornDerivation

/-!
# Predicate bridge for canonical Zorn derivations

The canonical Zorn owner predates the generic native derivation interface.  Its
selector and Mathlib's `IsLeibniz` selector have the same proposition, but this
fact is made explicit here so later operator-lane constructions do not rely on
definitional coincidence across owner files.
-/

namespace InfoGeometry.Lie.CanonicalZornDerivation

open InfoGeometry.Algebra.NonAssocDerivation

theorem isDerivation_iff_nativeIsLeibniz (D : EndCZ) :
    IsDerivation D ↔ InfoGeometry.Algebra.NonAssocDerivation.IsLeibniz ℝ CZ D := by
  rfl

theorem mem_canonicalZornDerivations_iff_native (D : EndCZ) :
    D ∈ canonicalZornDerivations ↔
      InfoGeometry.Algebra.NonAssocDerivation.IsLeibniz ℝ CZ D := by
  exact isDerivation_iff_nativeIsLeibniz D

end InfoGeometry.Lie.CanonicalZornDerivation
