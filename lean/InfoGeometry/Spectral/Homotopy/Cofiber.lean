import InfoGeometry.Spectral.Homotopy.Suspension
import InfoGeometry.Algebra.FiniteSpinAlgebra

/-!
# Pointed cofiber-sequence interface

The old Spectral project used a topological cofiber construction.  The
current Lean 4 port keeps that construction explicit: this module records a
pointed sequence and its null composite, while leaving any realization of a
cofiber to a separate owner.
-/

namespace InfoGeometry.Spectral.Homotopy.Cofiber

open InfoGeometry.Spectral.Homotopy.Suspension

/-- A pointed sequence with a specified cofiber carrier and null composite. -/
structure CofiberSequence (X Y C : PointedReadout) where
  map : PointedMap X Y
  inclusion : PointedMap Y C
  null_composite : ∀ x : X.carrier, inclusion (map x) = C.base

namespace CofiberSequence

variable {X Y C : PointedReadout} (S : CofiberSequence X Y C)

@[simp]
theorem map_base : S.map X.base = Y.base :=
  S.map.map_base

@[simp]
theorem inclusion_base : S.inclusion Y.base = C.base :=
  S.inclusion.map_base

theorem composite_base (x : X.carrier) :
    S.inclusion (S.map x) = C.base :=
  S.null_composite x

/-- The sequence induces a pointed map from the source to the cofiber. -/
def composite : PointedMap X C where
  toFun := fun x => S.inclusion (S.map x)
  map_base := by
    rw [S.map_base]
    exact S.inclusion_base

@[simp]
theorem composite_apply (x : X.carrier) :
    S.composite x = S.inclusion (S.map x) :=
  rfl

end CofiberSequence

end InfoGeometry.Spectral.Homotopy.Cofiber
