import InfoGeometry.Lie.SplitOctonionEllCircularPeirceBasis
import InfoGeometry.Lie.SplitOctonionErlangenInvariant

/-!
# Native quadratic transport for the `Ell` circular basis

This owner records the quadratic-form transport before any explicit coordinate
polynomial is expanded.  The `Ell` circular coordinates are the genuine
`Module.Basis.equivFun` coordinates of the nonassociative carrier, and the
quadratic form is pulled back from the native Zorn determinant.
-/

noncomputable section

namespace InfoGeometry.Lie.SplitOctonionEllCircularPolarTransport

open InfoGeometry.Lie.SplitOctonionEllCircularPeirceBasis
open InfoGeometry.Lie.SplitOctonionErlangenInvariant

abbrev CanonicalZorn :=
  InfoGeometry.Algebra.Zorn.KingdonCanonicalBridge.CanonicalZorn

abbrev Coordinate := Fin 8 → ℝ

/-- The native determinant quadratic form in `Ell` circular coordinates. -/
noncomputable def ellCircularQuadratic : QuadraticForm ℝ Coordinate :=
  canonicalDetQuadratic.comp coordinateEquiv.symm

@[simp] theorem ellCircularQuadratic_apply (x : Coordinate) :
    ellCircularQuadratic x =
      canonicalDetQuadratic (coordinateEquiv.symm x) :=
  rfl

/-- The polar form is transported by the same circular coordinate map. -/
theorem ellCircularPolar_apply (x y : Coordinate) :
    QuadraticMap.polar ellCircularQuadratic x y =
      QuadraticMap.polar canonicalDetQuadratic
        (coordinateEquiv.symm x) (coordinateEquiv.symm y) := by
  simp [ellCircularQuadratic, QuadraticMap.polar]

/-- Pulling the transported polar form back to the native carrier recovers the
native determinant polar form. -/
@[simp] theorem ellCircularPolar_coordinateEquiv
    (X Y : CanonicalZorn) :
    QuadraticMap.polar ellCircularQuadratic
        (coordinateEquiv X) (coordinateEquiv Y) =
      QuadraticMap.polar canonicalDetQuadratic X Y := by
  rw [ellCircularPolar_apply]
  simp

/-- The coordinate equivalence is an isometry for the pulled-back form. -/
noncomputable def ellCircularQuadraticIsometry :
    canonicalDetQuadratic.IsometryEquiv ellCircularQuadratic :=
  { coordinateEquiv with
    map_app' := fun X => by
      change canonicalDetQuadratic
        (coordinateEquiv.symm (coordinateEquiv X)) = canonicalDetQuadratic X
      rw [coordinateEquiv.symm_apply_apply] }

@[simp] theorem ellCircularQuadraticIsometry_apply (X : CanonicalZorn) :
    ellCircularQuadratic (ellCircularQuadraticIsometry X) =
      canonicalDetQuadratic X :=
  ellCircularQuadraticIsometry.map_app X

@[simp] theorem ellCircularQuadraticIsometry_symm_apply (x : Coordinate) :
    canonicalDetQuadratic (ellCircularQuadraticIsometry.symm x) =
      ellCircularQuadratic x :=
  ellCircularQuadraticIsometry.symm.map_app x

end InfoGeometry.Lie.SplitOctonionEllCircularPolarTransport
