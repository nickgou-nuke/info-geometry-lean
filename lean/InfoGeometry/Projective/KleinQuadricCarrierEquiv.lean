import InfoGeometry.Projective.KleinQuadricIncidence
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Projective.KleinQuadricPlucker

/-!
# Compatibility of the two native Klein-coordinate carriers

The repository contains two established six-coordinate Pluecker structures,
both ordered as `01,02,03,12,13,23`.  This owner gives the explicit coordinate
equivalences between them and proves that the geometric operations agree.

No third coordinate carrier is introduced.  In particular, the theorem below
lets incidence results owned by `KleinQuadricIncidence` be consumed by the
twistor/Grassmannian owners based on `KleinQuadricPlucker`.
-/

namespace InfoGeometry.Projective.KleinQuadricCarrierEquiv

namespace KQ

abbrev Vec4 (R : Type*) := InfoGeometry.Projective.KleinQuadric.Vec4 R
abbrev Plucker6 (R : Type*) := InfoGeometry.Projective.KleinQuadric.Plucker6 R

end KQ

namespace KP

abbrev Vec4 (R : Type*) := InfoGeometry.Projective.KleinQuadricPlucker.Vec4 R
abbrev Plucker6 (R : Type*) := InfoGeometry.Projective.KleinQuadricPlucker.Plucker6 R

end KP

/-- Coordinate-preserving equivalence of the two native four-vector carriers. -/
def vec4Equiv (R : Type*) : KQ.Vec4 R ≃ KP.Vec4 R where
  toFun X := ⟨X.x0, X.x1, X.x2, X.x3⟩
  invFun X := ⟨X.x0, X.x1, X.x2, X.x3⟩
  left_inv X := by cases X; rfl
  right_inv X := by cases X; rfl

/-- Coordinate-preserving equivalence of the two native Pluecker carriers. -/
def plucker6Equiv (R : Type*) : KQ.Plucker6 R ≃ KP.Plucker6 R where
  toFun P := ⟨P.p01, P.p02, P.p03, P.p12, P.p13, P.p23⟩
  invFun P := ⟨P.p01, P.p02, P.p03, P.p12, P.p13, P.p23⟩
  left_inv P := by cases P; rfl
  right_inv P := by cases P; rfl

variable {R : Type*} [CommRing R]

@[simp] theorem plucker6Equiv_wedge (u v : KQ.Vec4 R) :
    plucker6Equiv R (InfoGeometry.Projective.KleinQuadric.Vec4.wedge u v) =
      InfoGeometry.Projective.KleinQuadricPlucker.Plucker6.pluckerLine
        (vec4Equiv R u) (vec4Equiv R v) := by
  rfl

@[simp] theorem plucker6Equiv_kleinQ (P : KQ.Plucker6 R) :
    InfoGeometry.Projective.KleinQuadricPlucker.Plucker6.kleinQ
        (plucker6Equiv R P) =
      InfoGeometry.Projective.KleinQuadric.Plucker6.kleinQ P := by
  rfl

@[simp] theorem plucker6Equiv_polar (P Q : KQ.Plucker6 R) :
    InfoGeometry.Projective.KleinQuadricPlucker.Plucker6.kleinPolar
        (plucker6Equiv R P) (plucker6Equiv R Q) =
      InfoGeometry.Projective.KleinQuadric.Plucker6.polar P Q := by
  rw [InfoGeometry.Projective.KleinQuadric.Plucker6.polar_formula]
  rfl

/-- The incidence form in the first owner is literally the Klein polar form
after transport to the twistor/Grassmannian coordinate carrier. -/
theorem incidenceForm_eq_kleinPolar (P Q : KQ.Plucker6 R) :
    InfoGeometry.Projective.KleinQuadricIncidence.Plucker6.incidenceForm P Q =
      InfoGeometry.Projective.KleinQuadricPlucker.Plucker6.kleinPolar
        (plucker6Equiv R P) (plucker6Equiv R Q) := by
  rw [InfoGeometry.Projective.KleinQuadricIncidence.Plucker6.incidenceForm_eq_polar,
    plucker6Equiv_polar]

end InfoGeometry.Projective.KleinQuadricCarrierEquiv
