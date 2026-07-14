import InfoGeometry.Projective.Quadrics.AffineSlices
import InfoGeometry.Projective.Quadrics.SignatureDeterminant

/-!
# Quadric slice/sign packet

This file packages the already-proved finite quadric surface facts into one
small theorem surface:

* the `w = 1` affine slice equivalences for the canonical unit-coefficient
  ellipsoid, one-sheet hyperboloid, and elliptic paraboloid charts;
* the determinant-sign packet for the canonical homogeneous representatives.

It does not attempt any general `PGL₄(ℝ)` classification of arbitrary real
quadrics.
-/

namespace QuadricSliceSignPacket

open InfoGeometry.Projective.Quadrics.AffineSlices
open InfoGeometry.Projective.Quadrics.SignatureDeterminant

/--
Finite projective-quadric packet:

* the canonical affine slice equivalences for the three unit-coefficient charts;
* the determinant-sign packet for the canonical homogeneous representatives.

This is a packaging surface only.  It does not claim any general `PGL₄(ℝ)`
classification of quadrics.
-/
structure CanonicalQuadricSliceSignPacket (x y z : ℝ) where
  ellipsoid : ellipsoidAff x y z ↔ ellipsoidHom (⟨x, y, z, (1 : ℝ)⟩) = 0
  hyperboloid : hyperboloidAff x y z ↔ hyperboloidHom (⟨x, y, z, (1 : ℝ)⟩) = 0
  paraboloid : paraboloidAff x y z ↔ paraboloidHom (⟨x, y, z, (1 : ℝ)⟩) = 0
  determinant :
    Matrix.det ellipsoidQuadric = (-1 : ℝ) ∧
      Matrix.det hyperboloidQuadric = (1 : ℝ) ∧
      Matrix.det paraboloidQuadric = (-1 : ℝ)

/--
Construct the canonical finite packet from the already-proved lemmas.
-/
def canonical_quadric_slice_sign_packet (x y z : ℝ) :
    CanonicalQuadricSliceSignPacket x y z where
  ellipsoid := ellipsoidAff_iff_homogeneous_one (R := ℝ) x y z
  hyperboloid := hyperboloidAff_iff_homogeneous_one (R := ℝ) x y z
  paraboloid := paraboloidAff_iff_homogeneous_one (R := ℝ) x y z
  determinant := determinant_sign_packet

end QuadricSliceSignPacket
