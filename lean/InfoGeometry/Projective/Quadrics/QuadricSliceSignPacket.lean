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

namespace InfoGeometry.Projective.Quadrics.QuadricSliceSignPacket

open AffineSlices
open SignatureDeterminant

/--
Finite projective-quadric packet:

* the canonical affine slice equivalences for the three unit-coefficient charts;
* the determinant-sign packet for the canonical homogeneous representatives.

This is a packaging surface only.  It does not claim any general `PGL₄(ℝ)`
classification of quadrics.
-/
theorem canonical_quadric_slice_sign_packet (x y z : ℝ) :
    (ellipsoidAff x y z ↔
      ellipsoidHom (⟨x, y, z, (1 : ℝ)⟩) = 0) ∧
    (hyperboloidAff x y z ↔
      hyperboloidHom (⟨x, y, z, (1 : ℝ)⟩) = 0) ∧
    (paraboloidAff x y z ↔
      paraboloidHom (⟨x, y, z, (1 : ℝ)⟩) = 0) ∧
    (Matrix.det ellipsoidQuadric = (-1 : ℝ) ∧
      Matrix.det hyperboloidQuadric = (1 : ℝ) ∧
      Matrix.det paraboloidQuadric = (-1 : ℝ)) := by
  exact ⟨
    ellipsoidAff_iff_homogeneous_one (R := ℝ) x y z,
    hyperboloidAff_iff_homogeneous_one (R := ℝ) x y z,
    paraboloidAff_iff_homogeneous_one (R := ℝ) x y z,
    determinant_sign_packet
  ⟩

end InfoGeometry.Projective.Quadrics.QuadricSliceSignPacket
