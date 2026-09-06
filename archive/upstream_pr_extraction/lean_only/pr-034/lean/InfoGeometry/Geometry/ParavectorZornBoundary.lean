import InfoGeometry.Geometry.PauliParavectorBridge
import InfoGeometry.Canonical.ZornVectorMatrixExplicit

/-!
# Paravector/Zorn boundary map

This module is the small constructive bridge between the Pauli paravector
model and the explicit Zorn vector-matrix model.

It does **not** prove a Frobenius/Hurwitz classification theorem and does not
identify Clifford paravectors with split octonions.  It only proves the finite
coordinate boundary fact:

`(t,x,y,z) ↦ [[t+z, (x,y,0)], [(x,y,0), t-z]]`

has Zorn reduced norm `t² - x² - y² - z²`, the same scalar readout as the
Pauli determinant/Minkowski norm.
-/

namespace InfoGeometry.Geometry.ParavectorZornBoundary

open InfoGeometry.Canonical.ZornVectorMatrixExplicit
open InfoGeometry.Geometry.PauliParavectorBridge

/-! ## Coordinate embedding -/

/-- Embed the transverse `(x,y)` plane into the `Fin 3` vector slot. -/
def xyPlaneVec (x y : ℝ) : Vec3 :=
  ![x, y, 0]

/--
Boundary map from a Pauli/Minkowski paravector to the explicit Zorn model.

The diagonal entries are light-cone coordinates `t+z` and `t-z`; the vector
slots carry the transverse plane twice.  This is a norm-preserving boundary
map, not a multiplication-preserving algebra isomorphism.
-/
def zornBoundaryOfMinkowski4 (v : Minkowski4) : ZornCoord :=
  zornMk (v.t + v.z) (v.t - v.z) (xyPlaneVec v.x v.y) (xyPlaneVec v.x v.y)

@[simp] theorem zornA_boundary (v : Minkowski4) :
    zornA (zornBoundaryOfMinkowski4 v) = v.t + v.z := by
  rfl

@[simp] theorem zornB_boundary (v : Minkowski4) :
    zornB (zornBoundaryOfMinkowski4 v) = v.t - v.z := by
  rfl

@[simp] theorem zornX_boundary (v : Minkowski4) :
    zornX (zornBoundaryOfMinkowski4 v) = xyPlaneVec v.x v.y := by
  rfl

@[simp] theorem zornY_boundary (v : Minkowski4) :
    zornY (zornBoundaryOfMinkowski4 v) = xyPlaneVec v.x v.y := by
  rfl

/-! ## Norm and null-cone compatibility -/

/-- The Zorn reduced norm of the boundary representative is the Minkowski norm. -/
theorem zornNorm_boundary_eq_minkowski_q (v : Minkowski4) :
    zornNorm (zornBoundaryOfMinkowski4 v) = v.q := by
  simp [zornBoundaryOfMinkowski4, xyPlaneVec, zornNorm, zornMk, zornA, zornB,
    zornX, zornY, dot3, Minkowski4.q]
  ring

/-- The Zorn trace of the boundary representative is twice the time component. -/
theorem zornTrace_boundary_eq_two_time (v : Minkowski4) :
    zornTrace (zornBoundaryOfMinkowski4 v) = 2 * v.t := by
  simp [zornBoundaryOfMinkowski4, zornTrace, zornMk, zornA, zornB]
  ring

/-- Zorn nullness of the boundary representative is exactly paravector nullness. -/
theorem isZornNull_boundary_iff_isNull (v : Minkowski4) :
    IsZornNull (zornBoundaryOfMinkowski4 v) ↔ v.IsNull := by
  simp [IsZornNull, Minkowski4.IsNull, zornNorm_boundary_eq_minkowski_q]

/--
The Zorn norm of the boundary representative agrees with the real part of the
Pauli determinant.
-/
theorem zornNorm_boundary_eq_pauli_det_re (v : Minkowski4) :
    zornNorm (zornBoundaryOfMinkowski4 v) = (Matrix.det (pauliMatrix v)).re := by
  rw [zornNorm_boundary_eq_minkowski_q, det_pauliMatrix]
  simp

/--
The explicit Zorn quadratic-rank equation specializes to every paravector
boundary representative.
-/
theorem zornBoundary_quadratic_rank (v : Minkowski4) :
    zornMul (zornBoundaryOfMinkowski4 v) (zornBoundaryOfMinkowski4 v)
      - zornTrace (zornBoundaryOfMinkowski4 v) • zornBoundaryOfMinkowski4 v
      + zornNorm (zornBoundaryOfMinkowski4 v) • zornOne = 0 :=
  zornMul_self_quadratic_rank (zornBoundaryOfMinkowski4 v)

end InfoGeometry.Geometry.ParavectorZornBoundary
