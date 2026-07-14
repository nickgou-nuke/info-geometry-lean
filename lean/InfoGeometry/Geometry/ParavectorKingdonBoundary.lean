import InfoGeometry.Geometry.ParavectorZornBoundary
import InfoGeometry.Algebra.Zorn.KingdonCanonicalBridge

/-!
# Paravector boundary transported to the abstract Kingdon split octonions

This file completes the carrier-transport corridor

`Minkowski4 → ZornCoord → Canonical.ZornMatrix ℝ → AbstractKingdon`.

The map is a four-dimensional quadratic boundary embedding.  It preserves the
Minkowski/Pauli determinant through the split-octonion norm.  It is not asserted
to preserve multiplication, and no operator-algebraic commutant or modular
conjugation claim is made here.
-/

noncomputable section

namespace ParavectorKingdonBoundary

open InfoGeometry.Geometry.PauliParavectorBridge
open InfoGeometry.Geometry.ParavectorZornBoundary
open InfoGeometry.Canonical.ZornVectorMatrixExplicit
open InfoGeometry.Algebra.KingdonSplitOctonion
open InfoGeometry.Algebra.Zorn
open InfoGeometry.Algebra.Zorn.KingdonCanonicalBridge

abbrev CanonicalZorn := InfoGeometry.Canonical.ZornMatrix ℝ
abbrev Kingdon := AbstractKingdon

/-- Repackage the maintained tuple-coordinate boundary as the canonical Zorn carrier. -/
noncomputable def canonicalBoundary (v : Minkowski4) : CanonicalZorn :=
  InfoGeometry.Canonical.ZornMatrix.coordEquiv.symm (zornBoundaryOfMinkowski4 v)

@[simp] theorem canonicalBoundary_a (v : Minkowski4) :
    (canonicalBoundary v).a = v.t + v.z := rfl

@[simp] theorem canonicalBoundary_b (v : Minkowski4) :
    (canonicalBoundary v).b = v.t - v.z := rfl

@[simp] theorem canonicalBoundary_x (v : Minkowski4) :
    (canonicalBoundary v).x = xyPlaneVec v.x v.y := rfl

@[simp] theorem canonicalBoundary_y (v : Minkowski4) :
    (canonicalBoundary v).y = xyPlaneVec v.x v.y := rfl

/-- The canonical Zorn determinant of the boundary point is the Minkowski form. -/
theorem canonicalBoundary_det_eq_minkowski_q (v : Minkowski4) :
    ZornMatrix.detZ realCrossProduct3 (canonicalBoundary v) = v.q := by
  change zornNorm (zornBoundaryOfMinkowski4 v) = v.q
  exact zornNorm_boundary_eq_minkowski_q v

/-- Transport the canonical boundary point through the proved Kingdon/Zorn equivalence. -/
noncomputable def kingdonBoundary (v : Minkowski4) : Kingdon :=
  kingdonCanonicalLinearEquiv.symm (canonicalBoundary v)

@[simp] theorem kingdonCanonicalLinearEquiv_boundary (v : Minkowski4) :
    kingdonCanonicalLinearEquiv (kingdonBoundary v) = canonicalBoundary v := by
  exact LinearEquiv.apply_symm_apply kingdonCanonicalLinearEquiv (canonicalBoundary v)

/-- The transported Kingdon split norm is exactly the Minkowski quadratic form. -/
theorem kingdonNorm_boundary_eq_minkowski_q (v : Minkowski4) :
    kingdonNorm (kingdonBoundary v) = v.q := by
  rw [kingdonNorm_eq_realZorn_det]
  simp only [kingdonCanonicalLinearEquiv_boundary]
  exact canonicalBoundary_det_eq_minkowski_q v

/-- The Kingdon boundary norm is the real part of the maintained Pauli determinant. -/
theorem kingdonNorm_boundary_eq_pauli_det_re (v : Minkowski4) :
    kingdonNorm (kingdonBoundary v) = (Matrix.det (pauliMatrix v)).re := by
  rw [kingdonNorm_boundary_eq_minkowski_q, det_pauliMatrix]
  simp

/-- Kingdon norm-nullness of the boundary point is exactly Minkowski nullness. -/
theorem kingdonNorm_boundary_eq_zero_iff_isNull (v : Minkowski4) :
    kingdonNorm (kingdonBoundary v) = 0 ↔ v.IsNull := by
  rw [kingdonNorm_boundary_eq_minkowski_q]
  rfl

end ParavectorKingdonBoundary

end noncomputable section
