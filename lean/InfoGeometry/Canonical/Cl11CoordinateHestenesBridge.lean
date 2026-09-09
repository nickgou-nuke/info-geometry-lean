import InfoGeometry.Clifford.Cl11CoordinateAlgebra
import InfoGeometry.Canonical.HestenesDiracAdjoint

set_option autoImplicit false

/-!
# Coordinate `Cl(1,1)` and the Hestenes split-quaternion packet

This module identifies the two existing native coordinate owners. It does not
introduce another multiplication table: it transports the `Cl(1,1)`
coordinates to the generic Hestenes split-quaternion coordinates and proves
that multiplication, the three canonical Clifford involutions, the quadratic
norm, and its polarized bilinear form agree.
-/

namespace InfoGeometry.Canonical.Cl11CoordinateHestenesBridge

open InfoGeometry.Clifford.Cl11CoordinateAlgebra

abbrev HestenesCl11 :=
  InfoGeometry.Canonical.HestenesDiracAdjoint.SplitQuaternion ℝ

/-- Coordinate-preserving map from the finite `Cl(1,1)` owner to the generic
Hestenes split-quaternion owner. -/
def toHestenes (q : Cl11) : HestenesCl11 :=
  ⟨q.s, q.e1, q.e2, q.e12⟩

/-- Inverse coordinate map. -/
def ofHestenes (q : HestenesCl11) : Cl11 :=
  ⟨q.re, q.e, q.f, q.ef⟩

@[simp] theorem ofHestenes_toHestenes (q : Cl11) :
    ofHestenes (toHestenes q) = q := by
  rfl

@[simp] theorem toHestenes_ofHestenes (q : HestenesCl11) :
    toHestenes (ofHestenes q) = q := by
  rfl

/-- The two native four-coordinate carriers are equivalent. -/
def coordinateEquiv : Cl11 ≃ HestenesCl11 where
  toFun := toHestenes
  invFun := ofHestenes
  left_inv := ofHestenes_toHestenes
  right_inv := toHestenes_ofHestenes

@[simp] theorem toHestenes_zero : toHestenes 0 = 0 := by
  rfl

@[simp] theorem toHestenes_one : toHestenes 1 = 1 := by
  rfl

@[simp] theorem toHestenes_add (q r : Cl11) :
    toHestenes (q + r) = toHestenes q + toHestenes r := by
  rfl

@[simp] theorem toHestenes_neg (q : Cl11) :
    toHestenes (-q) = -toHestenes q := by
  rfl

@[simp] theorem toHestenes_smul (a : ℝ) (q : Cl11) :
    toHestenes (a • q) = a • toHestenes q := by
  rfl

@[simp] theorem toHestenes_mul (q r : Cl11) :
    toHestenes (q * r) = toHestenes q * toHestenes r := by
  change toHestenes (InfoGeometry.Clifford.Cl11CoordinateAlgebra.mul q r) = _
  ext <;>
    simp [toHestenes, InfoGeometry.Clifford.Cl11CoordinateAlgebra.mul] <;>
    ring

/-- Grade involution is transported without a convention change. -/
@[simp] theorem toHestenes_gradeInvolution (q : Cl11) :
    toHestenes (InfoGeometry.Clifford.Cl11CoordinateAlgebra.gradeInvolution q) =
      InfoGeometry.Canonical.HestenesDiracAdjoint.SplitQuaternion.gradeInvolution
        (toHestenes q) := by
  ext <;> simp [toHestenes, InfoGeometry.Clifford.Cl11CoordinateAlgebra.gradeInvolution,
    InfoGeometry.Canonical.HestenesDiracAdjoint.SplitQuaternion.gradeInvolution]

/-- Reversion is transported without a convention change. -/
@[simp] theorem toHestenes_reverse (q : Cl11) :
    toHestenes (InfoGeometry.Clifford.Cl11CoordinateAlgebra.reverse q) =
      InfoGeometry.Canonical.HestenesDiracAdjoint.SplitQuaternion.reversion
        (toHestenes q) := by
  ext <;> simp [toHestenes, InfoGeometry.Clifford.Cl11CoordinateAlgebra.reverse,
    InfoGeometry.Canonical.HestenesDiracAdjoint.SplitQuaternion.reversion]

/-- Clifford conjugation, rather than grade involution or reversion alone, is
the transported split-quaternion conjugation. -/
@[simp] theorem toHestenes_cliffordConjugate (q : Cl11) :
    toHestenes (InfoGeometry.Clifford.Cl11CoordinateAlgebra.cliffordConjugate q) =
      InfoGeometry.Canonical.HestenesDiracAdjoint.SplitQuaternion.cliffordConjugation
        (toHestenes q) := by
  ext <;> simp [toHestenes, InfoGeometry.Clifford.Cl11CoordinateAlgebra.cliffordConjugate,
    InfoGeometry.Clifford.Cl11CoordinateAlgebra.gradeInvolution,
    InfoGeometry.Clifford.Cl11CoordinateAlgebra.reverse,
    InfoGeometry.Canonical.HestenesDiracAdjoint.SplitQuaternion.cliffordConjugation]

/-- The coordinate Clifford conjugation is exactly grade involution after
reversion, stated in the common Hestenes carrier. -/
theorem transported_conjugation_is_grade_after_reversion (q : Cl11) :
    toHestenes (InfoGeometry.Clifford.Cl11CoordinateAlgebra.cliffordConjugate q) =
      InfoGeometry.Canonical.HestenesDiracAdjoint.SplitQuaternion.gradeInvolution
        (InfoGeometry.Canonical.HestenesDiracAdjoint.SplitQuaternion.reversion
          (toHestenes q)) := by
  rw [toHestenes_cliffordConjugate,
    InfoGeometry.Canonical.HestenesDiracAdjoint.SplitQuaternion.cliffordConjugation_eq_gradeInvolution_comp_reversion]

/-- The `(2,2)` quadratic form agrees exactly across the equivalence. -/
@[simp] theorem normSq_toHestenes (q : Cl11) :
    InfoGeometry.Canonical.HestenesDiracAdjoint.SplitQuaternion.normSq
      (toHestenes q) = InfoGeometry.Clifford.Cl11CoordinateAlgebra.splitNorm q := by
  dsimp [toHestenes, InfoGeometry.Canonical.HestenesDiracAdjoint.SplitQuaternion.normSq, splitNorm]

/-- Polarized Hestenes norm form. This is the bilinear form whose diagonal is
the split-quaternion norm. -/
def hestenesBilinear (q r : HestenesCl11) : ℝ :=
  q.re * r.re - q.e * r.e + q.f * r.f - q.ef * r.ef

@[simp] theorem hestenesBilinear_self (q : HestenesCl11) :
    hestenesBilinear q q =
      InfoGeometry.Canonical.HestenesDiracAdjoint.SplitQuaternion.normSq q := by
  simp [hestenesBilinear,
    InfoGeometry.Canonical.HestenesDiracAdjoint.SplitQuaternion.normSq, pow_two]

/-- The Krein bilinear form is preserved by the coordinate equivalence. -/
@[simp] theorem hestenesBilinear_toHestenes (q r : Cl11) :
    hestenesBilinear (toHestenes q) (toHestenes r) = kreinMetric q r := by
  rfl

/-- The scalar norm identity commutes with the carrier equivalence. -/
theorem toHestenes_mul_conjugate (q : Cl11) :
    toHestenes (q * cliffordConjugate q) =
      ⟨InfoGeometry.Canonical.HestenesDiracAdjoint.SplitQuaternion.normSq
        (toHestenes q), 0, 0, 0⟩ := by
  rw [toHestenes_mul, toHestenes_cliffordConjugate,
    InfoGeometry.Canonical.HestenesDiracAdjoint.SplitQuaternion.x_mul_cliffordConjugation]

/-- All three canonical involutions and the norm are simultaneously
intertwined by the same faithful coordinate equivalence. -/
theorem canonical_involution_norm_packet (q : Cl11) :
    toHestenes (gradeInvolution q) =
        InfoGeometry.Canonical.HestenesDiracAdjoint.SplitQuaternion.gradeInvolution
          (toHestenes q) ∧
    toHestenes (reverse q) =
        InfoGeometry.Canonical.HestenesDiracAdjoint.SplitQuaternion.reversion
          (toHestenes q) ∧
    toHestenes (cliffordConjugate q) =
        InfoGeometry.Canonical.HestenesDiracAdjoint.SplitQuaternion.cliffordConjugation
          (toHestenes q) ∧
    InfoGeometry.Canonical.HestenesDiracAdjoint.SplitQuaternion.normSq
      (toHestenes q) = splitNorm q := by
  refine ⟨toHestenes_gradeInvolution q, toHestenes_reverse q,
          toHestenes_cliffordConjugate q, normSq_toHestenes q⟩

end InfoGeometry.Canonical.Cl11CoordinateHestenesBridge
