import InfoGeometry.Optics.Cl11SplitQuaternionQGTSoldering
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Algebra.ZornVectorMatrix

set_option autoImplicit false

/-!
# Clifford conjugation through matrix and native Zorn soldering

The existing `Cl(1,1)` coordinate representation is transported through the
real split-quaternion matrix packet and one fixed-colour associative plane of
the native Zorn carrier.  The same anti-involution and quadratic norm are
proved to commute with every representation map.
-/

noncomputable section

namespace InfoGeometry.Optics.Cl11SplitQuaternionConjugationSoldering

open InfoGeometry.Algebra
open InfoGeometry.Algebra.ZornMatrix
open InfoGeometry.Clifford.Cl11CoordinateAlgebra
open InfoGeometry.Canonical.SplitOctonionFixedColorCl11Bridge
open InfoGeometry.Optics.Cl11SplitQuaternionQGTSoldering

/-- Standard split-octonion conjugation on the native Zorn carrier. -/
def nativeConjugate (X : Native) : Native :=
  { a := X.b
    v := fun j => -X.v j
    w := fun j => -X.w j
    b := X.a }

/-- Coordinate identity from the older native Zorn carrier to the repository's
fully developed vector-matrix owner. -/
def toVectorMatrix (X : Native) : ZornVectorMatrix ℝ :=
  ⟨X.a, X.v, X.w, X.b⟩

theorem toVectorMatrix_injective : Function.Injective toVectorMatrix := by
  intro X Y h
  cases X
  cases Y
  simpa [toVectorMatrix] using h

theorem nativeVec3_dot_eq_vectorDot (v w : Vec3 ℝ) :
    Vec3.dot v w = ZornVec3.dot v w := by
  simp [Vec3.dot, ZornVec3.dot, Fin.sum_univ_three]

theorem nativeVec3_cross_eq_vectorCross (v w : Vec3 ℝ) :
    Vec3.cross v w = ZornVec3.cross v w := by
  ext j
  fin_cases j <;> simp [Vec3.cross, ZornVec3.cross]

@[simp] theorem toVectorMatrix_nativeConjugate (X : Native) :
    toVectorMatrix (nativeConjugate X) = ZornVectorMatrix.conj (toVectorMatrix X) := by
  rfl

set_option maxHeartbeats 800000 in
@[simp] theorem toVectorMatrix_mul (X Y : Native) :
    toVectorMatrix (X * Y) =
      ZornVectorMatrix.mul (toVectorMatrix X) (toVectorMatrix Y) := by
  change toVectorMatrix (ZornMatrix.mul X Y) = _
  apply ZornVectorMatrix.ext
  · simp [toVectorMatrix, ZornMatrix.mul, ZornVectorMatrix.mul,
      nativeVec3_dot_eq_vectorDot]
  · funext j
    fin_cases j <;>
      simp [toVectorMatrix, ZornMatrix.mul, ZornVectorMatrix.mul,
        Vec3.add, Vec3.sub, Vec3.smul, Vec3.cross, ZornVec3.cross]
  · funext j
    fin_cases j <;>
      simp [toVectorMatrix, ZornMatrix.mul, ZornVectorMatrix.mul,
        Vec3.add, Vec3.smul, Vec3.cross, ZornVec3.cross]
  · simp [toVectorMatrix, ZornMatrix.mul, ZornVectorMatrix.mul,
      nativeVec3_dot_eq_vectorDot]

@[simp] theorem nativeConjugate_involutive (X : Native) :
    nativeConjugate (nativeConjugate X) = X := by
  ext j <;> simp [nativeConjugate]

/-- Native Zorn conjugation reverses the non-associative composition product. -/
theorem nativeConjugate_mul (X Y : Native) :
    nativeConjugate (X * Y) = nativeConjugate Y * nativeConjugate X := by
  apply toVectorMatrix_injective
  simp only [toVectorMatrix_nativeConjugate, toVectorMatrix_mul,
    ZornVectorMatrix.conj_mul]

@[simp] theorem nativeConjugate_fixedColorReadout
    (i : Fin 3) (A : Mat2) :
    nativeConjugate (fixedColorReadout i A) =
      fixedColorReadout i (splitQuaternionMatrixConjugate A) := by
  apply ZornMatrix.ext
  · rfl
  · funext j
    fin_cases i <;> fin_cases j <;>
      simp [nativeConjugate, fixedColorReadout,
        splitQuaternionMatrixConjugate, Vec3.basis]
  · funext j
    fin_cases i <;> fin_cases j <;>
      simp [nativeConjugate, fixedColorReadout,
        splitQuaternionMatrixConjugate, Vec3.basis]
  · rfl

/-- Clifford conjugation commutes with every fixed-colour Zorn realization. -/
@[simp] theorem nativeConjugate_cl11FixedColorSplitOctonion
    (i : Fin 3) (q : Cl11) :
    nativeConjugate (cl11FixedColorSplitOctonion i q) =
      cl11FixedColorSplitOctonion i (cliffordConjugate q) := by
  rw [cl11FixedColorSplitOctonion, nativeConjugate_fixedColorReadout,
    cl11FixedColorSplitOctonion,
    cl11SplitQuaternionMatrix_cliffordConjugate]

/-- The native Zorn quadratic norm of a fixed-colour matrix readout is its
`2 × 2` determinant. -/
theorem zornNorm_fixedColorReadout (i : Fin 3) (A : Mat2) :
    zornNorm (fixedColorReadout i A) = Matrix.det A := by
  fin_cases i <;>
    simp [zornNorm, fixedColorReadout, Vec3.dot, Vec3.basis,
      Matrix.det_fin_two]

/-- The complete coordinate → matrix → fixed-colour Zorn chain preserves the
split-quaternion `(2,2)` norm. -/
theorem zornNorm_cl11FixedColorSplitOctonion (i : Fin 3) (q : Cl11) :
    zornNorm (cl11FixedColorSplitOctonion i q) = splitNorm q := by
  calc
    zornNorm (cl11FixedColorSplitOctonion i q) =
        Matrix.det (cl11SplitQuaternionMatrix q) := by
      rw [cl11FixedColorSplitOctonion, zornNorm_fixedColorReadout]
    _ = InfoGeometry.Algebra.SplitQuaternionMatrices.det2
        (cl11SplitQuaternionMatrix q) := by
      simp [InfoGeometry.Algebra.SplitQuaternionMatrices.det2,
        Matrix.det_fin_two]
    _ = splitNorm q := det2_cl11SplitQuaternionMatrix q

/-- The Zorn conjugation and norm compatibility packet for the embedded
`Cl(1,1)` algebra. -/
theorem fixedColor_conjugation_norm_packet (i : Fin 3) (q : Cl11) :
    nativeConjugate (cl11FixedColorSplitOctonion i q) =
        cl11FixedColorSplitOctonion i (cliffordConjugate q) ∧
      zornNorm (cl11FixedColorSplitOctonion i q) = splitNorm q := by
  exact ⟨nativeConjugate_cl11FixedColorSplitOctonion i q,
    zornNorm_cl11FixedColorSplitOctonion i q⟩

end InfoGeometry.Optics.Cl11SplitQuaternionConjugationSoldering
