import Mathlib
import InfoGeometry.Canonical.ZornSpinor
import InfoGeometry.Algebra.ZornVectorMatrix

namespace InfoGeometry.Algebra.Zorn.CanonicalVectorMatrixBridge

open InfoGeometry.Canonical

abbrev CZ := InfoGeometry.Canonical.ZornMatrix ℝ
abbrev VZ := InfoGeometry.Algebra.ZornVectorMatrix ℝ

noncomputable def canonicalVectorEquiv : CZ ≃ VZ where
  toFun X := ⟨X.a, X.x, X.y, X.b⟩
  invFun X := ⟨X.a, X.b, X.v, X.w⟩
  left_inv X := by cases X; rfl
  right_inv X := by cases X; rfl

@[simp] theorem canonicalVectorEquiv_apply (X : CZ) :
    canonicalVectorEquiv X = ⟨X.a, X.x, X.y, X.b⟩ := rfl

@[simp] theorem canonicalVectorEquiv_symm_apply (X : VZ) :
    canonicalVectorEquiv.symm X = ⟨X.a, X.b, X.v, X.w⟩ := rfl

@[simp] theorem canonicalVectorEquiv_zero :
    canonicalVectorEquiv (0 : CZ) = InfoGeometry.Algebra.ZornVectorMatrix.zero := by
  rfl

@[simp] theorem canonicalVectorEquiv_add (X Y : CZ) :
    canonicalVectorEquiv (X + Y) =
      InfoGeometry.Algebra.ZornVectorMatrix.add
        (canonicalVectorEquiv X) (canonicalVectorEquiv Y) := by
  rfl

@[simp] theorem canonicalVectorEquiv_sub (X Y : CZ) :
    canonicalVectorEquiv (X - Y) =
      InfoGeometry.Algebra.ZornVectorMatrix.sub
        (canonicalVectorEquiv X) (canonicalVectorEquiv Y) := by
  rfl

@[simp] theorem canonicalVectorEquiv_neg (X : CZ) :
    canonicalVectorEquiv (-X) =
      InfoGeometry.Algebra.ZornVectorMatrix.neg (canonicalVectorEquiv X) := by
  rfl

@[simp] theorem canonicalVectorEquiv_smul (r : ℝ) (X : CZ) :
    canonicalVectorEquiv (r • X) =
      InfoGeometry.Algebra.ZornVectorMatrix.smul r (canonicalVectorEquiv X) := by
  rfl

@[simp] theorem canonicalVectorEquiv_one :
    canonicalVectorEquiv (1 : CZ) = InfoGeometry.Algebra.ZornVectorMatrix.one := by
  rfl

@[simp] theorem canonicalVectorEquiv_symm_zero :
    canonicalVectorEquiv.symm InfoGeometry.Algebra.ZornVectorMatrix.zero = (0 : CZ) := by
  apply canonicalVectorEquiv.injective
  simp only [Equiv.apply_symm_apply, canonicalVectorEquiv_zero]

@[simp] theorem canonicalVectorEquiv_symm_add (X Y : VZ) :
    canonicalVectorEquiv.symm (InfoGeometry.Algebra.ZornVectorMatrix.add X Y) =
      canonicalVectorEquiv.symm X + canonicalVectorEquiv.symm Y := by
  apply canonicalVectorEquiv.injective
  simp only [Equiv.apply_symm_apply, canonicalVectorEquiv_add]

@[simp] theorem canonicalVectorEquiv_symm_smul (r : ℝ) (X : VZ) :
    canonicalVectorEquiv.symm (InfoGeometry.Algebra.ZornVectorMatrix.smul r X) =
      r • canonicalVectorEquiv.symm X := by
  apply canonicalVectorEquiv.injective
  simp only [Equiv.apply_symm_apply, canonicalVectorEquiv_smul]

@[simp] theorem canonicalVectorEquiv_symm_neg (X : VZ) :
    canonicalVectorEquiv.symm (InfoGeometry.Algebra.ZornVectorMatrix.neg X) =
      -canonicalVectorEquiv.symm X := by
  apply canonicalVectorEquiv.injective
  simp only [Equiv.apply_symm_apply, canonicalVectorEquiv_neg]

@[simp] theorem canonicalVectorEquiv_symm_sub (X Y : VZ) :
    canonicalVectorEquiv.symm (InfoGeometry.Algebra.ZornVectorMatrix.sub X Y) =
      canonicalVectorEquiv.symm X - canonicalVectorEquiv.symm Y := by
  apply canonicalVectorEquiv.injective
  simp only [Equiv.apply_symm_apply, canonicalVectorEquiv_sub]

@[simp] theorem canonicalVectorEquiv_symm_one :
    canonicalVectorEquiv.symm InfoGeometry.Algebra.ZornVectorMatrix.one = (1 : CZ) := by
  apply canonicalVectorEquiv.injective
  simp only [Equiv.apply_symm_apply, canonicalVectorEquiv_one]

@[simp] theorem canonicalVectorEquiv_mul (X Y : CZ) :
    canonicalVectorEquiv (X * Y) =
      InfoGeometry.Algebra.ZornVectorMatrix.mul
        (canonicalVectorEquiv X) (canonicalVectorEquiv Y) := by
  apply InfoGeometry.Algebra.ZornVectorMatrix.ext
  · change X.a * Y.a + InfoGeometry.Canonical.ZornMatrix.dot X.x Y.y =
      X.a * Y.a + InfoGeometry.Algebra.ZornVec3.dot X.x Y.y
    simp [InfoGeometry.Canonical.ZornMatrix.dot, InfoGeometry.Algebra.ZornVec3.dot,
      Fin.sum_univ_three]
  · funext i
    change X.a * Y.x i + Y.b * X.x i -
        InfoGeometry.Canonical.ZornMatrix.cross X.y Y.y i =
      X.a * Y.x i + Y.b * X.x i -
        InfoGeometry.Algebra.ZornVec3.cross X.y Y.y i
    fin_cases i <;>
      simp [InfoGeometry.Canonical.ZornMatrix.cross,
        InfoGeometry.Algebra.ZornVec3.cross]
  · funext i
    change X.b * Y.y i + Y.a * X.y i +
        InfoGeometry.Canonical.ZornMatrix.cross X.x Y.x i =
      Y.a * X.y i + X.b * Y.y i +
        InfoGeometry.Algebra.ZornVec3.cross X.x Y.x i
    fin_cases i <;>
      simp [InfoGeometry.Canonical.ZornMatrix.cross,
        InfoGeometry.Algebra.ZornVec3.cross] <;>
      ring
  · change X.b * Y.b + InfoGeometry.Canonical.ZornMatrix.dot X.y Y.x =
      InfoGeometry.Algebra.ZornVec3.dot X.y Y.x + X.b * Y.b
    simp [InfoGeometry.Canonical.ZornMatrix.dot, InfoGeometry.Algebra.ZornVec3.dot,
      Fin.sum_univ_three]
    ring

@[simp] theorem canonicalVectorEquiv_symm_mul (X Y : VZ) :
    canonicalVectorEquiv.symm (InfoGeometry.Algebra.ZornVectorMatrix.mul X Y) =
      canonicalVectorEquiv.symm X * canonicalVectorEquiv.symm Y := by
  apply canonicalVectorEquiv.injective
  simp only [Equiv.apply_symm_apply, canonicalVectorEquiv_mul]

theorem add_mul (X Y Z : CZ) : (X + Y) * Z = X * Z + Y * Z := by
  apply canonicalVectorEquiv.injective
  simp only [canonicalVectorEquiv_mul, canonicalVectorEquiv_add]
  exact InfoGeometry.Algebra.ZornVectorMatrix.add_mul _ _ _

theorem mul_add (X Y Z : CZ) : X * (Y + Z) = X * Y + X * Z := by
  apply canonicalVectorEquiv.injective
  simp only [canonicalVectorEquiv_mul, canonicalVectorEquiv_add]
  exact InfoGeometry.Algebra.ZornVectorMatrix.mul_add _ _ _

theorem smul_mul (r : ℝ) (X Y : CZ) : (r • X) * Y = r • (X * Y) := by
  apply canonicalVectorEquiv.injective
  simp only [canonicalVectorEquiv_mul, canonicalVectorEquiv_smul]
  exact InfoGeometry.Algebra.ZornVectorMatrix.smul_mul r _ _

theorem mul_smul (r : ℝ) (X Y : CZ) : X * (r • Y) = r • (X * Y) := by
  apply canonicalVectorEquiv.injective
  simp only [canonicalVectorEquiv_mul, canonicalVectorEquiv_smul]
  exact InfoGeometry.Algebra.ZornVectorMatrix.mul_smul r _ _

theorem sub_mul (X Y Z : CZ) : (X - Y) * Z = X * Z - Y * Z := by
  apply canonicalVectorEquiv.injective
  simp only [canonicalVectorEquiv_mul, canonicalVectorEquiv_sub]
  exact InfoGeometry.Algebra.ZornVectorMatrix.sub_mul _ _ _

theorem mul_sub (X Y Z : CZ) : X * (Y - Z) = X * Y - X * Z := by
  apply canonicalVectorEquiv.injective
  simp only [canonicalVectorEquiv_mul, canonicalVectorEquiv_sub]
  exact InfoGeometry.Algebra.ZornVectorMatrix.mul_sub _ _ _

@[simp] theorem zero_mul (X : CZ) : (0 : CZ) * X = 0 := by
  apply canonicalVectorEquiv.injective
  simp only [canonicalVectorEquiv_mul, canonicalVectorEquiv_zero]
  exact InfoGeometry.Algebra.ZornVectorMatrix.zero_mul _

@[simp] theorem mul_zero (X : CZ) : X * (0 : CZ) = 0 := by
  apply canonicalVectorEquiv.injective
  simp only [canonicalVectorEquiv_mul, canonicalVectorEquiv_zero]
  exact InfoGeometry.Algebra.ZornVectorMatrix.mul_zero _

@[simp] theorem mul_one (X : CZ) : X * (1 : CZ) = X := by
  apply canonicalVectorEquiv.injective
  simp only [canonicalVectorEquiv_mul, canonicalVectorEquiv_one]
  exact InfoGeometry.Algebra.ZornVectorMatrix.mul_one _

@[simp] theorem one_mul (X : CZ) : (1 : CZ) * X = X := by
  apply canonicalVectorEquiv.injective
  simp only [canonicalVectorEquiv_mul, canonicalVectorEquiv_one]
  exact InfoGeometry.Algebra.ZornVectorMatrix.one_mul _

end InfoGeometry.Algebra.Zorn.CanonicalVectorMatrixBridge
