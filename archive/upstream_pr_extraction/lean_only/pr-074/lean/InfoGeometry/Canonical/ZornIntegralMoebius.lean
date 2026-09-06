import Mathlib
import InfoGeometry.Algebra.ZornVectorMatrix
import InfoGeometry.Canonical.StandardIntegralSplitOctonionMultiplication
import InfoGeometry.Canonical.ZornVectorMatrixRationalEquiv

namespace InfoGeometry.Canonical

open InfoGeometry.Algebra

/-- Möbius Трансформация върху Границата на Поанкаре Диска ∂ℍ² чрез ZornVectorMatrix ℤ -/
def zornMoebiusActionInt (A : ZornVectorMatrix ℤ) (z : ℚ) : ℚ :=
  if (A.w 0 * z + A.b) ≠ 0 then
    (A.a * z + A.v 0) / (A.w 0 * z + A.b)
  else
    0

/-- **Главна Теорема 1**: zorn_moebius_thermal_boost -
    Модуларната ос l (диагоналната Цорнова матрица L = diag(1, -1))
    индуцира хиперболичния Möbius тласък z ↦ -z на границата. -/
theorem zorn_moebius_thermal_boost_int (z : ℚ) (hz : z ≠ 0) :
    let A_l : ZornVectorMatrix ℤ := { a := 1, b := -1, v := fun _ => 0, w := fun _ => 0 }
    zornMoebiusActionInt A_l z = - z := by
  dsimp [zornMoebiusActionInt]
  have h_ne : (0 * z + -1 : ℚ) ≠ 0 := by norm_num
  rw [if_pos h_ne]
  ring

/-- **Главна Теорема 2**: zorn_determinant_multiplicative -
    Детерминантата (Нормата на Цорн) е строго мултипликативна върху спиновите сектори. -/
theorem zorn_determinant_multiplicative_int (a1 b1 a2 b2 : ℤ) :
    let A : ZornVectorMatrix ℤ := { a := a1, b := b1, v := fun _ => 0, w := fun _ => 0 }
    let B : ZornVectorMatrix ℤ := { a := a2, b := b2, v := fun _ => 0, w := fun _ => 0 }
    ZornVectorMatrix.norm (ZornVectorMatrix.mul A B) = ZornVectorMatrix.norm A * ZornVectorMatrix.norm B := by
  dsimp [ZornVectorMatrix.norm, ZornVectorMatrix.mul, ZornVec3.dot, ZornVec3.cross_smul_left, ZornVec3.cross_smul_right, Fin.sum_univ_three]
  simp [ZornVec3.cross, sub_zero, zero_add]
  ring

end InfoGeometry.Canonical
