import InfoGeometry.Canonical.ZornSpinor

namespace InfoGeometry.Canonical.ZornMatrix

variable {R : Type*} [CommRing R]

/- The canonical spinor owner predates a named conjugation API.  Keep the
   involution here, next to the multiplication operators which use it. -/
def conjugate (z : ZornMatrix R) : ZornMatrix R :=
  { a := z.b, b := z.a, x := -z.x, y := -z.y }

@[simp] theorem conjugate_add (z w : ZornMatrix R) :
    conjugate (z + w) = conjugate z + conjugate w := by
  cases z; cases w
  apply ZornMatrix.ext <;> simp [conjugate]

theorem conjugate_mul (z w : ZornMatrix R) :
    conjugate (z * w) = conjugate w * conjugate z := by
  cases z with
  | mk a b x y =>
    cases w with
    | mk c d p q =>
      apply ZornMatrix.ext
      · simp [conjugate, ZornMatrix.mul, ZornMatrix.dot]
        ring
      · simp [conjugate, ZornMatrix.mul, ZornMatrix.dot]
        ring
      · funext i
        fin_cases i <;>
          simp [conjugate, ZornMatrix.mul, ZornMatrix.dot, ZornMatrix.cross,
            Matrix.vecHead, Matrix.vecTail] <;> ring
      · funext i
        fin_cases i <;>
          simp [conjugate, ZornMatrix.mul, ZornMatrix.dot, ZornMatrix.cross,
            Matrix.vecHead, Matrix.vecTail] <;> ring

/-- Left multiplication by a fixed Zorn matrix, viewed as a linear map. -/
def leftMulLinear (z : ZornMatrix R) : ZornMatrix R →ₗ[R] ZornMatrix R where
  toFun w := z * w
  map_add' u v := by
    cases z with
    | mk a b x y =>
      cases u with
      | mk c d p q =>
        cases v with
        | mk e f r s =>
          apply ZornMatrix.ext
          · simp [ZornMatrix.mul, ZornMatrix.dot]
            ring
          · simp [ZornMatrix.mul, ZornMatrix.dot]
            ring
          · funext i
            fin_cases i <;>
              simp [ZornMatrix.mul, ZornMatrix.dot, ZornMatrix.cross,
                Matrix.vecHead, Matrix.vecTail] <;> ring
          · funext i
            fin_cases i <;>
              simp [ZornMatrix.mul, ZornMatrix.dot, ZornMatrix.cross,
                Matrix.vecHead, Matrix.vecTail] <;> ring
  map_smul' c w := by
    cases z with
    | mk a b x y =>
      cases w with
      | mk d e p q =>
        apply ZornMatrix.ext
        · simp [ZornMatrix.mul, ZornMatrix.dot]
          ring
        · simp [ZornMatrix.mul, ZornMatrix.dot]
          ring
        · funext i
          fin_cases i <;>
            simp [ZornMatrix.mul, ZornMatrix.dot, ZornMatrix.cross,
              Matrix.vecHead, Matrix.vecTail] <;> ring
        · funext i
          fin_cases i <;>
            simp [ZornMatrix.mul, ZornMatrix.dot, ZornMatrix.cross,
              Matrix.vecHead, Matrix.vecTail] <;> ring

@[simp] theorem leftMulLinear_apply (z w : ZornMatrix R) :
    leftMulLinear z w = z * w := rfl

/-- Right multiplication by a fixed Zorn matrix, viewed as a linear map. -/
def rightMulLinear (z : ZornMatrix R) : ZornMatrix R →ₗ[R] ZornMatrix R where
  toFun w := w * z
  map_add' u v := by
    cases z with
    | mk a b x y =>
      cases u with
      | mk c d p q =>
        cases v with
        | mk e f r s =>
          apply ZornMatrix.ext
          · simp [ZornMatrix.mul, ZornMatrix.dot]
            ring
          · simp [ZornMatrix.mul, ZornMatrix.dot]
            ring
          · funext i
            fin_cases i <;>
              simp [ZornMatrix.mul, ZornMatrix.dot, ZornMatrix.cross,
                Matrix.vecHead, Matrix.vecTail] <;> ring
          · funext i
            fin_cases i <;>
              simp [ZornMatrix.mul, ZornMatrix.dot, ZornMatrix.cross,
                Matrix.vecHead, Matrix.vecTail] <;> ring
  map_smul' c w := by
    cases z with
    | mk a b x y =>
      cases w with
      | mk d e p q =>
        apply ZornMatrix.ext
        · simp [ZornMatrix.mul, ZornMatrix.dot]
          ring
        · simp [ZornMatrix.mul, ZornMatrix.dot]
          ring
        · funext i
          fin_cases i <;>
            simp [ZornMatrix.mul, ZornMatrix.dot, ZornMatrix.cross,
              Matrix.vecHead, Matrix.vecTail] <;> ring
        · funext i
          fin_cases i <;>
            simp [ZornMatrix.mul, ZornMatrix.dot, ZornMatrix.cross,
              Matrix.vecHead, Matrix.vecTail] <;> ring

@[simp] theorem rightMulLinear_apply (z w : ZornMatrix R) :
    rightMulLinear z w = w * z := rfl

/-- Cayley conjugation as a linear map on the canonical Zorn carrier. -/
def conjugationLinear : ZornMatrix R →ₗ[R] ZornMatrix R where
  toFun := ZornMatrix.conjugate
  map_add' z w := ZornMatrix.conjugate_add z w
  map_smul' c z := by
    cases z with
    | mk a b x y =>
      apply ZornMatrix.ext
      · rfl
      · rfl
      · funext i
        change -(c * x i) = c * (-x i)
        ring
      · funext i
        change -(c * y i) = c * (-y i)
        ring

/-- Conjugation exchanges left multiplication with right multiplication. -/
theorem conjugationLinear_comp_leftMulLinear (z : ZornMatrix R) :
    conjugationLinear.comp (leftMulLinear z) =
      (rightMulLinear (ZornMatrix.conjugate z)).comp conjugationLinear := by
  apply LinearMap.ext
  intro w
  exact ZornMatrix.conjugate_mul z w

/-! The symmetric intertwining identity follows from the same
anti-multiplicativity, with the two factors exchanged. -/
theorem conjugationLinear_comp_rightMulLinear (z : ZornMatrix R) :
    conjugationLinear.comp (rightMulLinear z) =
      (leftMulLinear (ZornMatrix.conjugate z)).comp conjugationLinear := by
  apply LinearMap.ext
  intro w
  exact ZornMatrix.conjugate_mul w z

end InfoGeometry.Canonical.ZornMatrix
