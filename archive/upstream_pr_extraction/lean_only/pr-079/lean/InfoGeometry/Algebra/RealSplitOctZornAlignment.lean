import InfoGeometry.Algebra.RealSplitAlbert
import InfoGeometry.Algebra.ZornVectorMatrix

namespace InfoGeometry.Algebra.RealSplitOctZornAlignment

open InfoGeometry.Algebra

/-! Coordinate alignment between the two existing real split-octonion
carriers.  This is an actual equivalence of the maintained carriers, not a
new octonion model. -/

def toZorn (X : RealSplitOct) : ZornVectorMatrix ℝ :=
  { a := X.a
    v := ![X.x0, X.x1, X.x2]
    w := ![X.y0, X.y1, X.y2]
    b := X.b }

def fromZorn (X : ZornVectorMatrix ℝ) : RealSplitOct :=
  { a := X.a
    b := X.b
    x0 := X.v 0
    x1 := X.v 1
    x2 := X.v 2
    y0 := X.w 0
    y1 := X.w 1
    y2 := X.w 2 }

def equiv : RealSplitOct ≃ ZornVectorMatrix ℝ where
  toFun := toZorn
  invFun := fromZorn
  left_inv := by
    intro X
    cases X
    rfl
  right_inv := by
    intro X
    apply ZornVectorMatrix.ext
    · rfl
    · funext i
      fin_cases i <;> rfl
    · funext i
      fin_cases i <;> rfl
    · rfl

@[simp] theorem equiv_apply (X : RealSplitOct) : equiv X = toZorn X := rfl

@[simp] theorem equiv_symm_apply (X : ZornVectorMatrix ℝ) :
    equiv.symm X = fromZorn X := rfl

theorem fromZorn_toZorn (X : RealSplitOct) : fromZorn (toZorn X) = X := by
  cases X
  rfl

theorem toZorn_fromZorn (X : ZornVectorMatrix ℝ) : toZorn (fromZorn X) = X := by
  apply ZornVectorMatrix.ext
  · rfl
  · funext i
    fin_cases i <;> rfl
  · funext i
    fin_cases i <;> rfl
  · rfl

theorem toZorn_add (X Y : RealSplitOct) :
    toZorn (X + Y) = toZorn X + toZorn Y := by
  cases X; cases Y
  apply ZornVectorMatrix.ext
  · rfl
  · funext i
    fin_cases i <;> rfl
  · funext i
    fin_cases i <;> rfl
  · rfl

theorem toZorn_add_def (X Y : RealSplitOct) :
    toZorn (RealSplitOct.add X Y) = ZornVectorMatrix.add (toZorn X) (toZorn Y) := by
  cases X; cases Y
  apply ZornVectorMatrix.ext
  · rfl
  · funext i
    fin_cases i <;> rfl
  · funext i
    fin_cases i <;> rfl
  · rfl

theorem toZorn_smul (r : ℝ) (X : RealSplitOct) :
    toZorn (r • X) = r • toZorn X := by
  cases X
  apply ZornVectorMatrix.ext
  · rfl

  · funext i
    fin_cases i <;> rfl
  · funext i
    fin_cases i <;> rfl
  · rfl

theorem toZorn_smul_def (r : ℝ) (X : RealSplitOct) :
    toZorn (RealSplitOct.smul r X) = ZornVectorMatrix.smul r (toZorn X) := by
  cases X
  apply ZornVectorMatrix.ext
  · rfl
  · funext i
    fin_cases i <;> rfl
  · funext i
    fin_cases i <;> rfl
  · rfl

theorem toZorn_mul (X Y : RealSplitOct) :
    toZorn (RealSplitOct.mul X Y) = ZornVectorMatrix.mul (toZorn X) (toZorn Y) := by
  apply ZornVectorMatrix.ext
  · simp [toZorn, RealSplitOct.mul, ZornVectorMatrix.mul, ZornVec3.dot,
      ZornVec3.cross, Fin.sum_univ_succ]
    ring
  · funext i
    fin_cases i <;>
      simp [toZorn, RealSplitOct.mul, ZornVectorMatrix.mul, ZornVec3.dot,
        ZornVec3.cross, Fin.sum_univ_succ]
  · funext i
    fin_cases i <;>
      simp [toZorn, RealSplitOct.mul, ZornVectorMatrix.mul, ZornVec3.dot,
        ZornVec3.cross, Fin.sum_univ_succ]
  · simp [toZorn, RealSplitOct.mul, ZornVectorMatrix.mul, ZornVec3.dot,
      ZornVec3.cross, Fin.sum_univ_succ]
    ring

theorem toZorn_conj (X : RealSplitOct) :
    toZorn X.conj = ZornVectorMatrix.conj (toZorn X) := by
  apply ZornVectorMatrix.ext
  · rfl
  · funext i
    fin_cases i <;> rfl
  · funext i
    fin_cases i <;> rfl
  · rfl

theorem toZorn_conj_def (X : RealSplitOct) :
    toZorn (RealSplitOct.conj X) = ZornVectorMatrix.conj (toZorn X) := by
  apply ZornVectorMatrix.ext
  · rfl
  · funext i
    fin_cases i <;> rfl
  · funext i
    fin_cases i <;> rfl
  · rfl

theorem toZorn_norm (X : RealSplitOct) :
    ZornVectorMatrix.norm (toZorn X) = X.a * X.b -
      (X.x0 * X.y0 + X.x1 * X.y1 + X.x2 * X.y2) := by
  simp [toZorn, ZornVectorMatrix.norm, ZornVec3.dot, Fin.sum_univ_succ]
  ring

end InfoGeometry.Algebra.RealSplitOctZornAlignment
