import InfoGeometry.Exceptional.SplitOctonionZornReal
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Algebra.ZornVectorMatrix

namespace InfoGeometry.Exceptional.RealZorn

open InfoGeometry.Algebra

def vecToCanonical (u : Vec3Real) : ZornVec3 ℝ :=
  fun i => match i.1 with
  | 0 => u.1
  | 1 => u.2.1
  | _ => u.2.2

def vecFromCanonical (u : ZornVec3 ℝ) : Vec3Real :=
  (u 0, u 1, u 2)

theorem vecFromCanonical_to (u : Vec3Real) :
    vecFromCanonical (vecToCanonical u) = u := by
  rcases u with ⟨u₀, u₁, u₂⟩
  rfl

theorem vecToCanonical_from (u : ZornVec3 ℝ) :
    vecToCanonical (vecFromCanonical u) = u := by
  funext i
  fin_cases i <;> rfl

def toCanonical (X : ZornMatrixReal) : ZornVectorMatrix ℝ :=
  { a := X.a
    v := vecToCanonical X.u
    w := vecToCanonical X.v
    b := X.b }

/-! Factor-level coordinate readbacks used by the finite Jordan transport.
The canonical carrier stores the first vector factor as `v 1`; this is the
native counterpart of the source-side `u.2.1` coordinate. -/

@[simp] theorem toCanonical_x1 (X : ZornMatrixReal) :
    (toCanonical X).v 1 = X.u.2.1 := by
  rfl

@[simp] theorem toCanonical_x2 (X : ZornMatrixReal) :
    (toCanonical X).v 2 = X.u.2.2 := by
  rfl

@[simp] theorem toCanonical_y2 (X : ZornMatrixReal) :
    (toCanonical X).w 2 = X.v.2.2 := by
  rfl

def fromCanonical (X : ZornVectorMatrix ℝ) : ZornMatrixReal :=
  { a := X.a
    b := X.b
    u := vecFromCanonical X.v
    v := vecFromCanonical X.w }

def canonicalEquiv : ZornMatrixReal ≃ ZornVectorMatrix ℝ where
  toFun := toCanonical
  invFun := fromCanonical
  left_inv := by
    intro X
    cases X
    simp [toCanonical, fromCanonical, vecFromCanonical_to]
  right_inv := by
    intro X
    apply ZornVectorMatrix.ext
    · rfl
    · exact vecToCanonical_from X.v
    · exact vecToCanonical_from X.w
    · rfl

@[simp] theorem canonicalEquiv_apply (X : ZornMatrixReal) :
    canonicalEquiv X = toCanonical X := rfl

@[simp] theorem canonicalEquiv_symm_apply (X : ZornVectorMatrix ℝ) :
    canonicalEquiv.symm X = fromCanonical X := rfl

theorem toCanonical_add (X Y : ZornMatrixReal) :
    toCanonical (X + Y) =
      InfoGeometry.Algebra.ZornVectorMatrix.add (toCanonical X) (toCanonical Y) := by
  apply ZornVectorMatrix.ext
  · rfl
  · funext i
    fin_cases i <;> rfl
  · funext i
    fin_cases i <;> rfl
  · rfl

theorem canonicalEquiv_add (X Y : ZornMatrixReal) :
    canonicalEquiv (X + Y) =
      ZornVectorMatrix.add (canonicalEquiv X) (canonicalEquiv Y) := by
  exact toCanonical_add X Y

theorem canonicalEquiv_symm_add (X Y : ZornVectorMatrix ℝ) :
    canonicalEquiv.symm (ZornVectorMatrix.add X Y) =
      canonicalEquiv.symm X + canonicalEquiv.symm Y := by
  apply canonicalEquiv.injective
  simp only [canonicalEquiv_add, Equiv.apply_symm_apply]

theorem canonicalEquiv_neg (X : ZornMatrixReal) :
    canonicalEquiv (ZornMatrixReal.neg X) =
      ZornVectorMatrix.neg (canonicalEquiv X) := by
  apply ZornVectorMatrix.ext
  · rfl
  · funext i
    fin_cases i <;>
      simp [canonicalEquiv, toCanonical, vecToCanonical,
        ZornMatrixReal.neg, ZornVectorMatrix.neg, smul]
  · funext i
    fin_cases i <;>
      simp [canonicalEquiv, toCanonical, vecToCanonical,
        ZornMatrixReal.neg, ZornVectorMatrix.neg, smul]
  · rfl

theorem canonicalEquiv_symm_neg (X : ZornVectorMatrix ℝ) :
    canonicalEquiv.symm (ZornVectorMatrix.neg X) =
      ZornMatrixReal.neg (canonicalEquiv.symm X) := by
  apply canonicalEquiv.injective
  simp only [canonicalEquiv_neg, Equiv.apply_symm_apply]

theorem canonicalEquiv_mul (X Y : ZornMatrixReal) :
    canonicalEquiv (X * Y) =
      ZornVectorMatrix.mul (canonicalEquiv X) (canonicalEquiv Y) := by
  apply ZornVectorMatrix.ext
  · simp [canonicalEquiv, toCanonical, vecToCanonical,
      ZornVectorMatrix.mul, dot, cross, ZornVec3.dot, ZornVec3.cross,
      Fin.sum_univ_three]
  · funext i
    fin_cases i <;>
      simp [canonicalEquiv, toCanonical, vecToCanonical,
        ZornVectorMatrix.mul, add, sub, smul, dot, cross,
        ZornVec3.dot, ZornVec3.cross, Fin.sum_univ_three]
  · funext i
    fin_cases i <;>
      simp [canonicalEquiv, toCanonical, vecToCanonical,
        ZornVectorMatrix.mul, add, sub, smul, dot, cross,
        ZornVec3.dot, ZornVec3.cross, Fin.sum_univ_three]
  · simp [canonicalEquiv, toCanonical, vecToCanonical,
      ZornVectorMatrix.mul, dot, cross, ZornVec3.dot, ZornVec3.cross,
      Fin.sum_univ_three]
    ring

theorem canonicalEquiv_symm_mul (X Y : ZornVectorMatrix ℝ) :
    canonicalEquiv.symm (ZornVectorMatrix.mul X Y) =
      canonicalEquiv.symm X * canonicalEquiv.symm Y := by
  apply canonicalEquiv.injective
  simp only [canonicalEquiv_mul, Equiv.apply_symm_apply]

def realConj (X : ZornMatrixReal) : ZornMatrixReal :=
  { a := X.b
    b := X.a
    u := smul (-1) X.u
    v := smul (-1) X.v }

theorem canonicalEquiv_conj (X : ZornMatrixReal) :
    canonicalEquiv (realConj X) =
      ZornVectorMatrix.conj (canonicalEquiv X) := by
  apply ZornVectorMatrix.ext
  · rfl
  · funext i
    fin_cases i <;> simp [canonicalEquiv, toCanonical, vecToCanonical,
      realConj, smul, ZornVectorMatrix.conj]
  · funext i
    fin_cases i <;> simp [canonicalEquiv, toCanonical, vecToCanonical,
      realConj, smul, ZornVectorMatrix.conj]
  · rfl

theorem canonicalEquiv_symm_conj (X : ZornVectorMatrix ℝ) :
    canonicalEquiv.symm (ZornVectorMatrix.conj X) =
      realConj (canonicalEquiv.symm X) := by
  apply canonicalEquiv.injective
  simp only [canonicalEquiv_conj, Equiv.apply_symm_apply]

end InfoGeometry.Exceptional.RealZorn
