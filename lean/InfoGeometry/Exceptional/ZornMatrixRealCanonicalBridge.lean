import InfoGeometry.Exceptional.SplitOctonionZornReal
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

theorem canonicalEquiv_mul (X Y : ZornMatrixReal) :
    canonicalEquiv (X * Y) =
      ZornVectorMatrix.mul (canonicalEquiv X) (canonicalEquiv Y) := by
  apply ZornVectorMatrix.ext
  · simp [canonicalEquiv, toCanonical, vecToCanonical, ZornMatrixReal.mul,
      ZornVectorMatrix.mul, dot, cross, ZornVec3.dot, ZornVec3.cross,
      Fin.sum_univ_three]
  · funext i
    fin_cases i <;>
      simp [canonicalEquiv, toCanonical, vecToCanonical, ZornMatrixReal.mul,
        ZornVectorMatrix.mul, add, sub, smul, dot, cross,
        ZornVec3.dot, ZornVec3.cross, Fin.sum_univ_three] <;> ring
  · funext i
    fin_cases i <;>
      simp [canonicalEquiv, toCanonical, vecToCanonical, ZornMatrixReal.mul,
        ZornVectorMatrix.mul, add, sub, smul, dot, cross,
        ZornVec3.dot, ZornVec3.cross, Fin.sum_univ_three] <;> ring
  · simp [canonicalEquiv, toCanonical, vecToCanonical, ZornMatrixReal.mul,
      ZornVectorMatrix.mul, dot, cross, ZornVec3.dot, ZornVec3.cross,
      Fin.sum_univ_three] <;> ring

end InfoGeometry.Exceptional.RealZorn
