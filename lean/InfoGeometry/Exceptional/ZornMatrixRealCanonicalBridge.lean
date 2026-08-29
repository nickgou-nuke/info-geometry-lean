import InfoGeometry.Exceptional.SplitOctonionZornReal
import InfoGeometry.Algebra.ZornVectorMatrix
import InfoGeometry.Algebra.RealSplitOctZornAlignment

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

@[simp] theorem canonicalEquiv_fromCanonical (X : ZornVectorMatrix ℝ) :
    canonicalEquiv (fromCanonical X) = X := by
  exact canonicalEquiv.apply_symm_apply X

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

theorem fromCanonical_add (X Y : ZornVectorMatrix ℝ) :
    fromCanonical (ZornVectorMatrix.add X Y) =
      fromCanonical X + fromCanonical Y := by
  apply canonicalEquiv.injective
  change canonicalEquiv (canonicalEquiv.symm (ZornVectorMatrix.add X Y)) =
    canonicalEquiv (fromCanonical X + fromCanonical Y)
  rw [canonicalEquiv.apply_symm_apply, canonicalEquiv_add]
  simp [canonicalEquiv, toCanonical, fromCanonical, vecToCanonical_from]

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

theorem canonicalEquiv_zornHalf (X : ZornMatrixReal) :
    canonicalEquiv (zornHalf X) =
      ZornVectorMatrix.smul (2 : ℝ)⁻¹ (canonicalEquiv X) := by
  apply ZornVectorMatrix.ext
  · simp [canonicalEquiv, toCanonical, vecToCanonical, zornHalf,
      ZornVectorMatrix.smul]
    ring
  · funext i
    fin_cases i <;>
      simp [canonicalEquiv, toCanonical, vecToCanonical, zornHalf,
        smul, ZornVectorMatrix.smul]
  · funext i
    fin_cases i <;>
      simp [canonicalEquiv, toCanonical, vecToCanonical, zornHalf,
        smul, ZornVectorMatrix.smul]
  · simp [canonicalEquiv, toCanonical, vecToCanonical, zornHalf,
      ZornVectorMatrix.smul]
    ring

def toRealSplitOct (X : ZornMatrixReal) : RealSplitOct :=
  RealSplitOctZornAlignment.fromZorn (canonicalEquiv X)

@[simp] theorem toRealSplitOct_a (X : ZornMatrixReal) :
    (toRealSplitOct X).a = X.a := rfl

@[simp] theorem toRealSplitOct_b (X : ZornMatrixReal) :
    (toRealSplitOct X).b = X.b := rfl

@[simp] theorem toRealSplitOct_x0 (X : ZornMatrixReal) :
    (toRealSplitOct X).x0 = X.u.1 := rfl

@[simp] theorem toRealSplitOct_x1 (X : ZornMatrixReal) :
    (toRealSplitOct X).x1 = X.u.2.1 := rfl

@[simp] theorem toRealSplitOct_x2 (X : ZornMatrixReal) :
    (toRealSplitOct X).x2 = X.u.2.2 := rfl

@[simp] theorem toRealSplitOct_y0 (X : ZornMatrixReal) :
    (toRealSplitOct X).y0 = X.v.1 := rfl

@[simp] theorem toRealSplitOct_y1 (X : ZornMatrixReal) :
    (toRealSplitOct X).y1 = X.v.2.1 := rfl

@[simp] theorem toRealSplitOct_y2 (X : ZornMatrixReal) :
    (toRealSplitOct X).y2 = X.v.2.2 := rfl

theorem toRealSplitOct_add (X Y : ZornMatrixReal) :
    toRealSplitOct (X + Y) =
      RealSplitOct.add (toRealSplitOct X) (toRealSplitOct Y) := by
  change RealSplitOctZornAlignment.fromZorn
      (ZornVectorMatrix.add (canonicalEquiv X) (canonicalEquiv Y)) =
    RealSplitOctZornAlignment.fromZorn (canonicalEquiv X) +
      RealSplitOctZornAlignment.fromZorn (canonicalEquiv Y)
  exact RealSplitOctZornAlignment.fromZorn_add _ _

theorem toRealSplitOct_smul (r : ℝ) (X : ZornVectorMatrix ℝ) :
    RealSplitOctZornAlignment.fromZorn (ZornVectorMatrix.smul r X) =
      RealSplitOct.smul r (RealSplitOctZornAlignment.fromZorn X) := by
  exact RealSplitOctZornAlignment.fromZorn_smul r X

theorem toRealSplitOct_mul (X Y : ZornMatrixReal) :
    toRealSplitOct (X * Y) =
      RealSplitOct.mul (toRealSplitOct X) (toRealSplitOct Y) := by
  apply RealSplitOctZornAlignment.equiv.injective
  simp only [toRealSplitOct, RealSplitOctZornAlignment.equiv_apply,
    RealSplitOctZornAlignment.toZorn_fromZorn]
  rw [RealSplitOctZornAlignment.toZorn_mul]
  simp only [RealSplitOctZornAlignment.toZorn_fromZorn]
  exact canonicalEquiv_mul X Y

theorem toRealSplitOct_conj (X : ZornMatrixReal) :
    toRealSplitOct (realConj X) =
      RealSplitOct.conj (toRealSplitOct X) := by
  apply RealSplitOctZornAlignment.equiv.injective
  simp only [toRealSplitOct, RealSplitOctZornAlignment.equiv_apply,
    RealSplitOctZornAlignment.toZorn_fromZorn]
  rw [RealSplitOctZornAlignment.toZorn_conj]
  simp only [RealSplitOctZornAlignment.toZorn_fromZorn]
  exact canonicalEquiv_conj X

theorem fromCanonical_mul_a (X Y : ZornMatrixReal) :
    ((RealSplitOctZornAlignment.fromZorn (canonicalEquiv X)).mul
        (RealSplitOctZornAlignment.fromZorn (canonicalEquiv Y))).a =
      (X * Y).a := by
  simpa only [toRealSplitOct] using congrArg RealSplitOct.a
    (toRealSplitOct_mul X Y).symm

theorem fromCanonical_conj_a (X : ZornMatrixReal) :
    (RealSplitOctZornAlignment.fromZorn (canonicalEquiv X)).conj.a =
      (realConj X).a := by
  simpa only [toRealSplitOct] using congrArg RealSplitOct.a
    (toRealSplitOct_conj X).symm

theorem fromCanonical_mul (X Y : ZornMatrixReal) :
    RealSplitOct.mul (RealSplitOctZornAlignment.fromZorn (canonicalEquiv X))
        (RealSplitOctZornAlignment.fromZorn (canonicalEquiv Y)) =
      RealSplitOctZornAlignment.fromZorn (canonicalEquiv (X * Y)) := by
  simpa only [toRealSplitOct] using (toRealSplitOct_mul X Y).symm

theorem fromCanonical_conj (X : ZornMatrixReal) :
    RealSplitOct.conj (RealSplitOctZornAlignment.fromZorn (canonicalEquiv X)) =
      RealSplitOctZornAlignment.fromZorn (canonicalEquiv (realConj X)) := by
  simpa only [toRealSplitOct] using (toRealSplitOct_conj X).symm

theorem fromCanonical_mul_conj_right (X Y : ZornMatrixReal) :
    RealSplitOct.mul (RealSplitOctZornAlignment.fromZorn (canonicalEquiv X))
        (RealSplitOct.conj
          (RealSplitOctZornAlignment.fromZorn (canonicalEquiv Y))) =
      RealSplitOctZornAlignment.fromZorn (canonicalEquiv (X * realConj Y)) := by
  rw [fromCanonical_conj Y, fromCanonical_mul]

theorem fromCanonical_mul_conj_right_a (X Y : ZornMatrixReal) :
    (RealSplitOct.mul (RealSplitOctZornAlignment.fromZorn (canonicalEquiv X))
        (RealSplitOct.conj
          (RealSplitOctZornAlignment.fromZorn (canonicalEquiv Y)))).a =
      (X * realConj Y).a := by
  exact congrArg RealSplitOct.a (fromCanonical_mul_conj_right X Y)

theorem fromCanonical_conj_mul_left (X Y : ZornMatrixReal) :
    RealSplitOct.mul
        (RealSplitOct.conj
          (RealSplitOctZornAlignment.fromZorn (canonicalEquiv X)))
        (RealSplitOctZornAlignment.fromZorn (canonicalEquiv Y)) =
      RealSplitOctZornAlignment.fromZorn (canonicalEquiv (realConj X * Y)) := by
  rw [fromCanonical_conj X, fromCanonical_mul]

theorem fromCanonical_conj_mul_left_a (X Y : ZornMatrixReal) :
    (RealSplitOct.mul
        (RealSplitOct.conj
          (RealSplitOctZornAlignment.fromZorn (canonicalEquiv X)))
        (RealSplitOctZornAlignment.fromZorn (canonicalEquiv Y))).a =
      (realConj X * Y).a := by
  exact congrArg RealSplitOct.a (fromCanonical_conj_mul_left X Y)

@[simp] theorem fromCanonical_a (X : ZornMatrixReal) :
    (RealSplitOctZornAlignment.fromZorn (toCanonical X)).a = X.a := rfl

@[simp] theorem fromCanonical_b (X : ZornMatrixReal) :
    (RealSplitOctZornAlignment.fromZorn (toCanonical X)).b = X.b := rfl

end InfoGeometry.Exceptional.RealZorn
