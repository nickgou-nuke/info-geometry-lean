import Mathlib
import InfoGeometry.Canonical.ThreeColorIntegralCliffordEmbedding
import InfoGeometry.Algebra.ZornVectorMatrix

namespace InfoGeometry.Canonical

open InfoGeometry.Algebra

abbrev StandardRationalSplitOctonion := IntegralSplitBasis → ℚ

def rationalBasis (b : IntegralSplitBasis) : StandardRationalSplitOctonion :=
  Pi.single b 1

def rationalizeIntegral (x : StandardIntegralSplitOctonion) :
    StandardRationalSplitOctonion := fun b => x b

def toZorn (x : StandardRationalSplitOctonion) : ZornVectorMatrix ℚ :=
  { a := x .one + x .l
    v := ![x .i - x .il, -x .j + x .jl, x .k - x .kl]
    w := ![-x .i - x .il, x .j + x .jl, -x .k - x .kl]
    b := x .one - x .l }

def fromZorn (Z : ZornVectorMatrix ℚ) : StandardRationalSplitOctonion
  | .one => (Z.a + Z.b) / 2
  | .l => (Z.a - Z.b) / 2
  | .i => (Z.v 0 - Z.w 0) / 2
  | .il => -(Z.v 0 + Z.w 0) / 2
  | .j => (Z.w 1 - Z.v 1) / 2
  | .jl => (Z.v 1 + Z.w 1) / 2
  | .k => (Z.v 2 - Z.w 2) / 2
  | .kl => -(Z.v 2 + Z.w 2) / 2

theorem fromZorn_toZorn (x : StandardRationalSplitOctonion) :
    fromZorn (toZorn x) = x := by
  funext b
  fin_cases b <;> simp [fromZorn, toZorn] <;> ring

theorem toZorn_fromZorn (Z : ZornVectorMatrix ℚ) :
    toZorn (fromZorn Z) = Z := by
  apply ZornVectorMatrix.ext
  · simp [fromZorn, toZorn]
    ring
  · funext i
    fin_cases i <;> simp [fromZorn, toZorn] <;> ring
  · funext i
    fin_cases i <;> simp [fromZorn, toZorn] <;> ring
  · simp [fromZorn, toZorn]
    ring

def toZornLinear :
    StandardRationalSplitOctonion →ₗ[ℚ] ZornVectorMatrix ℚ where
  toFun := toZorn
  map_add' x y := by
    apply ZornVectorMatrix.ext
    · change (x .one + y .one) + (x .l + y .l) =
        (x .one + x .l) + (y .one + y .l)
      ring
    · funext i
      fin_cases i
      · change ((x .i + y .i) - (x .il + y .il)) =
          (x .i - x .il) + (y .i - y .il)
        ring
      · change (-(x .j + y .j) + (x .jl + y .jl)) =
          (-x .j + x .jl) + (-y .j + y .jl)
        ring
      · change ((x .k + y .k) - (x .kl + y .kl)) =
          (x .k - x .kl) + (y .k - y .kl)
        ring
    · funext i
      fin_cases i
      · change (-(x .i + y .i) - (x .il + y .il)) =
          (-x .i - x .il) + (-y .i - y .il)
        ring
      · change ((x .j + y .j) + (x .jl + y .jl)) =
          (x .j + x .jl) + (y .j + y .jl)
        ring
      · change (-(x .k + y .k) - (x .kl + y .kl)) =
          (-x .k - x .kl) + (-y .k - y .kl)
        ring
    · change (x .one + y .one) - (x .l + y .l) =
        (x .one - x .l) + (y .one - y .l)
      ring
  map_smul' r x := by
    simp only [RingHom.id_apply]
    have hsmul : r • toZorn x = ZornVectorMatrix.smul r (toZorn x) := by
      apply ZornVectorMatrix.ext
      · rfl
      · funext i; rfl
      · funext i; rfl
      · rfl
    rw [hsmul]
    apply ZornVectorMatrix.ext
    · dsimp [ZornVectorMatrix.smul, toZorn]
      ring
    · funext i
      fin_cases i <;> dsimp [ZornVectorMatrix.smul, toZorn] <;> ring
    · funext i
      fin_cases i <;> dsimp [ZornVectorMatrix.smul, toZorn] <;> ring
    · dsimp [ZornVectorMatrix.smul, toZorn]
      ring

def fromZornLinear :
    ZornVectorMatrix ℚ →ₗ[ℚ] StandardRationalSplitOctonion where
  toFun := fromZorn
  map_add' X Y := by
    change fromZorn (ZornVectorMatrix.add X Y) = fromZorn X + fromZorn Y
    funext b
    cases b <;> simp [fromZorn, ZornVectorMatrix.add] <;> ring
  map_smul' r X := by
    simp only [RingHom.id_apply]
    change fromZorn (ZornVectorMatrix.smul r X) = r • fromZorn X
    funext b
    cases b <;> simp [fromZorn, ZornVectorMatrix.smul] <;> ring

noncomputable def zornVectorMatrixRationalEquiv :
    StandardRationalSplitOctonion ≃ₗ[ℚ] ZornVectorMatrix ℚ :=
  let hleft : Function.LeftInverse fromZornLinear toZornLinear := by
    intro x
    funext b
    change fromZorn (toZorn x) b = x b
    exact congrFun (fromZorn_toZorn x) b
  let hright : Function.RightInverse fromZornLinear toZornLinear := by
    intro Z
    exact toZorn_fromZorn Z
  LinearEquiv.ofBijective toZornLinear ⟨hleft.injective, hright.surjective⟩

@[simp] theorem rationalEquiv_one :
    zornVectorMatrixRationalEquiv (rationalBasis .one) =
      ({ a := 1, v := 0, w := 0, b := 1 } : ZornVectorMatrix ℚ) := by
  change toZorn (rationalBasis .one) = _
  apply ZornVectorMatrix.ext <;>
    simp [toZorn, rationalBasis]

@[simp] theorem rationalEquiv_l :
    zornVectorMatrixRationalEquiv (rationalBasis .l) =
      ({ a := 1, v := 0, w := 0, b := -1 } : ZornVectorMatrix ℚ) := by
  change toZorn (rationalBasis .l) = _
  apply ZornVectorMatrix.ext <;> simp [toZorn, rationalBasis]

@[simp] theorem rationalEquiv_i :
    zornVectorMatrixRationalEquiv (rationalBasis .i) =
      ({ a := 0, v := ![1, 0, 0], w := ![-1, 0, 0], b := 0 } : ZornVectorMatrix ℚ) := by
  change toZorn (rationalBasis .i) = _
  apply ZornVectorMatrix.ext <;> simp [toZorn, rationalBasis]

@[simp] theorem rationalEquiv_il :
    zornVectorMatrixRationalEquiv (rationalBasis .il) =
      ({ a := 0, v := ![-1, 0, 0], w := ![-1, 0, 0], b := 0 } : ZornVectorMatrix ℚ) := by
  change toZorn (rationalBasis .il) = _
  apply ZornVectorMatrix.ext <;> simp [toZorn, rationalBasis]

@[simp] theorem rationalEquiv_j :
    zornVectorMatrixRationalEquiv (rationalBasis .j) =
      ({ a := 0, v := ![0, -1, 0], w := ![0, 1, 0], b := 0 } : ZornVectorMatrix ℚ) := by
  change toZorn (rationalBasis .j) = _
  apply ZornVectorMatrix.ext <;> simp [toZorn, rationalBasis]

@[simp] theorem rationalEquiv_jl :
    zornVectorMatrixRationalEquiv (rationalBasis .jl) =
      ({ a := 0, v := ![0, 1, 0], w := ![0, 1, 0], b := 0 } : ZornVectorMatrix ℚ) := by
  change toZorn (rationalBasis .jl) = _
  apply ZornVectorMatrix.ext <;> simp [toZorn, rationalBasis]

@[simp] theorem rationalEquiv_k :
    zornVectorMatrixRationalEquiv (rationalBasis .k) =
      ({ a := 0, v := ![0, 0, 1], w := ![0, 0, -1], b := 0 } : ZornVectorMatrix ℚ) := by
  change toZorn (rationalBasis .k) = _
  apply ZornVectorMatrix.ext <;> simp [toZorn, rationalBasis]

@[simp] theorem rationalEquiv_kl :
    zornVectorMatrixRationalEquiv (rationalBasis .kl) =
      ({ a := 0, v := ![0, 0, -1], w := ![0, 0, -1], b := 0 } : ZornVectorMatrix ℚ) := by
  change toZorn (rationalBasis .kl) = _
  apply ZornVectorMatrix.ext <;> simp [toZorn, rationalBasis]

def coordinateSplitNorm (x : StandardRationalSplitOctonion) : ℚ :=
  x .one ^ 2 - x .l ^ 2 + x .i ^ 2 - x .il ^ 2 +
    x .j ^ 2 - x .jl ^ 2 + x .k ^ 2 - x .kl ^ 2

def coordinateConj (x : StandardRationalSplitOctonion) : StandardRationalSplitOctonion
  | .one => x .one
  | .l => -x .l
  | .i => -x .i
  | .il => -x .il
  | .j => -x .j
  | .jl => -x .jl
  | .k => -x .k
  | .kl => -x .kl

theorem zornVectorMatrixRationalEquiv_preserves_norm
    (x : StandardRationalSplitOctonion) :
    ZornVectorMatrix.norm (zornVectorMatrixRationalEquiv x) =
      coordinateSplitNorm x := by
  change ZornVectorMatrix.norm (toZorn x) = _
  simp [ZornVectorMatrix.norm, ZornVec3.dot, Fin.sum_univ_three,
    toZorn, coordinateSplitNorm]
  ring

theorem zornVectorMatrixRationalEquiv_map_conj
    (x : StandardRationalSplitOctonion) :
    zornVectorMatrixRationalEquiv (coordinateConj x) =
      ZornVectorMatrix.conj (zornVectorMatrixRationalEquiv x) := by
  change toZorn (coordinateConj x) = ZornVectorMatrix.conj (toZorn x)
  apply ZornVectorMatrix.ext
  · simp [coordinateConj, ZornVectorMatrix.conj, toZorn, sub_eq_add_neg]
  · funext i
    fin_cases i <;> simp [coordinateConj, ZornVectorMatrix.conj, toZorn] <;> ring
  · funext i
    fin_cases i <;> simp [coordinateConj, ZornVectorMatrix.conj, toZorn] <;> ring
  · simp [coordinateConj, ZornVectorMatrix.conj, toZorn] <;> ring

end InfoGeometry.Canonical
