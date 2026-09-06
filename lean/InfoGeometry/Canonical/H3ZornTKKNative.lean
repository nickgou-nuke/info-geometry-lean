import Mathlib
import InfoGeometry.Canonical.H3ZornJordanTripleBridge

noncomputable section

namespace InfoGeometry.Canonical.H3ZornTKKNative

open InfoGeometry.Algebra
open InfoGeometry.Algebra.H3Zorn
open InfoGeometry.Canonical.H3ZornJordanTripleBridge

abbrev H3 := H3Zorn ℝ

def kantorOperator (x y : H3) : Module.End ℝ H3 where
  toFun z := jordanTriple x z y - jordanTriple y z x
  map_add' z₁ z₂ := by simp [jordanTriple_add_middle]; abel
  map_smul' r z := by simp [jordanTriple_smul_middle, smul_sub]

theorem kantorOperator_apply (x y z : H3) :
    kantorOperator x y z = jordanTriple x z y - jordanTriple y z x := rfl

theorem kantorOperator_zero (x y : H3) : kantorOperator x y = 0 := by
  apply LinearMap.ext
  intro z
  rw [kantorOperator_apply, jordanTriple_K_expression_zero]
  simp

theorem innerDerivation_triple (x y u v w : H3) :
    innerDerivation x y (jordanTriple u v w) =
      jordanTriple (innerDerivation x y u) v w +
        jordanTriple u (innerDerivation x y v) w +
          jordanTriple u v (innerDerivation x y w) := by
  apply jordanTriple_derivation
  exact InfoGeometry.Algebra.h3ZornJordanInnerDerivation_mem_F4 x y

/-! The same derivation law in the native endomorphism Lie algebra. -/
theorem innerDerivation_lie_jordanTripleD (x y u v : H3) :
    ⁅innerDerivation x y, jordanTripleD u v⁆ =
      jordanTripleD (innerDerivation x y u) v +
        jordanTripleD u (innerDerivation x y v) := by
  apply LinearMap.ext
  intro w
  change innerDerivation x y (jordanTriple u v w) -
      jordanTriple u v (innerDerivation x y w) = _
  rw [innerDerivation_triple]
  simp only [jordanTripleD_apply, LinearMap.add_apply]
  abel

theorem innerDerivation_is_jordan_derivation (x y : H3) :
    H3ZornJordanDerivation (innerDerivation x y) := by
  exact InfoGeometry.Algebra.h3ZornJordanInnerDerivation_mem_F4 x y

theorem jordanTriple_eq_mul_add_inner (x y z : H3) :
    jordanTriple x y z = (x * y) * z + innerDerivation x y z := by
  simp only [jordanTriple, innerDerivation_apply]
  simp [mul_comm]
  abel

theorem jordanTripleD_eq_left_add_inner (x y : H3) :
    jordanTripleD x y = jordanLmul (R := ℝ) (x * y) + innerDerivation x y := by
  apply LinearMap.ext
  intro z
  simp only [jordanTripleD_apply, jordanTriple, jordanLmul_apply,
    LinearMap.add_apply, innerDerivation_apply]
  simp [mul_comm]
  abel

structure TKKCarrier where
  neg : H3
  zeroOp : Module.End ℝ H3
  zeroAdj : Module.End ℝ H3
  pos : H3

@[ext] theorem TKKCarrier.ext (X Y : TKKCarrier)
    (hneg : X.neg = Y.neg) (hop : X.zeroOp = Y.zeroOp)
    (hadj : X.zeroAdj = Y.zeroAdj) (hpos : X.pos = Y.pos) : X = Y := by
  cases X; cases Y
  simp only at hneg hop hadj hpos
  rw [hneg, hop, hadj, hpos]

def tkkNeg (X : TKKCarrier) : TKKCarrier where
  neg := -X.neg
  zeroOp := -X.zeroOp
  zeroAdj := -X.zeroAdj
  pos := -X.pos

def tkkBracket (X Y : TKKCarrier) : TKKCarrier where
  neg := X.zeroOp Y.neg - Y.zeroOp X.neg
  zeroOp := (X.zeroOp.comp Y.zeroOp - Y.zeroOp.comp X.zeroOp) +
    (jordanTripleD X.neg Y.pos - jordanTripleD Y.neg X.pos)
  zeroAdj := (Y.zeroAdj.comp X.zeroAdj - X.zeroAdj.comp Y.zeroAdj) +
    (jordanTripleD Y.pos X.neg - jordanTripleD X.pos Y.neg)
  pos := -(X.zeroAdj Y.pos) + Y.zeroAdj X.pos

theorem tkkBracket_antisymm (X Y : TKKCarrier) :
    tkkBracket Y X = tkkNeg (tkkBracket X Y) := by
  cases X with
  | mk xn xo xa xp =>
    cases Y with
    | mk yn yo ya yp =>
      apply TKKCarrier.ext
      · simp [tkkBracket, tkkNeg]
      · apply LinearMap.ext
        intro z
        simp [tkkBracket, tkkNeg, LinearMap.comp_apply]
        abel
      · apply LinearMap.ext
        intro z
        simp [tkkBracket, tkkNeg, LinearMap.comp_apply]
        abel
      · simp [tkkBracket, tkkNeg]

theorem tkkBracket_self_zero (X : TKKCarrier) :
    tkkBracket X X = { neg := 0, zeroOp := 0, zeroAdj := 0, pos := 0 } := by
  apply TKKCarrier.ext
  · simp [tkkBracket]
  · apply LinearMap.ext
    intro z
    simp [tkkBracket, LinearMap.comp_apply]
  · apply LinearMap.ext
    intro z
    simp [tkkBracket, LinearMap.comp_apply]
  · simp [tkkBracket]

theorem tkk_jacobi_neg_neg_pos (x z xi : H3) :
    let X : TKKCarrier := { neg := x, zeroOp := 0, zeroAdj := 0, pos := 0 }
    let Z : TKKCarrier := { neg := z, zeroOp := 0, zeroAdj := 0, pos := 0 }
    let Xi : TKKCarrier := { neg := 0, zeroOp := 0, zeroAdj := 0, pos := xi }
    (tkkBracket X (tkkBracket Z Xi)).neg +
      (tkkBracket Z (tkkBracket Xi X)).neg +
        (tkkBracket Xi (tkkBracket X Z)).neg = 0 := by
  dsimp [tkkBracket, tkkNeg, jordanTripleD]
  simp [jordanTriple_outer_symm]

end InfoGeometry.Canonical.H3ZornTKKNative
