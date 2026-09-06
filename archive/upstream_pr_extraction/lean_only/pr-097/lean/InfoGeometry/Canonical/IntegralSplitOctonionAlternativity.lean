import Mathlib
import InfoGeometry.Canonical.StandardIntegralSplitOctonionMultiplication
import InfoGeometry.Canonical.ZornVectorMatrixIsomorphism

namespace InfoGeometry.Canonical

/-!
The integral coordinate product is related to the native rational Zorn product
by scalar extension.  Alternativity is transported through that native map;
the proof does not unfold the full octonion associator into a heartbeat-sized
polynomial normalization problem.
-/

def integralToRational
    (x : StandardIntegralSplitOctonion) :
    StandardRationalSplitOctonion :=
  fun b => (x b : ℚ)

theorem integralToRational_injective :
    Function.Injective integralToRational := by
  intro x y h
  funext b
  have hb := congrFun h b
  change (x b : ℚ) = (y b : ℚ) at hb
  exact_mod_cast hb

theorem integralToRational_mul
    (x y : StandardIntegralSplitOctonion) :
    integralToRational (splitOctonionMul x y) =
      splitOctonionMulQ (integralToRational x) (integralToRational y) := by
  ext b
  cases b <;>
    simp [integralToRational, splitOctonionMul, splitOctonionMulQ,
      splitQuaternionOf, splitQuaternionLPart, splitQuaternionConj,
      splitQuaternionMul, splitQuaternionAdd,
      splitOctonionOfQuaternionPair,
      splitQuaternionOfQ, splitQuaternionLPartQ, splitQuaternionConjQ,
      splitQuaternionMulQ, splitQuaternionAddQ,
      splitOctonionOfQuaternionPairQ] <;>
    ring

private theorem native_sub_eq_zero
    {A B : InfoGeometry.Algebra.ZornVectorMatrix ℚ}
    (h : InfoGeometry.Algebra.ZornVectorMatrix.sub A B =
      InfoGeometry.Algebra.ZornVectorMatrix.zero) :
    A = B := by
  have ha := congrArg (fun Z => Z.a) h
  have hb := congrArg (fun Z => Z.b) h
  have hv (i : Fin 3) := congrArg (fun Z => Z.v i) h
  have hw (i : Fin 3) := congrArg (fun Z => Z.w i) h
  have ha0 : A.a - B.a = 0 := by
    simpa [InfoGeometry.Algebra.ZornVectorMatrix.sub,
      InfoGeometry.Algebra.ZornVectorMatrix.add,
      InfoGeometry.Algebra.ZornVectorMatrix.neg,
      InfoGeometry.Algebra.ZornVectorMatrix.zero,
      sub_eq_add_neg] using ha
  have hb0 : A.b - B.b = 0 := by
    simpa [InfoGeometry.Algebra.ZornVectorMatrix.sub,
      InfoGeometry.Algebra.ZornVectorMatrix.add,
      InfoGeometry.Algebra.ZornVectorMatrix.neg,
      InfoGeometry.Algebra.ZornVectorMatrix.zero,
      sub_eq_add_neg] using hb
  have ha' : A.a = B.a := sub_eq_zero.mp ha0
  have hb' : A.b = B.b := sub_eq_zero.mp hb0
  have hv' : A.v = B.v := by
    funext i
    have hi := hv i
    have hi' : A.v i - B.v i = 0 := by
      simpa [InfoGeometry.Algebra.ZornVectorMatrix.sub,
        InfoGeometry.Algebra.ZornVectorMatrix.add,
        InfoGeometry.Algebra.ZornVectorMatrix.neg,
        InfoGeometry.Algebra.ZornVectorMatrix.zero,
        sub_eq_add_neg] using hi
    exact sub_eq_zero.mp hi'
  have hw' : A.w = B.w := by
    funext i
    have hi := hw i
    have hi' : A.w i - B.w i = 0 := by
      simpa [InfoGeometry.Algebra.ZornVectorMatrix.sub,
        InfoGeometry.Algebra.ZornVectorMatrix.add,
        InfoGeometry.Algebra.ZornVectorMatrix.neg,
        InfoGeometry.Algebra.ZornVectorMatrix.zero,
        sub_eq_add_neg] using hi
    exact sub_eq_zero.mp hi'
  cases A
  cases B
  simp_all

theorem splitOctonion_left_alternative
    (x y : StandardIntegralSplitOctonion) :
    splitOctonionMul x (splitOctonionMul x y) =
      splitOctonionMul (splitOctonionMul x x) y := by
  apply integralToRational_injective
  rw [integralToRational_mul, integralToRational_mul,
    integralToRational_mul, integralToRational_mul]
  let X := zornVectorMatrixRationalEquiv (integralToRational x)
  let Y := zornVectorMatrixRationalEquiv (integralToRational y)
  have h := InfoGeometry.Algebra.ZornVectorMatrix.associator_left_alternative X Y
  apply zornVectorMatrixRationalEquiv.injective
  rw [zornVectorMatrixRationalEquiv_map_mul,
    zornVectorMatrixRationalEquiv_map_mul,
    zornVectorMatrixRationalEquiv_map_mul,
    zornVectorMatrixRationalEquiv_map_mul]
  have hz0 : InfoGeometry.Algebra.ZornVectorMatrix.sub
      (InfoGeometry.Algebra.ZornVectorMatrix.mul
        (InfoGeometry.Algebra.ZornVectorMatrix.mul X X) Y)
      (InfoGeometry.Algebra.ZornVectorMatrix.mul X
        (InfoGeometry.Algebra.ZornVectorMatrix.mul X Y)) = 0 := by
    simpa [InfoGeometry.Algebra.ZornVectorMatrix.associator] using h
  exact (native_sub_eq_zero hz0).symm

theorem splitOctonion_right_alternative
    (x y : StandardIntegralSplitOctonion) :
    splitOctonionMul (splitOctonionMul y x) x =
      splitOctonionMul y (splitOctonionMul x x) := by
  apply integralToRational_injective
  rw [integralToRational_mul, integralToRational_mul,
    integralToRational_mul, integralToRational_mul]
  let X := zornVectorMatrixRationalEquiv (integralToRational x)
  let Y := zornVectorMatrixRationalEquiv (integralToRational y)
  have h := InfoGeometry.Algebra.ZornVectorMatrix.associator_right_alternative Y X
  apply zornVectorMatrixRationalEquiv.injective
  rw [zornVectorMatrixRationalEquiv_map_mul,
    zornVectorMatrixRationalEquiv_map_mul,
    zornVectorMatrixRationalEquiv_map_mul,
    zornVectorMatrixRationalEquiv_map_mul]
  have hz0 : InfoGeometry.Algebra.ZornVectorMatrix.sub
      (InfoGeometry.Algebra.ZornVectorMatrix.mul
        (InfoGeometry.Algebra.ZornVectorMatrix.mul Y X) X)
      (InfoGeometry.Algebra.ZornVectorMatrix.mul Y
        (InfoGeometry.Algebra.ZornVectorMatrix.mul X X)) = 0 := by
    simpa [InfoGeometry.Algebra.ZornVectorMatrix.associator] using h
  exact native_sub_eq_zero hz0

theorem splitOctonion_flexible
    (x y : StandardIntegralSplitOctonion) :
    splitOctonionMul (splitOctonionMul x y) x =
      splitOctonionMul x (splitOctonionMul y x) := by
  apply integralToRational_injective
  rw [integralToRational_mul, integralToRational_mul,
    integralToRational_mul, integralToRational_mul]
  let X := zornVectorMatrixRationalEquiv (integralToRational x)
  let Y := zornVectorMatrixRationalEquiv (integralToRational y)
  have h := InfoGeometry.Algebra.ZornVectorMatrix.associator_flexible X Y
  apply zornVectorMatrixRationalEquiv.injective
  rw [zornVectorMatrixRationalEquiv_map_mul,
    zornVectorMatrixRationalEquiv_map_mul,
    zornVectorMatrixRationalEquiv_map_mul,
    zornVectorMatrixRationalEquiv_map_mul]
  have hz0 : InfoGeometry.Algebra.ZornVectorMatrix.sub
      (InfoGeometry.Algebra.ZornVectorMatrix.mul
        (InfoGeometry.Algebra.ZornVectorMatrix.mul X Y) X)
      (InfoGeometry.Algebra.ZornVectorMatrix.mul X
        (InfoGeometry.Algebra.ZornVectorMatrix.mul Y X)) = 0 := by
    simpa [InfoGeometry.Algebra.ZornVectorMatrix.associator] using h
  exact native_sub_eq_zero hz0

end InfoGeometry.Canonical
