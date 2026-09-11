import InfoGeometry.Lie.SplitOctonionEllCrossChannel
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Lie.SplitOctonionCircularZ3Grading

/-!
# Native circular CAR packet

This owner exports the full colour-indexed opposite-channel relations and the
square-zero identities on the native canonical Zorn carrier.  It is an
algebraic completion of the paired product owner; no coordinate or
associativity claim is added.
-/

noncomputable section

set_option maxHeartbeats 1000000

namespace InfoGeometry.Lie.SplitOctonionEllCircularCAR

open InfoGeometry.Algebra.Zorn.KingdonCanonicalBridge
open InfoGeometry.Algebra.Zorn.SplitQuaternionCore
open InfoGeometry.Algebra.Zorn.SplitOctonionWittPlanes
open InfoGeometry.Lie.SplitOctonionEllPolarization
open InfoGeometry.Lie.SplitOctonionEllCrossChannel

abbrev CZ := CanonicalZorn

theorem rootPlus_mul_rootMinus_delta (a b : Fin 3) :
    rootPlus a * rootMinus b =
      (if a = b then uPlus else 0) := by
  fin_cases a <;> fin_cases b <;>
    ext i <;>
    simp [rootPlus, rootMinus, uPlus, chiralNull, ellBasis,
      quaternionBasis, iUnit, jUnit, kQuaternionUnit, lUnit,
      InfoGeometry.Algebra.Zorn.G2TrifactorSU3.zMul,
      InfoGeometry.Canonical.ZornMatrix.mul,
      Equiv.smul_def,
      InfoGeometry.Canonical.ZornMatrix.coordEquiv,
      InfoGeometry.Canonical.ZornMatrix.dot,
      InfoGeometry.Canonical.ZornMatrix.cross]
  all_goals (try fin_cases i) <;> norm_num

theorem rootMinus_mul_rootPlus_delta (a b : Fin 3) :
    rootMinus a * rootPlus b =
      (if a = b then uMinus else 0) := by
  fin_cases a <;> fin_cases b <;>
    ext i <;>
    simp [rootPlus, rootMinus, uMinus, chiralNull, ellBasis,
      quaternionBasis, iUnit, jUnit, kQuaternionUnit, lUnit,
      InfoGeometry.Algebra.Zorn.G2TrifactorSU3.zMul,
      InfoGeometry.Canonical.ZornMatrix.mul,
      Equiv.smul_def,
      InfoGeometry.Canonical.ZornMatrix.coordEquiv,
      InfoGeometry.Canonical.ZornMatrix.dot,
      InfoGeometry.Canonical.ZornMatrix.cross]
  all_goals (try fin_cases i) <;> norm_num

theorem rootPlus_sq_zero (a : Fin 3) :
    rootPlus a * rootPlus a = 0 := by
  fin_cases a <;>
    ext i <;>
    simp [rootPlus, chiralNull, ellBasis, quaternionBasis, iUnit,
      jUnit, kQuaternionUnit, lUnit,
      InfoGeometry.Algebra.Zorn.G2TrifactorSU3.zMul,
      InfoGeometry.Canonical.ZornMatrix.mul,
      Equiv.smul_def,
      InfoGeometry.Canonical.ZornMatrix.coordEquiv,
      InfoGeometry.Canonical.ZornMatrix.dot,
      InfoGeometry.Canonical.ZornMatrix.cross]
  all_goals (try fin_cases i) <;> norm_num

theorem rootMinus_sq_zero (a : Fin 3) :
    rootMinus a * rootMinus a = 0 := by
  fin_cases a <;>
    ext i <;>
    simp [rootMinus, chiralNull, ellBasis, quaternionBasis, iUnit,
      jUnit, kQuaternionUnit, lUnit,
      InfoGeometry.Algebra.Zorn.G2TrifactorSU3.zMul,
      InfoGeometry.Canonical.ZornMatrix.mul,
      Equiv.smul_def,
      InfoGeometry.Canonical.ZornMatrix.coordEquiv,
      InfoGeometry.Canonical.ZornMatrix.dot,
      InfoGeometry.Canonical.ZornMatrix.cross]
  all_goals (try fin_cases i) <;> norm_num

theorem rootPlus_mul_rootMinus_anticommutator (a b : Fin 3) :
    rootPlus a * rootMinus b + rootMinus b * rootPlus a =
      (if a = b then (1 : CZ) else 0) := by
  rw [rootPlus_mul_rootMinus_delta, rootMinus_mul_rootPlus_delta]
  by_cases h : a = b
  · simpa [h] using uPlus_add_uMinus
  · have h' : b ≠ a := by exact Ne.symm h
    simp [h, h']

theorem rootPlus_mul_rootMinus_commutator (a b : Fin 3) :
    rootPlus a * rootMinus b - rootMinus b * rootPlus a =
      (if a = b then lUnit else 0) := by
  rw [rootPlus_mul_rootMinus_delta, rootMinus_mul_rootPlus_delta]
  by_cases h : a = b
  · simpa [h] using uPlus_sub_uMinus
  · have h' : b ≠ a := by exact Ne.symm h
    simp [h, h']

theorem rootPlus_mul_rootPlus_anticommutator (a b : Fin 3) :
    rootPlus a * rootPlus b + rootPlus b * rootPlus a = 0 := by
  fin_cases a <;> fin_cases b
  · simpa only [rootPlus_sq_zero, zero_add]
  · simpa [Fin.ext_iff] using congrArg₂ (fun x y : CZ => x + y)
      InfoGeometry.Lie.SplitOctonionCircularZ3Grading.rootPlus_zero_mul_rootPlus_one
      InfoGeometry.Lie.SplitOctonionCircularZ3Grading.rootPlus_one_mul_rootPlus_zero
  · simpa [Fin.ext_iff] using congrArg₂ (fun x y : CZ => x + y)
      InfoGeometry.Lie.SplitOctonionCircularZ3Grading.rootPlus_zero_mul_rootPlus_two
      InfoGeometry.Lie.SplitOctonionCircularZ3Grading.rootPlus_two_mul_rootPlus_zero
  · simpa [Fin.ext_iff] using congrArg₂ (fun x y : CZ => x + y)
      InfoGeometry.Lie.SplitOctonionCircularZ3Grading.rootPlus_one_mul_rootPlus_zero
      InfoGeometry.Lie.SplitOctonionCircularZ3Grading.rootPlus_zero_mul_rootPlus_one
  · simpa only [rootPlus_sq_zero, zero_add]
  · simpa [Fin.ext_iff] using congrArg₂ (fun x y : CZ => x + y)
      InfoGeometry.Lie.SplitOctonionCircularZ3Grading.rootPlus_one_mul_rootPlus_two
      InfoGeometry.Lie.SplitOctonionCircularZ3Grading.rootPlus_two_mul_rootPlus_one
  · simpa [Fin.ext_iff] using congrArg₂ (fun x y : CZ => x + y)
      InfoGeometry.Lie.SplitOctonionCircularZ3Grading.rootPlus_two_mul_rootPlus_zero
      InfoGeometry.Lie.SplitOctonionCircularZ3Grading.rootPlus_zero_mul_rootPlus_two
  · simpa [Fin.ext_iff] using congrArg₂ (fun x y : CZ => x + y)
      InfoGeometry.Lie.SplitOctonionCircularZ3Grading.rootPlus_two_mul_rootPlus_one
      InfoGeometry.Lie.SplitOctonionCircularZ3Grading.rootPlus_one_mul_rootPlus_two
  · simpa only [rootPlus_sq_zero, zero_add]

theorem rootMinus_mul_rootMinus_anticommutator (a b : Fin 3) :
    rootMinus a * rootMinus b + rootMinus b * rootMinus a = 0 := by
  fin_cases a <;> fin_cases b
  · simp only [rootMinus_sq_zero, zero_add]
  · apply InfoGeometry.Canonical.ZornMatrix.ext <;>
      simp [rootMinus, chiralNull, ellBasis, quaternionBasis, iUnit,
        jUnit, kQuaternionUnit, lUnit,
        InfoGeometry.Algebra.Zorn.G2TrifactorSU3.zMul,
        InfoGeometry.Canonical.ZornMatrix.mul,
        InfoGeometry.Canonical.ZornMatrix.dot,
        InfoGeometry.Canonical.ZornMatrix.cross,
        Equiv.smul_def, InfoGeometry.Canonical.ZornMatrix.coordEquiv] <;> ring <;> simp
  · apply InfoGeometry.Canonical.ZornMatrix.ext <;>
      simp [rootMinus, chiralNull, ellBasis, quaternionBasis, iUnit,
        jUnit, kQuaternionUnit, lUnit,
        InfoGeometry.Algebra.Zorn.G2TrifactorSU3.zMul,
        InfoGeometry.Canonical.ZornMatrix.mul,
        InfoGeometry.Canonical.ZornMatrix.dot,
        InfoGeometry.Canonical.ZornMatrix.cross,
        Equiv.smul_def, InfoGeometry.Canonical.ZornMatrix.coordEquiv] <;> ring <;> simp
  · apply InfoGeometry.Canonical.ZornMatrix.ext <;>
      simp [rootMinus, chiralNull, ellBasis, quaternionBasis, iUnit,
        jUnit, kQuaternionUnit, lUnit,
        InfoGeometry.Algebra.Zorn.G2TrifactorSU3.zMul,
        InfoGeometry.Canonical.ZornMatrix.mul,
        InfoGeometry.Canonical.ZornMatrix.dot,
        InfoGeometry.Canonical.ZornMatrix.cross,
        Equiv.smul_def, InfoGeometry.Canonical.ZornMatrix.coordEquiv] <;> ring <;> simp
  · simp only [rootMinus_sq_zero, zero_add]
  · apply InfoGeometry.Canonical.ZornMatrix.ext <;>
      simp [rootMinus, chiralNull, ellBasis, quaternionBasis, iUnit,
        jUnit, kQuaternionUnit, lUnit,
        InfoGeometry.Algebra.Zorn.G2TrifactorSU3.zMul,
        InfoGeometry.Canonical.ZornMatrix.mul,
        InfoGeometry.Canonical.ZornMatrix.dot,
        InfoGeometry.Canonical.ZornMatrix.cross,
        Equiv.smul_def, InfoGeometry.Canonical.ZornMatrix.coordEquiv] <;> ring <;> simp
  · apply InfoGeometry.Canonical.ZornMatrix.ext <;>
      simp [rootMinus, chiralNull, ellBasis, quaternionBasis, iUnit,
        jUnit, kQuaternionUnit, lUnit,
        InfoGeometry.Algebra.Zorn.G2TrifactorSU3.zMul,
        InfoGeometry.Canonical.ZornMatrix.mul,
        InfoGeometry.Canonical.ZornMatrix.dot,
        InfoGeometry.Canonical.ZornMatrix.cross,
        Equiv.smul_def, InfoGeometry.Canonical.ZornMatrix.coordEquiv] <;> ring <;> simp
  · apply InfoGeometry.Canonical.ZornMatrix.ext <;>
      simp [rootMinus, chiralNull, ellBasis, quaternionBasis, iUnit,
        jUnit, kQuaternionUnit, lUnit,
        InfoGeometry.Algebra.Zorn.G2TrifactorSU3.zMul,
        InfoGeometry.Canonical.ZornMatrix.mul,
        InfoGeometry.Canonical.ZornMatrix.dot,
        InfoGeometry.Canonical.ZornMatrix.cross,
        Equiv.smul_def, InfoGeometry.Canonical.ZornMatrix.coordEquiv] <;> ring
  · simp only [rootMinus_sq_zero, zero_add]

end InfoGeometry.Lie.SplitOctonionEllCircularCAR
