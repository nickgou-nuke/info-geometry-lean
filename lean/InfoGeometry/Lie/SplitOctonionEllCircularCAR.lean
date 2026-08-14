import InfoGeometry.Lie.SplitOctonionEllCrossChannel

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

end InfoGeometry.Lie.SplitOctonionEllCircularCAR
