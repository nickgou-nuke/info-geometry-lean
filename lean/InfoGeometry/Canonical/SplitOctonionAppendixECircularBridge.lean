import InfoGeometry.Clifford.GogberashviliAppendixE
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Clifford.SplitOctonionQuaternionEllBridge

/-!
# Appendix-E sign calibration

The explicit Appendix-E zero divisors are the same elements as the existing
quaternionic Witt channels.  The only convention issue is the lower channel:
the paper's `G⁻` is the negative of the repository's `wittMinus`.
No new carrier or multiplication is introduced here.
-/

noncomputable section

namespace InfoGeometry.Canonical.SplitOctonionAppendixECircularBridge

open InfoGeometry.Clifford.GogberashviliAppendixE
open InfoGeometry.Clifford.GogberashviliSplitOctonionBasis
open InfoGeometry.Clifford.SplitOctonionQuaternionEllBridge

abbrev ECarrier := InfoGeometry.Algebra.Zorn.ConcreteComposition.ZornCell ℝ

theorem appendixE_DPlusI_eq_rhoPlus : DPlusI = rhoPlus := rfl

theorem appendixE_DMinusI_eq_rhoMinus : DMinusI = rhoMinus := rfl

theorem appendixE_GnPlusJ_eq_wittPlus (n : Fin 3) :
    GnPlusJ n = wittPlus n := by
  fin_cases n <;>
    apply zorn_ext <;>
      dsimp only [GnPlusJ, wittPlus, quaternionUnit, ellLift,
        J, j, smulZ_val, addZ_val, smulZ, addZ] <;>
      ring

theorem appendixE_GnMinusJ_eq_neg_wittMinus (n : Fin 3) :
    GnMinusJ n = negZ (wittMinus n) := by
  fin_cases n <;>
    apply zorn_ext <;>
      dsimp only [GnMinusJ, wittMinus, quaternionUnit, ellLift,
        J, j, negZ, smulZ_val, addZ_val, smulZ, addZ] <;>
      ring

theorem appendixE_GnPlusJ_sq (n : Fin 3) :
    GnPlusJ n * GnPlusJ n = 0 := by
  exact GnPlusJ_sq n

theorem appendixE_GnMinusJ_sq (n : Fin 3) :
    GnMinusJ n * GnMinusJ n = 0 := by
  exact GnMinusJ_sq n

theorem appendixE_GnPlusJ_anticommutator (n : Fin 3) :
    GnPlusJ n * GnMinusJ n + GnMinusJ n * GnPlusJ n = oneZ := by
  exact GnPlusJ_anticommutator_GnMinusJ n

def appendixEExpansion (α β : ℝ) (y z : Fin 3 → ℝ) : ECarrier :=
  α • DPlusI + sumFin3 (fun n => y n • GnPlusJ n) +
    β • DMinusI + sumFin3 (fun n => z n • GnMinusJ n)

def appendixEUpperCoordinates (X : ECarrier) : Fin 3 → ℝ
  | 0 => X.x1
  | 1 => X.x2
  | 2 => X.x3

def appendixELowerCoordinates (X : ECarrier) : Fin 3 → ℝ
  | 0 => X.y1
  | 1 => X.y2
  | 2 => X.y3

theorem appendixEExpansion_reconstruct (X : ECarrier) :
    appendixEExpansion X.r X.s
        (appendixEUpperCoordinates X) (appendixELowerCoordinates X) = X := by
  apply zorn_ext <;>
    simp [appendixEExpansion, DPlusI, DMinusI, GnPlusJ, GnMinusJ,
      appendixEUpperCoordinates, appendixELowerCoordinates,
      oneZ, I, J, j, negZ, smulZ_val, addZ_val, smulZ, addZ,
      sumFin3] <;>
    ring

end InfoGeometry.Canonical.SplitOctonionAppendixECircularBridge
