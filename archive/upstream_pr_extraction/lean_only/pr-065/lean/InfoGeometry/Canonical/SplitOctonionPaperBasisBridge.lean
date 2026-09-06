import InfoGeometry.Algebra.ZornMatrix
import InfoGeometry.Canonical.SplitOctonionGogberashviliNormBridge
import Mathlib.Tactic

/-!
# Real paper-basis bridge for the native split-Zorn carrier

This owner records the linear dictionary between the paper notation
`1, J_i, j_i, I` and the native Peirce/chiral Zorn basis.  It is a real
coordinate bridge only: it does not identify the nonassociative carrier with
a Clifford algebra or assert a `G₂` theorem.
-/

namespace InfoGeometry.Canonical.SplitOctonionPaperBasisBridge

noncomputable section

open InfoGeometry.Algebra
open InfoGeometry.Algebra.ZornMatrix
open InfoGeometry.Canonical.SplitOctonionGogberashviliNormBridge

abbrev Native := ZornMatrix ℝ

def paperOne : Native := I
def paperI : Native := E11 - E22
def paperJ (i : Fin 3) : Native := U i + V i
def paperj (i : Fin 3) : Native := V i - U i

def paperUPlus : Native := E11
def paperUMinus : Native := E22
def paperSPlus (i : Fin 3) : Native := U i
def paperSMinus (i : Fin 3) : Native := V i

theorem paper_one_eq_uPlus_add_uMinus :
    paperOne = paperUPlus + paperUMinus := by
  apply ZornMatrix.ext
  · simp [paperOne, paperUPlus, paperUMinus, I, E11, E22, add]
  · funext i
    fin_cases i <;>
      simp [paperOne, paperUPlus, paperUMinus, I, E11, E22,
        add, Vec3.add]
  · funext i
    fin_cases i <;>
      simp [paperOne, paperUPlus, paperUMinus, I, E11, E22,
        add, Vec3.add]
  · simp [paperOne, paperUPlus, paperUMinus, I, E11, E22, add]

theorem paper_I_eq_uPlus_sub_uMinus :
    paperI = paperUPlus - paperUMinus := rfl

theorem paper_J_eq_SPlus_add_SMinus (i : Fin 3) :
    paperJ i = paperSPlus i + paperSMinus i := rfl

theorem paper_j_eq_SMinus_sub_SPlus (i : Fin 3) :
    paperj i = paperSMinus i - paperSPlus i := rfl

theorem paper_coordinate_readout (c omega : ℝ)
    (lambdaVec positionVec : Fin 3 → ℝ) (t : ℝ) :
    toNativeZorn c
        { omega := omega, lambda := lambdaVec,
          position := positionVec, time := t } =
      { a := omega + c * t
        v := fun i => lambdaVec i - positionVec i
        w := fun i => lambdaVec i + positionVec i
        b := omega - c * t } := by
  apply ZornMatrix.ext
  · rfl
  · funext i
    fin_cases i <;> simp [toNativeZorn, Vec3.sub]
  · funext i
    fin_cases i <;> simp [toNativeZorn, Vec3.add]
  · rfl

theorem paperNorm_eq_zornNorm (c : ℝ)
    (s : SignalCoordinates) :
    zornNorm (toNativeZorn c s) = signalNorm c s :=
  native_zorn_norm_eq_signalNorm c s

end
end InfoGeometry.Canonical.SplitOctonionPaperBasisBridge
