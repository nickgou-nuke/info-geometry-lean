import Mathlib.Tactic
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Canonical.ChiralSplitCartanActionBridge
import InfoGeometry.Canonical.SplitCartanChiralNilpotentBlock

/-!
# Finite Cartan action readout for the chiral nilpotent block

This file is only the finite interoperability edge between the explicit real
block owner and the generic split-Cartan action owner.  It introduces no new
Cartan action and makes no Clifford, Tomita, or analytic identification.
-/

noncomputable section

namespace InfoGeometry.Canonical.SplitCartanChiralNilpotentActionBridge

open InfoGeometry.Canonical.SplitCartanChiralNilpotentBlock

theorem cartanAction_eq_splitCartanDiagonal (a : ℝ) :
    cartanAction a =
      InfoGeometry.OperatorAlgebra.ChiralSplitCartanActionBridge.splitCartanDiagonal
        (A := ℝ) a := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [cartanAction,
      InfoGeometry.OperatorAlgebra.ChiralSplitCartanActionBridge.splitCartanDiagonal]

theorem cartanAction_conjugates_qPlus (a : ℝ) :
    cartanAction a * qPlus * cartanAction (-a) =
      !![0, Real.exp (2 * a); 0, 0] := by
  rw [cartanAction_eq_splitCartanDiagonal, cartanAction_eq_splitCartanDiagonal]
  change
    InfoGeometry.OperatorAlgebra.ChiralSplitCartanActionBridge.splitCartanConjugation a
        (InfoGeometry.OperatorAlgebra.ChiralCuntzSUSYNative.qPlus (1 : ℝ)) =
      !![0, Real.exp (2 * a); 0, 0]
  simpa [InfoGeometry.OperatorAlgebra.ChiralCuntzSUSYNative.qPlus] using
      (InfoGeometry.OperatorAlgebra.ChiralSplitCartanActionBridge.cartanConj_qPlus
        (A := ℝ) a (1 : ℝ))

theorem cartanAction_conjugates_qMinus (a : ℝ) :
    cartanAction a * qMinus * cartanAction (-a) =
      !![0, 0; Real.exp (-2 * a), 0] := by
  rw [cartanAction_eq_splitCartanDiagonal, cartanAction_eq_splitCartanDiagonal]
  change
    InfoGeometry.OperatorAlgebra.ChiralSplitCartanActionBridge.splitCartanConjugation a
        (InfoGeometry.OperatorAlgebra.ChiralCuntzSUSYNative.qMinus (1 : ℝ)) =
      !![0, 0; Real.exp (-2 * a), 0]
  simpa [InfoGeometry.OperatorAlgebra.ChiralCuntzSUSYNative.qMinus, neg_mul] using
      (InfoGeometry.OperatorAlgebra.ChiralSplitCartanActionBridge.cartanConj_qMinus
        (A := ℝ) a (1 : ℝ))

theorem cartanAction_conjugates_qAnticomm (a : ℝ) :
    cartanAction a * qAnticomm * cartanAction (-a) = qAnticomm := by
  rw [cartanAction_eq_splitCartanDiagonal, cartanAction_eq_splitCartanDiagonal]
  change
    InfoGeometry.OperatorAlgebra.ChiralSplitCartanActionBridge.splitCartanConjugation a
        (InfoGeometry.OperatorAlgebra.ChiralCuntzSUSYNative.qAnticomm (1 : ℝ) (1 : ℝ)) =
      InfoGeometry.OperatorAlgebra.ChiralCuntzSUSYNative.qAnticomm (1 : ℝ) (1 : ℝ)
  exact InfoGeometry.OperatorAlgebra.ChiralSplitCartanActionBridge.cartanConj_qAnticomm
    (A := ℝ) a (1 : ℝ) (1 : ℝ)

theorem cartanAction_conjugates_hodgeDirac (a : ℝ) :
    cartanAction a * hodgeDirac * cartanAction (-a) =
      !![0, Real.exp (2 * a); Real.exp (-2 * a), 0] := by
  rw [hodgeDirac, mul_add, add_mul,
    cartanAction_conjugates_qPlus, cartanAction_conjugates_qMinus]
  ext i j
  fin_cases i <;> fin_cases j <;> simp

theorem cartanAction_conjugates_hodgeLaplacian (a : ℝ) :
    cartanAction a * hodgeLaplacian * cartanAction (-a) = hodgeLaplacian := by
  rw [hodgeLaplacian_eq_qAnticomm, cartanAction_conjugates_qAnticomm]

end InfoGeometry.Canonical.SplitCartanChiralNilpotentActionBridge
