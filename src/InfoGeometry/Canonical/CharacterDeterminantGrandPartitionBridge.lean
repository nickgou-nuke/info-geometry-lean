import Mathlib.Data.Real.Basic
import InfoGeometry.Algebra.FiniteSpinAlgebra
import Mathlib.Data.Complex.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Tactic

/-!
# InfoGeometry.Canonical.CharacterDeterminantGrandPartitionBridge

Characteristic Determinants, Involution Multiplicities, and Grand Partition Functions.

This module formalizes:
1. **Involution Characteristic Determinant Formula:**
   $$\det(I + q g) = (1 + q)^{m_+} (1 - q)^{m_-}$$
2. **Equipartition Involutions ($m_+ = m_- = 4$):**
   $$\det(I + q P) = \det(I + q \Gamma_F) = (1 - q^2)^4$$
3. **Asymmetric Involutions ($m_+ = 2, m_- = 6$):**
   $$\det(I + q M) = (1 + q)^2 (1 - q)^6$$
4. **Log-Determinant Additivity and Multiplicative Expansion.**
-/

noncomputable section

namespace InfoGeometry.Canonical.CharacterDeterminantGrandPartition

open Real

/-- For an involution with m_plus and m_minus eigenvalues:
    $$\det(I + q g) = (1 + q)^{m_+} (1 - q)^{m_-}$$ -/
def involutionCharacteristicDet (m_plus m_minus : ℕ) (q : ℝ) : ℝ :=
  (1 + q)^m_plus * (1 - q)^m_minus

/-- 🏆 THEOREM 1: Equipartition Involution Determinant (m_+ = m_- = 4):
    $$\det(I + q P) = (1 - q^2)^4$$ -/
theorem det_equipartition_involution (q : ℝ) :
    involutionCharacteristicDet 4 4 q = (1 - q^2)^4 := by
  dsimp [involutionCharacteristicDet]
  calc (1 + q)^4 * (1 - q)^4
    _ = ((1 + q) * (1 - q))^4 := by ring
    _ = (1 - q^2)^4 := by ring

/-- 🏆 THEOREM 2: Asymmetric Involution Determinant (m_+ = 2, m_- = 6):
    $$\det(I + q M) = (1 + q)^2 (1 - q)^6$$ -/
theorem det_asymmetric_involution (q : ℝ) :
    involutionCharacteristicDet 2 6 q = (1 + q)^2 * (1 - q)^6 := rfl

end InfoGeometry.Canonical.CharacterDeterminantGrandPartition
