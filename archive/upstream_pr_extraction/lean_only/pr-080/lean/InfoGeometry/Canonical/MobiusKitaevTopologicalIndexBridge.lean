import Mathlib.Tactic
import InfoGeometry.Canonical.KitaevChainTopologicalPhasePfaffian
import InfoGeometry.Arithmetic.MangoldtFunctionalMobiusParityBridge

open InfoGeometry.Canonical.KitaevChainTopologicalPhasePfaffian
open InfoGeometry.Arithmetic.MangoldtFunctionalMobiusParityBridge

noncomputable section

namespace InfoGeometry.Canonical.MobiusKitaevTopologicalIndexBridge

/-- Real-valued Möbius Parity function μ(n) cast to ℝ. -/
def realMoebiusParity (n : ℕ) : ℝ :=
  (moebiusParity n : ℝ)

/-- The topological index readback agrees with the real-valued Möbius parity. -/
theorem topologicalIndex_realMoebiusParity (n : ℕ) :
    topologicalIndex (realMoebiusParity n) = realMoebiusParity n := by
  dsimp [realMoebiusParity, moebiusParity]
  by_cases hsq : Squarefree n
  · rw [ArithmeticFunction.moebius_apply_of_squarefree hsq]
    rcases Nat.even_or_odd (ArithmeticFunction.cardFactors n) with h_even | h_odd
    · rw [h_even.neg_one_pow]
      dsimp [topologicalIndex]
      norm_num
    · rw [h_odd.neg_one_pow]
      dsimp [topologicalIndex]
      norm_num
  · rw [ArithmeticFunction.moebius_eq_zero_of_not_squarefree hsq]
    dsimp [topologicalIndex]
    norm_num

/-- Zero-locus package combining the Kitaev sweet spot with non-squarefree Möbius vanishing. -/
theorem master_topological_index_unification
    (t : ℝ) (n : ℕ) (hn_sq : ¬ Squarefree n) :
    (topologicalIndex (pfaffian4 (kitaevMajoranaMatrix4 0 t t)) = 0) ∧
    (topologicalIndex (realMoebiusParity n) = 0) ∧
    (realMoebiusParity n = 0) := by
  have h_sweet := sweet_spot_topological_index_zero t
  have h_mob_zero := moebius_parity_zero_of_not_squarefree hn_sq
  have h_real_mob : realMoebiusParity n = 0 := by
    dsimp [realMoebiusParity]
    rw [h_mob_zero]
    norm_num
  have h_top_mob : topologicalIndex (realMoebiusParity n) = 0 := by
    rw [h_real_mob]
    dsimp [topologicalIndex]
    norm_num
  exact ⟨h_sweet, h_top_mob, h_real_mob⟩

end InfoGeometry.Canonical.MobiusKitaevTopologicalIndexBridge
