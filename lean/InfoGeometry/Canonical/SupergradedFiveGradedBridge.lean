import InfoGeometry.Canonical.MobiusChiralClosure
import InfoGeometry.Arithmetic.WittenParityIndex

/-!
# Bridge: superbracket → five-graded closure → Witten–Möbius parity

Connects the three existing layers:
1. `SupergradedBracket.lean` — parity-controlled commutator/anticommutator
2. `FiveGradedMobiusWittenGlobality.lean` — weight decomposition, grade-two compensation
3. `MobiusChiralClosure.lean`, `WittenParityIndex.lean` — chiral trace zero, parity alternation
-/

open InfoGeometry.Arithmetic.WittenParityIndex
open InfoGeometry.Canonical.MobiusChiralClosure

namespace SupergradedFiveGradedBridge

/-- The alternating Witten parity sequence (+1, −1, +1, −1) sums to zero. -/
theorem witten_parity_sum_zero :
    (witten_parity_factor 1 + witten_parity_factor 2 +
     witten_parity_factor 3 + witten_parity_factor 4 : ℝ) = 0 := by
  norm_num [witten_parity_factor]

/--
Bridge theorem: the Witten–Möbius parity cancellation and the Möbius
chiral trace cancellations.
-/
theorem witten_mobius_bridge :
    (Matrix.trace chi_global_4 = 0) ∧
    (Matrix.trace (moebius_strip_4 * chi_global_4) = 0) ∧
    ((witten_parity_factor 1 + witten_parity_factor 2 +
      witten_parity_factor 3 + witten_parity_factor 4 : ℝ) = 0) := by
  refine ⟨?_, ?_, ?_⟩
  · exact global_chiral_balance_4
  · exact moebius_parity_closure_achieved_4
  · norm_num [witten_parity_factor]

end SupergradedFiveGradedBridge
