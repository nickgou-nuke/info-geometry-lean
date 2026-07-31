import Mathlib.Tactic
import Omega.Folding.ZeckendorfSignature
import Omega.GU.Window6P6CompactnessPrinciple

namespace Omega.GU

open Omega.ZeckSig

/-- Compactness plus the audited Zeckendorf data for `12 = 8 + 3 + 1`: this is the concrete
chapter-local package recording the standard-model dimension split and its no-adjacent-gap audit.
-/
def Window6SMUniquenessFromZeckendorfUnderCompactness
    (selfadjoint unitaryCompact : Prop) : Prop :=
  selfadjoint ∧
    unitaryCompact ∧
    12 = Nat.fib 6 + Nat.fib 4 + Nat.fib 2 ∧
    Nat.fib 2 + Nat.fib 4 + Nat.fib 6 = 12 ∧
    Nat.fib 2 = 1 ∧ Nat.fib 4 = 3 ∧ Nat.fib 6 = 8 ∧
    4 - 2 ≥ 2 ∧ 6 - 4 ≥ 2

/-- Under the compactness principle for the window-`6` observable, the Zeckendorf audit at
dimension `12` matches the unique SM-type decomposition `1 + 3 + 8`.
    prop:window6-sm-uniqueness-from-zeckendorf-under-compactness -/
theorem paper_window6_sm_uniqueness_from_zeckendorf_under_compactness :
    ∀ (selfadjoint finiteDim commutantStarAlg unitaryCompact : Prop),
      selfadjoint →
      finiteDim →
      (selfadjoint → finiteDim → commutantStarAlg) →
      (commutantStarAlg → unitaryCompact) →
      Window6SMUniquenessFromZeckendorfUnderCompactness selfadjoint unitaryCompact := by
  intro selfadjoint finiteDim commutantStarAlg unitaryCompact
    hSelfadjoint hFinite hComm hCompact
  have hCompact :=
    paper_window6_p6_compactness_principle
      selfadjoint finiteDim commutantStarAlg unitaryCompact
      hSelfadjoint hFinite hComm hCompact
  rcases sm_boundary_count with ⟨hSum, hFib2, hFib4, hFib6⟩
  rcases sm_zeckendorf_no_adjacent with ⟨hGap24, hGap46⟩
  refine ⟨hCompact.1, hCompact.2, dim_sm_zeckendorf, hSum, hFib2, hFib4, hFib6, hGap24, hGap46⟩

end Omega.GU
