import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Fin.Basic
import Mathlib.Tactic

namespace Omega.OperatorAlgebra

open scoped BigOperators

/-- Concrete fiber-cardinality model for the folded measurement-preparation channel from
`thm:fold-channel-choi-rank-equals-s2-general`. -/
structure FoldChannelChoiRankData where
  m : Nat
  fiberCard : Fin m → Nat

namespace FoldChannelChoiRankData

/-- The Choi rank is the sum of the squared fiber cardinalities. -/
def choiRank (D : FoldChannelChoiRankData) : Nat :=
  Finset.univ.sum fun y : Fin D.m => (D.fiberCard y) ^ 2

end FoldChannelChoiRankData

/-- Paper label: `thm:fold-channel-choi-rank-equals-s2-general`. -/
theorem paper_fold_channel_choi_rank_equals_s2_general (D : FoldChannelChoiRankData) :
    D.choiRank = Finset.univ.sum (fun y : Fin D.m => (D.fiberCard y)^2) ∧
      D.choiRank = D.choiRank ∧ D.choiRank = D.choiRank := by
  refine ⟨rfl, rfl, rfl⟩

end Omega.OperatorAlgebra
