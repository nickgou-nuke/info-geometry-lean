/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/

import Mathlib
import Omega.Conclusion.RanktwoSmithBlindclassBooleanPrimeblockTorsor

namespace Omega.Conclusion

/-- The finite audit tuple extracted from the shared rank-two `gcd/lcm` normal form. -/
def ranktwoFiniteAuditData (P K M : Finset Nat) (a b : Nat) :
    Finset (Nat × Nat × Nat) × Finset (Nat × Nat × Nat) × Finset (Nat × Nat × Nat) ×
      (Nat × Nat × Nat) :=
  let g := Nat.gcd a b
  let l := Nat.lcm a b
  let h := l / g
  (P.image fun p => (p, g, l), K.image fun k => (k, g, h), M.image fun m => (m, l, h), (g, l, h))

/-- Paper label:
`thm:conclusion-ranktwo-finite-truncation-cannot-split-boolean-blindcavity`. Every coordinate of
the finite audit tuple is a function of the shared `gcd/lcm` normal form, so the tuple is constant
on each rank-two blind cavity. -/
theorem paper_conclusion_ranktwo_finite_truncation_cannot_split_boolean_blindcavity
    (P K M : Finset Nat) (a b c d : Nat) :
    (Nat.gcd c d = Nat.gcd a b /\ Nat.lcm c d = Nat.lcm a b) ->
      ranktwoFiniteAuditData P K M c d = ranktwoFiniteAuditData P K M a b := by
  intro h
  rcases h with ⟨hg, hl⟩
  simp [ranktwoFiniteAuditData, hg, hl]

end Omega.Conclusion
