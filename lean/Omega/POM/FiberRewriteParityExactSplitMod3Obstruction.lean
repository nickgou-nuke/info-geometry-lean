/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/

import Mathlib.Tactic
import Omega.Folding.FiberArithmeticProperties

namespace Omega.POM

/-- Exact parity balance for a finite sign-valued fiber. -/
theorem paper_pom_fiber_rewrite_parity_exact_split
    {α : Type*} [DecidableEq α] (S : Finset α) (sgn : α → ℤ)
    (hsgn : ∀ ω ∈ S, sgn ω = 1 ∨ sgn ω = -1) :
    let A := (S.filter (fun ω => sgn ω = 1)).card
    let B := (S.filter (fun ω => sgn ω = -1)).card
    2 * (A : ℤ) = S.card + ∑ ω ∈ S, sgn ω ∧
      2 * (B : ℤ) = S.card - ∑ ω ∈ S, sgn ω ∧
      (A = B ↔ (∑ ω ∈ S, sgn ω) = 0) := by
  dsimp
  exact ⟨Omega.parity_split_identity hsgn,
    Omega.parity_split_identity_odd hsgn,
    Omega.parity_split_balanced_iff_sum_zero hsgn⟩

end Omega.POM
