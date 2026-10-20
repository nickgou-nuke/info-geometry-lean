/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/

import Mathlib

/-!
# Finite maximum-caliber existence

This is the finite variational theorem only.  It uses a finite candidate
carrier and a decidable feasibility predicate; it makes no analytic,
compactness, uniqueness, or infinite-dimensional claim.
-/

namespace InfoGeometry.Optimization

theorem exists_maximizer_on_finite_feasible
    {Path : Type*} [DecidableEq Path]
    (candidates : Finset Path) (feasible : Path → Prop)
    [DecidablePred feasible]
    (caliber : Path → ℝ)
    (hfeasible : ∃ p ∈ candidates, feasible p) :
    ∃ p ∈ candidates, feasible p ∧
      ∀ q ∈ candidates, feasible q → caliber q ≤ caliber p := by
  let feasibleCandidates := candidates.filter feasible
  have hne : feasibleCandidates.Nonempty := by
    rcases hfeasible with ⟨p, hp, hfp⟩
    exact ⟨p, Finset.mem_filter.mpr ⟨hp, hfp⟩⟩
  obtain ⟨p, hp, hmax⟩ := Finset.exists_max_image feasibleCandidates caliber hne
  refine ⟨p, (Finset.mem_filter.mp hp).1, (Finset.mem_filter.mp hp).2, ?_⟩
  intro q hq hqf
  apply hmax q
  exact Finset.mem_filter.mpr ⟨hq, hqf⟩

end InfoGeometry.Optimization
