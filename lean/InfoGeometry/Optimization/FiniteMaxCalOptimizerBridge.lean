/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/

/- SPDX-License-Identifier: Apache-2.0 -/

import InfoGeometry.Optimization.FiniteMaxCalExistence
import InfoGeometry.Topology.MaximumCaliberPath

/-!
# Finite-candidate MaxCal optimizer construction

A finite feasible candidate family yields an inhabitant of the existing
`MaximumCaliberOptimizer` interface when it exhausts the feasible
 distributions. This is a finite existence theorem only; it asserts neither
uniqueness nor an unbounded path-space variational result.
-/

namespace InfoGeometry.Optimization

open InfoGeometry.Topology.MaximumCaliberPath

/-- Construct the existing MaxCal optimizer socket from a finite, exhaustive
family of feasible distributions. -/
theorem exists_maximumCaliberOptimizer_of_finite_candidates
    {Path : Type*}
    (candidateDistributions : Finset (Path → ℝ))
    (caliber : (Path → ℝ) → ℝ)
    (constraint : (Path → ℝ) → Prop)
    (hfeasible : ∃ μ ∈ candidateDistributions, constraint μ)
    (hexhaustive : ∀ μ, constraint μ → μ ∈ candidateDistributions) :
    ∃ M : MaximumCaliberOptimizer Path,
      M.optimizer ∈ candidateDistributions := by
  classical
  obtain ⟨μ, hμ, hμfeasible, hmax⟩ :=
    exists_maximizer_on_finite_feasible candidateDistributions constraint caliber hfeasible
  refine ⟨⟨caliber, constraint, μ, hμfeasible, ?_⟩, hμ⟩
  intro ν hν
  exact hmax ν (hexhaustive ν hν) hν

end InfoGeometry.Optimization
