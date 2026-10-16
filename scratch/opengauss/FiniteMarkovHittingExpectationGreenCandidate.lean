/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.QuantumContext.FiniteMarkovHittingPMFExpectation
import InfoGeometry.QuantumContext.FiniteMarkovDirichletApproximation
import InfoGeometry.QuantumContext.FiniteMarkovHittingColimitGreen

/-!
# Candidate: finite path-expectation supremum and the group-inverse potential

This candidate identifies the supremum of the finite-horizon PMF expectations
with the already established order-colimit Green potential. It asserts no
expectation over an infinite path space.
-/

namespace InfoGeometry.QuantumContext.FiniteMarkovHittingExpectationGreenCandidate

open InfoGeometry.QuantumContext.FiniteMarkovHittingPMFExpectation
open InfoGeometry.QuantumContext.FiniteMarkovHittingColimitGreen
open InfoGeometry.QuantumContext.FiniteMarkovDirichletApproximation
open InfoGeometry.QuantumContext.MarkovDrazin
open InfoGeometry.Canonical.HartwigSouriauFrameDrazin

/-- The supremum of the finite-horizon successor-path PMF costs equals the
group-inverse Dirichlet potential. This is a supremum over finite-horizon
expectations, with no infinite-path expectation interpretation. -/
theorem successorPathExpectedCost_sup_eq_groupInversePotentialDifference
    {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]
    (P G : Matrix ι ι ℝ) (π : ι → ℝ)
    (hP : P ∈ Matrix.rowStochastic ℝ ι)
    (hPpos : ∀ i j, 0 < P i j)
    (hπnonneg : ∀ i, 0 ≤ π i)
    (hπsum : ∑ i, π i = 1)
    (hπstat : ∀ j, ∑ i, π i * P i j = π j)
    (hG : IsGroupInverse (1 - P) G)
    (target i : ι) :
    sSup (Set.range (fun n => successorPathExpectedCost P hP target n i)) =
      groupInversePotentialDifference π G i target := by
  have hseq : (fun n => successorPathExpectedCost P hP target n i) =
      (fun n => firstHitApproximation P target n i) := by
    funext n
    exact successorPathExpectedCost_eq_firstHitApproximation
      P hP target n i
  rw [hseq]
  exact firstHitApproximationColimit_eq_groupInversePotentialDifference
    P G π hP hPpos hπnonneg hπsum hπstat hG target i

end InfoGeometry.QuantumContext.FiniteMarkovHittingExpectationGreenCandidate
