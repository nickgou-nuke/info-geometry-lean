import Omega.Multiscale.NormalizedStokesFiniteCoverInverseTower

namespace Omega.Multiscale

noncomputable section

open NormalizedStokesFiniteCoverInverseTowerSystem

/-- Representative-independence and levelwise Stokes for normalized solenoid currents. -/
theorem paper_app_solenoid_fundamental_current_and_stokes
    (S : NormalizedStokesFiniteCoverInverseTowerSystem)
    (coverDegree_two_le : ∀ n, 2 ≤ S.coverDegree n)
    (bulkPullback : ∀ n, S.bulkIntegral (n + 1) =
      (S.coverDegree n : ℝ) * S.bulkIntegral n)
    (boundaryPullback : ∀ n, S.boundaryIntegral (n + 1) =
      (S.coverDegree n : ℝ) * S.boundaryIntegral n)
    (levelwiseStokes : ∀ n,
      S.differentialIntegral n = S.boundaryIntegral n) :
    (∀ n, normalizedBulk S (n + 1) = normalizedBulk S n) ∧
      (∀ n, normalizedBoundary S (n + 1) = normalizedBoundary S n) ∧
        (∀ n, normalizedDifferential S n = normalizedBoundary S n) := by
  exact ⟨normalizedBulk_step S coverDegree_two_le bulkPullback,
    normalizedBoundary_step S coverDegree_two_le boundaryPullback,
    normalizedStokes_levelwise S levelwiseStokes⟩

end

end Omega.Multiscale
