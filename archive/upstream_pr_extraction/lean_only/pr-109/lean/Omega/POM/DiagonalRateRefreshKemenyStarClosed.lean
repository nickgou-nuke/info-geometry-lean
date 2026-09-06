import Omega.POM.DiagonalRateRefreshFundamentalMatrixRankone
import Omega.POM.DiagonalRateRefreshHittingTimeMeanClosed
import Omega.POM.DiagonalRateRefreshHittingTimePGFClosed

namespace Omega.POM

/-- Paper label: `thm:pom-diagonal-rate-refresh-kemeny-star-closed`.
This chapter-local wrapper touches the closed hitting-time mean, the singleton-deleted
fundamental-matrix formula, and the closed PGF package on a concrete two-state instance. -/
theorem paper_pom_diagonal_rate_refresh_kemeny_star_closed :
    let r : Bool → ℚ := fun _ => 1
    let π : Bool → ℚ := fun b => if b then 0 else 1
    (diagonalRateAbsorbingMeanHitTime r π false true =
      1 / r false + (1 / π true) * ∑ z, if z = true then 0 else π z / r z) ∧
      pom_diagonal_rate_refresh_fundamental_matrix_rankone_formula r π true ∧
      (let G := fun z => diagonalRateRefreshHoldingPGF (r z) 0
       let Gbar := diagonalRateRefreshFailurePGF π true G
       let J := diagonalRateRefreshRenewalPGF π true G
       let F := diagonalRateRefreshClosedHittingPGF r π false true 0
       J = π true + (1 - π true) * Gbar * J ∧
         F = G false * J ∧
         F = G false * π true / (1 - (1 - π true) * Gbar)) := by
  let r : Bool → ℚ := fun _ => 1
  let π : Bool → ℚ := fun b => if b then 0 else 1
  dsimp [r, π]
  refine ⟨?_, ?_, ?_⟩
  · exact paper_pom_diagonal_rate_refresh_hitting_time_mean_closed
      (fun _ : Bool => 1) (fun b => if b then 0 else 1) false true
  · exact paper_pom_diagonal_rate_refresh_fundamental_matrix_rankone
      (fun _ : Bool => 1) (fun b => if b then 0 else 1) true
  · exact paper_pom_diagonal_rate_refresh_hitting_time_pgf_closed
      (fun _ : Bool => 1) (fun b => if b then 0 else 1) false true 0
      (by simp)
      (by simp [diagonalRateRefreshFailurePGF, diagonalRateRefreshHoldingPGF])

end Omega.POM
