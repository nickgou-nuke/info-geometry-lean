import InfoGeometry.Probability.SquareRootSimplexBridge
import InfoGeometry.Thermo.FiniteDiagonal

/-!
# Finite diagonal Gibbs square-root readout

The finite diagonal Gibbs owner already supplies positive normalized weights.
This file transports that existing probability vector through the shared
square-root coordinate owner.  It adds no new partition or density object.
-/

open scoped BigOperators

namespace InfoGeometry.Thermo.FiniteDiagonal

open InfoGeometry.Probability.Homological
open InfoGeometry.Probability.SquareRootSimplexBridge

variable {n : ℕ} [Nonempty (Fin n)]

theorem gibbsWeight_squareRootEmbedding_sum_sq
    (H : Fin n → ℝ) (β : ℝ) :
    ∑ i, (squareRootEmbedding n (gibbsWeight H β) i) ^ 2 = 4 := by
  exact squareRootEmbedding_sum_sq
    (gibbsWeight H β)
    (fun i => gibbsWeight_nonneg H β i)
    (gibbsWeight_sum_one H β)

theorem gibbsDensity_diag_eq_squareRoot_sq_div_four
    (H : Fin n → ℝ) (β : ℝ) (i : Fin n) :
    gibbsDensity H β i i =
      ((squareRootEmbedding n (gibbsWeight H β) i) ^ 2 / 4 : ℝ) := by
  change gibbsWeight H β i =
    (squareRootEmbedding n (gibbsWeight H β) i) ^ 2 / 4
  rw [squareRootEmbedding_sq (gibbsWeight H β)
    (fun j => gibbsWeight_nonneg H β j) i]
  ring

theorem gibbsDensity_posSemidef
    (H : Fin n → ℝ) (β : ℝ) :
    Matrix.PosSemidef (gibbsDensity H β) := by
  unfold gibbsDensity
  exact Matrix.PosSemidef.diagonal (fun i => gibbsWeight_nonneg H β i)

theorem gibbsDensity_trace_one
    (H : Fin n → ℝ) (β : ℝ) :
    Matrix.trace (gibbsDensity H β) = 1 := by
  unfold gibbsDensity
  rw [Matrix.trace]
  simpa using gibbsWeight_sum_one H β

end InfoGeometry.Thermo.FiniteDiagonal
