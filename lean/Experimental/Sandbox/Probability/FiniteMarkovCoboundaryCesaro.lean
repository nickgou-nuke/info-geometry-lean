import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Topology.Order.Basic
import Experimental.Sandbox.Probability.FiniteMarkovCesaroPrerequisites

/-!
# Cesàro decay for bounded finite Markov coboundaries

For a finite row-stochastic matrix `P`, the Cesàro averages of the iterates
`P^k ((1 - P) u)` tend coordinatewise to zero whenever `u` is bounded.
The proof uses the finite telescoping identity and the uniform endpoint bound;
it does not assert convergence of the ordinary powers of `P`.
-/

namespace InfoGeometry.Experimental.Probability.FiniteMarkovCesaro

open Filter
open scoped Topology

/-- The coordinatewise Cesàro average through time `N` of the orbit of the
coboundary `(1 - P) u`. The denominator is the number `N + 1` of terms. -/
noncomputable def coboundaryCesaroAverage {n : ℕ}
    (P : Matrix (Fin n) (Fin n) ℝ) (u : Fin n → ℝ) (N : ℕ) (i : Fin n) : ℝ :=
  (∑ k ∈ Finset.range (N + 1),
    (P ^ k).mulVec ((1 - P).mulVec u) i) / (N + 1 : ℝ)

/-- For bounded input, the Cesàro averages of a finite Markov coboundary
converge to zero at each coordinate. -/
theorem tendsto_coboundaryCesaroAverage_zero {n : ℕ}
    (P : Matrix (Fin n) (Fin n) ℝ)
    (hP : P ∈ Matrix.rowStochastic ℝ (Fin n))
    (u : Fin n → ℝ) (M : ℝ)
    (hu : ∀ j, |u j| ≤ M) (i : Fin n) :
    Tendsto (fun N => coboundaryCesaroAverage P u N i) atTop (𝓝 0) := by
  have hdenom_pos (N : ℕ) : (0 : ℝ) < (N + 1 : ℝ) := by positivity
  have hmajorant :
      Tendsto (fun N : ℕ => (2 * M) * (1 / (N + 1 : ℝ))) atTop (𝓝 0) := by
    simpa [mul_zero] using
      (tendsto_const_nhds (x := 2 * M)).mul
        tendsto_one_div_add_atTop_nhds_zero_nat
  apply squeeze_zero_norm _ hmajorant
  intro N
  rw [Real.norm_eq_abs, coboundaryCesaroAverage, abs_div]
  have htelescope :=
    telescoping_one_sub_matrix_mulVec P u N
  have hsum_eq :
      (∑ k ∈ Finset.range (N + 1),
        (P ^ k).mulVec ((1 - P).mulVec u) i) =
        (u - (P ^ (N + 1)).mulVec u) i := by
    simpa only [Finset.sum_apply] using
      congrArg (fun v : Fin n → ℝ => v i) htelescope
  rw [hsum_eq]
  rw [abs_of_pos (hdenom_pos N)]
  calc
    |(u - (P ^ (N + 1)).mulVec u) i| / (N + 1 : ℝ)
        ≤ (2 * M) / (N + 1 : ℝ) :=
          div_le_div_of_nonneg_right
            (endpoint_error_le_two_mul_bound P hP u M hu N i)
            (le_of_lt (hdenom_pos N))
    _ = (2 * M) * (1 / (N + 1 : ℝ)) := by ring

end InfoGeometry.Experimental.Probability.FiniteMarkovCesaro
