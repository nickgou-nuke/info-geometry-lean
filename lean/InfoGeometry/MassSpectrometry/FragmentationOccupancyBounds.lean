import InfoGeometry.MassSpectrometry.FragmentationGreenResponse

/-!
# Rank-local bounds for finite fragmentation occupancy

These are inequalities for finite matrix sums. No probability space or
hitting-time expectation is silently introduced. The lower bound counts the
initial original state; the upper bound includes the final absorption step.
-/

noncomputable section
namespace InfoGeometry.MassSpectrometry.StochasticGrammar
open scoped BigOperators Matrix
open InfoGeometry.SignedNetwork.RankedDAGResolvent
open InfoGeometry.Algebra.RankedMatrixPowers

variable {n : ℕ} {D : FragmentationDAG n}

/-- Every truncation has a rank-local row bound, even before choosing a horizon. -/
theorem finiteGreen_row_sum_le_rank (G : StochasticGrammar D) (N : ℕ) :
    ∀ u, ∑ v, finiteGreen G.transientMatrix N u v ≤ ((D.rank u + 1 : ℕ) : ℝ) := by
  induction N with
  | zero => intro u; simp [finiteGreen]
  | succ N ih =>
      intro u
      have hstep (v : Fin n) :
          G.weight u v * (∑ j, finiteGreen G.transientMatrix N v j) ≤
            G.weight u v * (D.rank u : ℝ) := by
        by_cases hz : G.weight u v = 0
        · simp [hz]
        · have hr : ((D.rank v + 1 : ℕ) : ℝ) ≤ (D.rank u : ℝ) := by
            exact_mod_cast Nat.succ_le_of_lt (G.rank_decreases_of_weight_ne_zero hz)
          exact mul_le_mul_of_nonneg_left ((ih v).trans hr) (G.weight_nonneg u v)
      calc
        ∑ v, finiteGreen G.transientMatrix (N + 1) u v =
            1 + ∑ w, G.weight u w * (∑ v, finiteGreen G.transientMatrix N w v) := by
          rw [FiniteGreenResponse.finiteGreen_succ_left]
          simp only [Matrix.add_apply, Finset.sum_add_distrib, Matrix.mul_apply]
          rw [show (∑ v, (1 : Matrix (Fin n) (Fin n) ℝ) u v) = 1 by
            simp [Matrix.one_apply]]
          congr 1
          rw [Finset.sum_comm]
          simp only [Finset.mul_sum, transientMatrix]
        _ ≤ 1 + ∑ w, G.weight u w * (D.rank u : ℝ) :=
          add_le_add_left (Finset.sum_le_sum (fun v _ => hstep v)) 1
        _ = 1 + (∑ w, G.weight u w) * (D.rank u : ℝ) := by rw [Finset.sum_mul]
        _ ≤ 1 + 1 * (D.rank u : ℝ) :=
          add_le_add_left (mul_le_mul_of_nonneg_right (G.row_sum_le_one u)
            (Nat.cast_nonneg _)) 1
        _ = ((D.rank u + 1 : ℕ) : ℝ) := by push_cast; ring

/-- A nonempty time window includes the identity contribution. -/
theorem one_le_finiteGreen_row_sum (G : StochasticGrammar D)
    (N : ℕ) (hN : 0 < N) (u : Fin n) :
    1 ≤ ∑ v, finiteGreen G.transientMatrix N u v := by
  have hzero : (0 : ℕ) ∈ Finset.range N := by simpa using hN
  calc
    1 = ∑ v, (G.transientMatrix ^ 0) u v := by simp [Matrix.one_apply]
    _ ≤ ∑ k ∈ Finset.range N, ∑ v, (G.transientMatrix ^ k) u v :=
      Finset.single_le_sum
        (fun k _ => Finset.sum_nonneg (fun v _ => G.transient_pow_nonneg k u v)) hzero
    _ = ∑ v, finiteGreen G.transientMatrix N u v := by
      simp only [finiteGreen, Finset.sum_apply]
      exact Finset.sum_comm

theorem occupancyPotential_bounds (G : StochasticGrammar D) (u : Fin n) :
    1 ≤ G.occupancyPotential u ∧
      G.occupancyPotential u ≤ ((D.rank u + 1 : ℕ) : ℝ) := by
  have heq : G.occupancyPotential u =
      ∑ v, finiteGreen G.transientMatrix (rankHorizon D.rank) u v := by
    simp [occupancyPotential, fundamentalMatrix, Matrix.mulVec, dotProduct]
  rw [heq]
  exact ⟨G.one_le_finiteGreen_row_sum _ (by simp [rankHorizon]) u,
    G.finiteGreen_row_sum_le_rank _ u⟩

/-- Nonnegative rewards give nonnegative finite responses. -/
theorem response_nonneg (G : StochasticGrammar D) (g : Fin n → ℝ)
    (hg : ∀ u, 0 ≤ g u) (u : Fin n) : 0 ≤ (G.fundamentalMatrix *ᵥ g) u := by
  exact Finset.sum_nonneg (fun v _ => mul_nonneg
    (G.finiteGreen_nonneg _ u v) (hg v))

end InfoGeometry.MassSpectrometry.StochasticGrammar
