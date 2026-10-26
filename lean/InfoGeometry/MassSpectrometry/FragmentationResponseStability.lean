import InfoGeometry.MassSpectrometry.FragmentationOccupancyBounds
import InfoGeometry.MassSpectrometry.NumericalEvidenceBounds
import Mathlib.Analysis.Matrix.Normed

/-!
# Quantitative stability of finite fragmentation response

The matrix norm is explicitly Mathlib's maximum-absolute-row-sum operator norm;
the vector norm is the native finite-product supremum norm. No global norm
instance is installed. The exact resolvent identity gives a constructive error
certificate on a bounded reward domain. Both kernels must retain strict DAG
support; no empirical residual is promoted to a uniform error bound.
-/

noncomputable section
namespace InfoGeometry.MassSpectrometry
open scoped BigOperators Matrix Matrix.Norms.Operator
open InfoGeometry.Algebra.RankedMatrixPowers
open InfoGeometry.SignedNetwork.RankedDAGResolvent

namespace FiniteGreenResponse

/-- A nonnegative row-mass bound controls the native infinity operator norm. -/
theorem norm_le_of_nonneg_row_sum
    {ι : Type*} [Fintype ι] (K : Matrix ι ι ℝ) (C : ℝ) (hC : 0 ≤ C)
    (hpos : ∀ i j, 0 ≤ K i j) (hrow : ∀ i, ∑ j, K i j ≤ C) : ‖K‖ ≤ C := by
  have h : (Finset.univ.sup fun i => ∑ j, ‖K i j‖₊) ≤ (⟨C, hC⟩ : NNReal) := by
    apply Finset.sup_le
    intro i _
    apply NNReal.coe_le_coe.mp
    calc
      ((∑ j, ‖K i j‖₊ : NNReal) : ℝ) = ∑ j, K i j := by
        simp only [NNReal.coe_sum, coe_nnnorm]
        exact Finset.sum_congr rfl (fun j _ => Real.norm_of_nonneg (hpos i j))
      _ ≤ C := hrow i
  rw [Matrix.linfty_opNorm_def]
  exact_mod_cast h

end FiniteGreenResponse

namespace StochasticGrammar
variable {n : ℕ} {D E : FragmentationDAG n}

theorem transient_norm_le_one (G : StochasticGrammar D) : ‖G.transientMatrix‖ ≤ 1 :=
  FiniteGreenResponse.norm_le_of_nonneg_row_sum _ 1 (by norm_num)
    G.weight_nonneg G.row_sum_le_one

theorem fundamentalMatrix_norm_le (G : StochasticGrammar D) :
    ‖G.fundamentalMatrix‖ ≤ (rankHorizon D.rank : ℝ) :=
  FiniteGreenResponse.norm_le_of_nonneg_row_sum _ _ (Nat.cast_nonneg _)
    (G.finiteGreen_nonneg _) (G.finiteGreen_row_sum_le _)

/-- The kernels may belong to different ranked DAGs on the same coordinate set. -/
theorem fundamentalMatrix_difference (G : StochasticGrammar D) (H : StochasticGrammar E) :
    G.fundamentalMatrix - H.fundamentalMatrix =
      G.fundamentalMatrix * (G.transientMatrix - H.transientMatrix) * H.fundamentalMatrix :=
  FiniteGreenResponse.resolvent_identity _ _ _ _
    G.transient_pow_rankHorizon_eq_zero H.transient_pow_rankHorizon_eq_zero

theorem fundamentalMatrix_difference_norm_le
    (G : StochasticGrammar D) (H : StochasticGrammar E) :
    ‖G.fundamentalMatrix - H.fundamentalMatrix‖ ≤
      (rankHorizon D.rank : ℝ) * (rankHorizon E.rank : ℝ) *
        ‖G.transientMatrix - H.transientMatrix‖ := by
  rw [G.fundamentalMatrix_difference H]
  calc
    ‖G.fundamentalMatrix * (G.transientMatrix - H.transientMatrix) * H.fundamentalMatrix‖ ≤
        (‖G.fundamentalMatrix‖ * ‖G.transientMatrix - H.transientMatrix‖) *
          ‖H.fundamentalMatrix‖ :=
      (norm_mul_le _ _).trans (mul_le_mul_of_nonneg_right (norm_mul_le _ _) (norm_nonneg _))
    _ ≤ ((rankHorizon D.rank : ℝ) * ‖G.transientMatrix - H.transientMatrix‖) *
          (rankHorizon E.rank : ℝ) :=
      mul_le_mul
        (mul_le_mul_of_nonneg_right G.fundamentalMatrix_norm_le (norm_nonneg _))
        H.fundamentalMatrix_norm_le (norm_nonneg _)
        (mul_nonneg (Nat.cast_nonneg _) (norm_nonneg _))
    _ = _ := by ring

theorem response_difference_norm_le (G : StochasticGrammar D) (H : StochasticGrammar E)
    (g : Fin n → ℝ) :
    ‖G.fundamentalMatrix *ᵥ g - H.fundamentalMatrix *ᵥ g‖ ≤
      ((rankHorizon D.rank : ℝ) * (rankHorizon E.rank : ℝ) *
        ‖G.transientMatrix - H.transientMatrix‖) * ‖g‖ := by
  rw [← Matrix.sub_mulVec]
  exact (Matrix.linfty_opNorm_mulVec _ _).trans
    (mul_le_mul_of_nonneg_right (G.fundamentalMatrix_difference_norm_le H) (norm_nonneg _))

/-- Finite response amplifies a reward perturbation by at most the rank horizon. -/
theorem response_reward_error (G : StochasticGrammar D) (g h : Fin n → ℝ) :
    ‖G.fundamentalMatrix *ᵥ g - G.fundamentalMatrix *ᵥ h‖ ≤
      (rankHorizon D.rank : ℝ) * ‖g - h‖ := by
  rw [← Matrix.mulVec_sub]
  exact (Matrix.linfty_opNorm_mulVec _ _).trans
    (mul_le_mul_of_nonneg_right G.fundamentalMatrix_norm_le (norm_nonneg _))

/-- Kernel and reward errors remain distinct in the accumulated response. -/
theorem response_two_source_error (G : StochasticGrammar D) (H : StochasticGrammar E)
    (g h : Fin n → ℝ) :
    ‖G.fundamentalMatrix *ᵥ g - H.fundamentalMatrix *ᵥ h‖ ≤
      (rankHorizon D.rank : ℝ) * ‖g - h‖ +
        ((rankHorizon D.rank : ℝ) * (rankHorizon E.rank : ℝ) *
          ‖G.transientMatrix - H.transientMatrix‖) * ‖h‖ := by
  have heq : G.fundamentalMatrix *ᵥ g - H.fundamentalMatrix *ᵥ h =
      (G.fundamentalMatrix *ᵥ g - G.fundamentalMatrix *ᵥ h) +
        (G.fundamentalMatrix *ᵥ h - H.fundamentalMatrix *ᵥ h) := by abel
  rw [heq]
  exact (norm_add_le _ _).trans
    (add_le_add (G.response_reward_error g h) (G.response_difference_norm_le H h))

/-- A uniform response certificate on bounded rewards, using the existing owner. -/
def response_uniformErrorBound (G : StochasticGrammar D) (H : StochasticGrammar E)
    (δ C : NNReal) (hδ : ‖G.transientMatrix - H.transientMatrix‖ ≤ (δ : ℝ)) :
    NumericalEvidence.UniformErrorBound
      (fun g : {g : Fin n → ℝ // ‖g‖ ≤ (C : ℝ)} => G.fundamentalMatrix *ᵥ g.1)
      (fun g : {g : Fin n → ℝ // ‖g‖ ≤ (C : ℝ)} => H.fundamentalMatrix *ᵥ g.1) where
  error := (rankHorizon D.rank : NNReal) * (rankHorizon E.rank : NNReal) * δ * C
  bound g := by
    rw [dist_comm, dist_eq_norm]
    calc
      ‖G.fundamentalMatrix *ᵥ g.1 - H.fundamentalMatrix *ᵥ g.1‖ ≤
          ((rankHorizon D.rank : ℝ) * (rankHorizon E.rank : ℝ) *
            ‖G.transientMatrix - H.transientMatrix‖) * ‖g.1‖ :=
        G.response_difference_norm_le H g.1
      _ ≤ ((rankHorizon D.rank : ℝ) * (rankHorizon E.rank : ℝ) * (δ : ℝ)) * (C : ℝ) := by
        gcongr; first | exact hδ | exact g.2
      _ = _ := by simp

end StochasticGrammar
end InfoGeometry.MassSpectrometry
