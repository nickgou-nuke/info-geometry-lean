import InfoGeometry.Analysis.LogOddsSimplexGeometry
import Mathlib.Analysis.Convex.Deriv

noncomputable section

namespace InfoGeometry.Detector.AmariLegendreCore

open InfoGeometry.Canonical.AmariBinarySimplexBridge
open InfoGeometry.Analysis.LogOddsSimplexGeometry
open InfoGeometry.Prequantum.JaynesKLPotential
open scoped Topology

theorem hasDerivAt_massieu (parameter : ℝ) :
    HasDerivAt massieu (logistic parameter) parameter := by
  simpa [massieu, logistic] using
    ((Real.hasDerivAt_exp parameter).const_add 1).log
      (by positivity : 1 + Real.exp parameter ≠ 0)

theorem hasDerivAt_dual_gradient {probability : ℝ}
    (interior : probability ∈ Set.Ioo (0 : ℝ) 1) :
    HasDerivAt (deriv negativeEntropy) (fisherMix probability) probability := by
  apply (hasDerivAt_logit interior).congr_of_eventuallyEq
  filter_upwards [Ioo_mem_nhds interior.1 interior.2] with value value_interior
  exact deriv_negativeEntropy value_interior

theorem inverse_hessians {probability : ℝ}
    (interior : probability ∈ Set.Ioo (0 : ℝ) 1) :
    deriv (deriv negativeEntropy) probability *
      deriv (deriv massieu) (logit probability) = 1 := by
  rw [(hasDerivAt_dual_gradient interior).deriv, deriv2_massieu]
  exact fisherMix_mul_fisherExp_logit interior

theorem massieu_strictConvex : StrictConvexOn ℝ Set.univ massieu := by
  apply strictConvexOn_of_deriv2_pos' (convex_univ : Convex ℝ (Set.univ : Set ℝ))
  · intro parameter _
    exact (hasDerivAt_massieu parameter).continuousAt.continuousWithinAt
  · intro parameter _
    change 0 < deriv (deriv massieu) parameter
    rw [deriv2_massieu]
    exact fisherExp_pos parameter

theorem negativeEntropy_strictConvex :
    StrictConvexOn ℝ (Set.Ioo (0 : ℝ) 1) negativeEntropy := by
  apply strictConvexOn_of_deriv2_pos' (convex_Ioo (0 : ℝ) 1)
  · intro probability interior
    exact (hasDerivAt_negativeEntropy interior).continuousAt.continuousWithinAt
  · intro probability interior
    change 0 < deriv (deriv negativeEntropy) probability
    rw [(hasDerivAt_dual_gradient interior).deriv]
    exact fisherMix_pos interior

theorem log_logistic (parameter : ℝ) :
    Real.log (logistic parameter) = parameter - massieu parameter := by
  unfold logistic massieu
  rw [Real.log_div (Real.exp_ne_zero _) (by positivity), Real.log_exp]

theorem log_complement_logistic (parameter : ℝ) :
    Real.log (1 - logistic parameter) = -massieu parameter := by
  have complement : 1 - logistic parameter = (1 + Real.exp parameter)⁻¹ := by
    unfold logistic
    field_simp
    ring
  rw [complement, Real.log_inv]
  rfl

theorem fenchel_gap_eq_binary_kl (parameter probability : ℝ)
    (interior : probability ∈ Set.Ioo (0 : ℝ) 1) :
    fenchelGap parameter probability =
      scalarKLDivergence probability (logistic parameter) +
      scalarKLDivergence (1 - probability) (1 - logistic parameter) := by
  unfold scalarKLDivergence
  rw [Real.log_div interior.1.ne' (logistic_pos parameter).ne',
    Real.log_div (sub_pos.mpr interior.2).ne' (one_sub_logistic_pos parameter).ne',
    log_logistic, log_complement_logistic]
  unfold fenchelGap negativeEntropy
  ring

theorem fenchel_gap_nonnegative (parameter probability : ℝ)
    (interior : probability ∈ Set.Ioo (0 : ℝ) 1) :
    0 ≤ fenchelGap parameter probability := by
  rw [fenchel_gap_eq_binary_kl parameter probability interior]
  exact add_nonneg
    (scalarKLDivergence_nonneg _ _ interior.1 (logistic_pos parameter))
    (scalarKLDivergence_nonneg _ _ (sub_pos.mpr interior.2)
      (one_sub_logistic_pos parameter))

theorem legendre_isGreatest {probability : ℝ}
    (interior : probability ∈ Set.Ioo (0 : ℝ) 1) :
    IsGreatest (Set.range (fun parameter => parameter * probability - massieu parameter))
      (negativeEntropy probability) := by
  constructor
  · refine ⟨logit probability, ?_⟩
    have contact := fenchelGap_contact (logit probability)
    rw [logistic_logit interior] at contact
    unfold fenchelGap at contact
    linarith
  · rintro value ⟨parameter, rfl⟩
    have bound := fenchel_gap_nonnegative parameter probability interior
    unfold fenchelGap at bound
    linarith

theorem fisher_eq_expected_squared_score (parameter : ℝ) :
    logistic parameter * (deriv (fun value => Real.log (logistic value)) parameter) ^ 2 +
      (1 - logistic parameter) *
        (deriv (fun value => Real.log (1 - logistic value)) parameter) ^ 2 =
      deriv (deriv massieu) parameter := by
  have success := (hasDerivAt_logistic parameter).log (logistic_pos parameter).ne'
  have failure := ((hasDerivAt_const parameter (1 : ℝ)).sub
    (hasDerivAt_logistic parameter)).log (one_sub_logistic_pos parameter).ne'
  simp only [Pi.sub_apply] at failure
  rw [success.deriv, failure.deriv, deriv2_massieu]
  unfold fisherExp
  field_simp [(logistic_pos parameter).ne', (one_sub_logistic_pos parameter).ne']
  ring

end InfoGeometry.Detector.AmariLegendreCore
