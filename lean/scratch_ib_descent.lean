import InfoGeometry.Canonical.IBCore
import InfoGeometry.EntropicInference

namespace InfoGeometry.Canonical.IB.Sandbox

variable {X Y T : Type} [Fintype X] [Fintype Y] [Fintype T]
variable [DecidableEq X] [DecidableEq Y] [DecidableEq T]
variable [MeasurableSpace X] [MeasurableSingletonClass X]
variable [MeasurableSpace Y] [MeasurableSingletonClass Y]
variable [MeasurableSpace T] [MeasurableSingletonClass T]

open scoped BigOperators ENNReal NNReal
open InfoGeometry.EntropicInference

/-- 
Lemma: Mutual Information expansion.
-/
theorem mutualInformation_eq_average_kl
    (prob : IBProblem (X := X) (Y := Y))
    (pT_givenX : X → FinProb T)
    (hpos_p : ∀ x t, 0 < (pT_givenX x t).toReal)
    (hpos_x : ∀ x, 0 < (marginal_x prob x).toReal) :
    let pXT := jointXT prob pT_givenX
    let qT := inducedMarginalT prob pT_givenX
    mutualInformation pXT = ∑ x : X, (marginal_x prob x).toReal * (InfoGeometry.fin_kl_div (pT_givenX x) qT).toReal := by
  unfold mutualInformation
  let pXT := jointXT prob pT_givenX
  let pX := marginal_x prob
  let qT := inducedMarginalT prob pT_givenX
  let qXT := independentCoupling pX qT
  
  -- Use kl_chain_rule_toReal_strict
  -- We need to show marginals match and conditional of qXT is qT.
  have hpos_xt : ∀ x t, 0 < (pXT (x, t)).toReal := by
    intro x t
    unfold jointXT
    simp [hpos_x, hpos_p]
  
  have hpos_qxt : ∀ x t, 0 < (qXT (x, t)).toReal := by
    intro x t
    unfold independentCoupling
    simp [hpos_x]
    unfold inducedMarginalT
    -- Need support of qT to be full
    sorry

  -- This is becoming complex. Let's use a more direct approach for finite sums.
  sorry

end InfoGeometry.Canonical.IB.Sandbox
