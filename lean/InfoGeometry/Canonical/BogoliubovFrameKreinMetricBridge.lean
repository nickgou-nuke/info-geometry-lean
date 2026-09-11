import InfoGeometry.Canonical.BogoliubovVielbein
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Canonical.SemilinearFunctionalAnalysisOwners

/-!
# Transported Krein metric

The metric induced by a transported frame is a pullback in the associative
endomorphism algebra.  This owner keeps the frame transport and the
split-octonion representation separate: no representation datum is inferred.
-/

noncomputable section

namespace InfoGeometry.Canonical

open BogoliubovVielbein
open InfoGeometry.Krein

variable {E : Type}
variable [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

local notation "H₂" => DoubledSpace E
local notation "EndH" => H₂ →L[ℝ] H₂

/-- Pullback of an endomorphism-valued pairing by a frame `U`. -/
def pullbackMetric (U G : EndH) : EndH :=
  (ContinuousLinearMap.adjoint U).comp (G.comp U)

@[simp] theorem pullbackMetric_apply (U G : EndH) (x : H₂) :
    pullbackMetric U G x =
      ContinuousLinearMap.adjoint U (G (U x)) := rfl

theorem pullbackMetric_selfadjoint
    (U G : EndH)
    (hG : ContinuousLinearMap.adjoint G = G) :
    ContinuousLinearMap.adjoint (pullbackMetric U G) =
      pullbackMetric U G := by
  unfold pullbackMetric
  rw [SemilinearFunctionalAnalysisOwners.adjoint_comp_reverse,
    SemilinearFunctionalAnalysisOwners.adjoint_comp_reverse,
    ContinuousLinearMap.adjoint_adjoint, hG]
  rfl

/-- The metric induced by the existing Bogoliubov local frame. -/
def transportedKreinMetric
    (V : BogoliubovVielbeinBundle (E := E)) (G₀ : EndH) (t : ℝ) : EndH :=
  pullbackMetric (V.localFrame t) G₀

theorem transportedKreinMetric_eq
    (V : BogoliubovVielbeinBundle (E := E)) (G₀ : EndH) (t : ℝ) :
    transportedKreinMetric V G₀ t =
      (ContinuousLinearMap.adjoint (V.localFrame t)).comp
        (G₀.comp (V.localFrame t)) := rfl

theorem transportedKreinMetric_selfadjoint
    (V : BogoliubovVielbeinBundle (E := E)) (G₀ : EndH) (t : ℝ)
    (hG : ContinuousLinearMap.adjoint G₀ = G₀) :
    ContinuousLinearMap.adjoint (transportedKreinMetric V G₀ t) =
      transportedKreinMetric V G₀ t :=
  pullbackMetric_selfadjoint (V.localFrame t) G₀ hG

end InfoGeometry.Canonical
