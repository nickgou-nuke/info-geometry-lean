import Mathlib.Tactic
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Krein.DoubledSpace

namespace InfoGeometry.Canonical.HestenesKreinDiracAnomalyCapstone

open InfoGeometry.Krein

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

structure DiracAnomalyFunctional (E : Type*) [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [CompleteSpace E] where
  anomaly : (DoubledSpace E →L[ℝ] DoubledSpace E) → ℝ
  anomaly_neg : ∀ D, anomaly (-D) = -anomaly D

theorem doubled_krein_anomaly_cancellation
    (A : DiracAnomalyFunctional E)
    (D : DoubledSpace E →L[ℝ] DoubledSpace E)
    (hD : D.comp (particleHoleC (E := E)) =
      -((particleHoleC (E := E)).comp D)) :
    A.anomaly D + A.anomaly (((particleHoleC (E := E)).comp D).comp
      (particleHoleC (E := E))) = 0 := by
  have h_conj := particleHole_conjugation_neg (E := E) D hD
  rw [h_conj, A.anomaly_neg, add_neg_cancel]

theorem hestenes_krein_dirac_anomaly_canonical_capstone
    (A : DiracAnomalyFunctional E)
    (D : DoubledSpace E →L[ℝ] DoubledSpace E)
    (hD : D.comp (particleHoleC (E := E)) =
      -((particleHoleC (E := E)).comp D)) :
    ((particleHoleC (E := E)).comp particleHoleC =
      ContinuousLinearMap.id ℝ (DoubledSpace E)) ∧
    ((chiralParity (E := E)).comp chiralParity =
      ContinuousLinearMap.id ℝ (DoubledSpace E)) ∧
    ((particleHoleC (E := E)).comp chiralParity =
      -(chiralParity.comp particleHoleC)) ∧
    (A.anomaly D + A.anomaly (((particleHoleC (E := E)).comp D).comp
      (particleHoleC (E := E))) = 0) := by
  exact ⟨particleHoleC_comp_self, chiralParity_comp_self,
    particleHoleC_chiralParity_anticommute,
    doubled_krein_anomaly_cancellation A D hD⟩

end InfoGeometry.Canonical.HestenesKreinDiracAnomalyCapstone
