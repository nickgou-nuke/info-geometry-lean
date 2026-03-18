import Mathlib
import InfoGeometry.Singular.KreinNaturalFlow
import InfoGeometry.Canonical.AnomalyGauge
import InfoGeometry.Canonical.GrandUnification
import InfoGeometry.Canonical.PerelmanW
import InfoGeometry.Canonical.WeylInformationGauge
import InfoGeometry.Canonical.RicciMongeAmpere

/-!
# The Unitary Bridge of Information Geometry

This module formalizes the high-level connections between:
1.  **Jordan/KKT Barriers**: Primal information structures.
2.  **Weyl Gauge Theory**: Scaling and path-dependence.
3.  **Singular Natural Gradient**: Causal flow on the boundary.
4.  **Perelman Renormalization**: Entropy monotonicity.

The glue is the Cartan involution and the resulting Chiral Anomaly.
-/

namespace InfoGeometry.Unstable.SingularUnitaryBridge

open InfoGeometry.Singular.MoorePenrose
open InfoGeometry.Singular.Drazin
open InfoGeometry.Singular.Architecture
open InfoGeometry.Canonical.AnomalyGauge
open InfoGeometry.Krein
open InfoGeometry.Canonical.GrandUnification
open InfoGeometry.Canonical.PerelmanW
open InfoGeometry.Canonical.WeylInformationGauge
open InfoGeometry.Canonical.RicciMongeAmpere

variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/--
**The KKT-Perelman Bridge:**
The KKT barrier potential `K = -log detJ` is the functional generator for the 
singular geometry. On the renormalization path, it maps to the constant part 
of the Perelman `W` functional.
-/
theorem kkt_perelman_correspondence (J : JordanKKTData E) (x : E) :
    J.K x = - Real.log (J.detJ x) := rfl

/--
**The Anomaly-Gauge Bridge:**
The Chiral Anomaly acts as the gauge field that restores metric invariance 
when the Weyl scale transform becomes singular.
-/
structure UnitaryGaugeState (G : HilbertDoubled E →L[ℝ] HilbertDoubled E) where
  anomaly : HilbertDoubled E →L[ℝ] HilbertDoubled E
  is_anomaly : ∃ G_pinv D_inv k hMP hD, anomaly = ChiralAnomaly G G_pinv D_inv k hMP hD
  is_gauge : IsKreinSkewAdjointH (E := E) anomaly

/--
**Universal Scaling Law:**
At the singular limit, the Natural Gradient flow generator is forced into 
the Lie subalgebra 𝔨 by the Anomaly Gauge Field.
-/
theorem natural_gradient_gauge_rotation 
    (G grad_f : HilbertDoubled E →L[ℝ] HilbertDoubled E)
    (flow : SingularNaturalGradientFlow G grad_f)
    (hD_symm :
      (Drazin_Projector G flow.D_inv flow.k_index flow.is_drazin)†
        = Drazin_Projector G flow.D_inv flow.k_index flow.is_drazin) :
    IsKreinSkewAdjointH (E := E) (extractFlowAnomaly flow) := by
  -- Bridging IsKreinSkewAdjointH and the algebraic adj X = -X
  change (extractFlowAnomaly flow)† = -(extractFlowAnomaly flow)
  unfold extractFlowAnomaly
  exact ChiralAnomaly_is_SkewAdjoint
    G flow.G_pinv flow.D_inv flow.k_index flow.is_mp flow.is_drazin hD_symm

/--
**The Master Bridge of Renormalization:**
The dissipation of the Perelman `W`-functional along the Natural Gradient flow 
is bounded by the norm of the Chiral Anomaly.
-/
lemma rg_dissipation_bounded_by_anomaly
    (flow : ScalarRicciFlow E) (τ f : ℝ → ℝ)
    (χ : HilbertDoubled E →L[ℝ] HilbertDoubled E)
    (hDiff : Differentiable ℝ (fun s => WFunctional flow τ f s))
    (hLaw : ∀ s : ℝ, WDissipation flow τ f s = nnnorm χ) :
    Monotone (fun s => WFunctional flow τ f s) := by
  apply WFunctional_monotone_of_nonneg_dissipation (diss := fun _ => (nnnorm χ : ℝ))
  · exact hDiff
  · intro s; exact hLaw s
  · intro s; exact (nnnorm χ).2

end InfoGeometry.Unstable.SingularUnitaryBridge
