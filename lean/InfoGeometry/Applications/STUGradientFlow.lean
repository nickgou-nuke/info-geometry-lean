/-
InfoGeometry/Applications/STUGradientFlow.lean

Operator-level STU gradient-flow readouts.

The authoritative definitions are owned by `STUOperatorBridge`: the tangent
space is the operator algebra, regularity is the non-vanishing operator
quartic invariant, and boundary surgery is expressed by Drazin projectors.
This module contains only direct theorem readouts from that owner.
-/

import InfoGeometry.Application.STUOperatorBridge
import InfoGeometry.Algebra.FiniteSpinAlgebra

noncomputable section

namespace InfoGeometry.Applications.STUGradientFlow

open InfoGeometry.Application.STUOperator

section Hilbert

variable {E : Type*}
variable [NormedAddCommGroup E] [InnerProductSpace ℝ E]

theorem operator_fisher_gradient_spec
    (I : OperatorQuarticInvariant (E := E))
    (F : OperatorFisherMetric I)
    (ρ : E →L[ℝ] E)
    (hρ : IsRegularOperator I ρ)
    (δ : E →L[ℝ] E) :
    F.metric ρ (F.gradient ρ) δ = F.dPotential ρ δ :=
  F.gradient_spec ρ hρ δ

theorem operator_gradient_flow_vector_field
    (I : OperatorQuarticInvariant (E := E))
    (F : OperatorGradientFlow I)
    (ρ : E →L[ℝ] E)
    (hρ : IsRegularOperator I ρ) :
    F.vectorField ρ = -F.fisher.gradient ρ :=
  F.vectorField_eq_negative_gradient ρ hρ

theorem operator_drazin_core_projector_idempotent
    {A D : E →L[ℝ] E}
    (hD : IsDrazinInverse A D) :
    drazinCoreProjector A D * drazinCoreProjector A D =
      drazinCoreProjector A D :=
  drazinCoreProjector_idempotent hD

theorem operator_drazin_nil_projector_idempotent
    {A D : E →L[ℝ] E}
    (hD : IsDrazinInverse A D) :
    drazinNilProjector A D * drazinNilProjector A D =
      drazinNilProjector A D :=
  drazinNilProjector_idempotent hD

theorem operator_drazin_core_nil_orthogonal
    {A D : E →L[ℝ] E}
    (hD : IsDrazinInverse A D) :
    drazinCoreProjector A D * drazinNilProjector A D = 0 :=
  drazinCore_mul_nil hD

theorem operator_drazin_nil_core_orthogonal
    {A D : E →L[ℝ] E}
    (hD : IsDrazinInverse A D) :
    drazinNilProjector A D * drazinCoreProjector A D = 0 :=
  drazinNil_mul_core hD

end Hilbert

end InfoGeometry.Applications.STUGradientFlow
