import InfoGeometry.Krein.KreinModularBilinearReadout
import InfoGeometry.Algebra.FiniteSpinAlgebra

namespace InfoGeometry.Krein

open KreinSpace

variable {H : Type*}
variable [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
variable [KreinSpace H]

/-- A property that a modular flow is compatible with the native Cartan
involution `ε` of an involutive self-dual carrier. -/
structure ModularCartanCompatibility
    (X : InvolutiveSelfDualCarrier)
    (G : KreinSkewGenerator (H := X.H)) where
  flow_commutes_epsilon :
    ∀ t, (G.modularFlow.flow t).comp X.ε = X.ε.comp (G.modularFlow.flow t)

theorem flow_commutes_Pplus
    (X : InvolutiveSelfDualCarrier)
    (G : KreinSkewGenerator (H := X.H))
    (C : ModularCartanCompatibility X G) (t : ℝ) :
    X.Pplus.comp (G.modularFlow.flow t) =
      (G.modularFlow.flow t).comp X.Pplus := by
  unfold InvolutiveSelfDualCarrier.Pplus
  rw [ContinuousLinearMap.smul_comp, ContinuousLinearMap.comp_smul,
    ContinuousLinearMap.add_comp, ContinuousLinearMap.comp_add,
    ContinuousLinearMap.id_comp, ContinuousLinearMap.comp_id,
    C.flow_commutes_epsilon]

theorem flow_commutes_Pminus
    (X : InvolutiveSelfDualCarrier)
    (G : KreinSkewGenerator (H := X.H))
    (C : ModularCartanCompatibility X G) (t : ℝ) :
    X.Pminus.comp (G.modularFlow.flow t) =
      (G.modularFlow.flow t).comp X.Pminus := by
  unfold InvolutiveSelfDualCarrier.Pminus
  rw [ContinuousLinearMap.smul_comp, ContinuousLinearMap.comp_smul,
    ContinuousLinearMap.sub_comp, ContinuousLinearMap.comp_sub,
    ContinuousLinearMap.id_comp, ContinuousLinearMap.comp_id,
    C.flow_commutes_epsilon]

theorem modularFlow_preserves_Pplus
    (X : InvolutiveSelfDualCarrier)
    (G : KreinSkewGenerator (H := X.H))
    (C : ModularCartanCompatibility X G) (t : ℝ) (u : X.H) :
    G.modularFlow.flow t (X.Pplus u) =
      X.Pplus (G.modularFlow.flow t u) := by
  exact congrArg (fun T : X.H →L[ℝ] X.H => T u)
    (flow_commutes_Pplus X G C t) |>.symm

theorem modularFlow_preserves_Pminus
    (X : InvolutiveSelfDualCarrier)
    (G : KreinSkewGenerator (H := X.H))
    (C : ModularCartanCompatibility X G) (t : ℝ) (u : X.H) :
    G.modularFlow.flow t (X.Pminus u) =
      X.Pminus (G.modularFlow.flow t u) := by
  exact congrArg (fun T : X.H →L[ℝ] X.H => T u)
    (flow_commutes_Pminus X G C t) |>.symm

end InfoGeometry.Krein
