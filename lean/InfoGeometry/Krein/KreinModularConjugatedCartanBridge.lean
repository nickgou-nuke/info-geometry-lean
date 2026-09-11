import InfoGeometry.Krein.KreinModularConjugatedOperatorBridge
import InfoGeometry.Algebra.FiniteSpinAlgebra

namespace InfoGeometry.Krein

open KreinSpace

variable {H : Type*}
variable [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
variable [KreinSpace H]

local notation "EndH" => H →L[ℝ] H

theorem modularConjugatedOperator_fixes_Pplus
    (X : InvolutiveSelfDualCarrier)
    (G : KreinSkewGenerator (H := X.H))
    (C : ModularCartanCompatibility X G) (t : ℝ) :
    modularConjugatedOperator G t X.Pplus = X.Pplus := by
  unfold modularConjugatedOperator
  have hP := flow_commutes_Pplus X G C (-t)
  have hInv :
      (G.modularFlow.flow t).comp (G.modularFlow.flow (-t)) =
        ContinuousLinearMap.id ℝ X.H := by
    change G.modularFlow.flow t * G.modularFlow.flow (-t) =
      ContinuousLinearMap.id ℝ X.H
    calc
      G.modularFlow.flow t * G.modularFlow.flow (-t) =
          G.modularFlow.flow (t + (-t)) := (G.flow_add t (-t)).symm
      _ = 1 := by rw [add_neg_cancel, G.flow_zero]
      _ = ContinuousLinearMap.id ℝ X.H := by rfl
  ext u
  change G.modularFlow.flow t
      (X.Pplus (G.modularFlow.flow (-t) u)) = X.Pplus u
  have hpoint :
      X.Pplus (G.modularFlow.flow (-t) u) =
        G.modularFlow.flow (-t) (X.Pplus u) :=
    congrArg (fun T : X.H →L[ℝ] X.H => T u) hP
  calc
    G.modularFlow.flow t
        (X.Pplus (G.modularFlow.flow (-t) u)) =
      G.modularFlow.flow t
        (G.modularFlow.flow (-t) (X.Pplus u)) := by
          rw [hpoint]
    _ = X.Pplus u := by
      have h := congrArg (fun T : X.H →L[ℝ] X.H => T (X.Pplus u)) hInv
      simpa [ContinuousLinearMap.comp_apply] using h

theorem modularConjugatedOperator_fixes_Pminus
    (X : InvolutiveSelfDualCarrier)
    (G : KreinSkewGenerator (H := X.H))
    (C : ModularCartanCompatibility X G) (t : ℝ) :
    modularConjugatedOperator G t X.Pminus = X.Pminus := by
  unfold modularConjugatedOperator
  have hP := flow_commutes_Pminus X G C (-t)
  have hInv :
      (G.modularFlow.flow t).comp (G.modularFlow.flow (-t)) =
        ContinuousLinearMap.id ℝ X.H := by
    change G.modularFlow.flow t * G.modularFlow.flow (-t) =
      ContinuousLinearMap.id ℝ X.H
    calc
      G.modularFlow.flow t * G.modularFlow.flow (-t) =
          G.modularFlow.flow (t + (-t)) := (G.flow_add t (-t)).symm
      _ = 1 := by rw [add_neg_cancel, G.flow_zero]
      _ = ContinuousLinearMap.id ℝ X.H := by rfl
  ext u
  change G.modularFlow.flow t
      (X.Pminus (G.modularFlow.flow (-t) u)) = X.Pminus u
  have hpoint :
      X.Pminus (G.modularFlow.flow (-t) u) =
        G.modularFlow.flow (-t) (X.Pminus u) :=
    congrArg (fun T : X.H →L[ℝ] X.H => T u) hP
  calc
    G.modularFlow.flow t
        (X.Pminus (G.modularFlow.flow (-t) u)) =
      G.modularFlow.flow t
        (G.modularFlow.flow (-t) (X.Pminus u)) := by
          rw [hpoint]
    _ = X.Pminus u := by
      have h := congrArg (fun T : X.H →L[ℝ] X.H => T (X.Pminus u)) hInv
      simpa [ContinuousLinearMap.comp_apply] using h

end InfoGeometry.Krein
