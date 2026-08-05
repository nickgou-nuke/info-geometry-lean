import InfoGeometry.OperatorAlgebra.HorizonKMS
import InfoGeometry.Physics.Algebra.TopologicalBraidMonodromyOperator
import InfoGeometry.Physics.Thermodynamics.TopologicalMonodromyKMSBridge

/-!
# Logarithmic CFT KMS modular triple

This file packages the existing square-zero monodromy lane as a KMS readout
triple.  It reuses the bounded unipotent monodromy readout already proved in
`TopologicalMonodromyKMSBridge`; it does not assert an analytic strip theorem
or a full Tomita--Takesaki modular identification.
-/

namespace InfoGeometry.Physics.Thermodynamics

open ContinuousLinearMap
open InfoGeometry.OperatorAlgebra.HorizonKMS
open InfoGeometry.Physics.Thermodynamics.TopologicalMonodromyKMSBridge

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H]

local notation "EndH" => H →L[ℝ] H

local instance : AddCommGroup EndH := inferInstance
local instance : Module ℝ EndH := inferInstance
noncomputable local instance : NormedRing EndH := inferInstance
noncomputable local instance : NormedAlgebra ℝ EndH := inferInstance
local instance : IsTopologicalRing EndH := inferInstance
local instance : SMulCommClass ℝ EndH EndH := inferInstance
local instance : IsScalarTower ℝ EndH EndH := inferInstance

/-- A thin KMS packaging of the logarithmic monodromy lane. -/
structure LogCFTKMSModularTriple where
  monodromy : InfoGeometry.Physics.Algebra.ContinuousMonodromyOperator H
  readout : KMSReadoutDatum (H →L[ℝ] H)

/-- The canonical packaging built from the existing unipotent monodromy readout. -/
def logCFTKMSCanonical
    (M : InfoGeometry.Physics.Algebra.ContinuousMonodromyOperator H) :
    LogCFTKMSModularTriple (H := H) where
  monodromy := M
  readout := unipotentMonodromyReadoutDatum M

@[simp] theorem canonical_readout
    (M : InfoGeometry.Physics.Algebra.ContinuousMonodromyOperator H) :
    (logCFTKMSCanonical (H := H) M).readout =
      unipotentMonodromyReadoutDatum M :=
  rfl

theorem logCFTKMS_beta_pos (T : LogCFTKMSModularTriple (H := H)) :
    0 < T.readout.beta :=
  T.readout.beta_pos

theorem logCFTKMS_flow_zero (T : LogCFTKMSModularTriple (H := H)) :
    ∀ X : H →L[ℝ] H, T.readout.flow 0 X = X :=
  T.readout.flow_zero

theorem logCFTKMS_flow_add (T : LogCFTKMSModularTriple (H := H)) :
    ∀ s t : ℝ, ∀ X : H →L[ℝ] H,
      T.readout.flow (s + t) X = T.readout.flow s (T.readout.flow t X) :=
  T.readout.flow_add

theorem logCFTKMS_flow_invariant (T : LogCFTKMSModularTriple (H := H)) :
    ∀ t : ℝ, ∀ X : H →L[ℝ] H,
      T.readout.state (T.readout.flow t X) = T.readout.state X :=
  T.readout.flow_invariant

/--
The canonical logarithmic CFT KMS readout flow is continuous as a map on the
product of time and bounded operators.
-/
theorem logCFTKMSCanonical_flow_continuous
    (M : InfoGeometry.Physics.Algebra.ContinuousMonodromyOperator H) :
    Continuous (fun p : ℝ × (H →L[ℝ] H) =>
      (logCFTKMSCanonical (H := H) M).readout.flow p.1 p.2) := by
  have hflow :
      Continuous (fun p : ℝ × (H →L[ℝ] H) =>
        InfoGeometry.Physics.Algebra.continuousUnipotentFlow M p.1) :=
    (InfoGeometry.Physics.Algebra.continuous_continuousUnipotentFlow
      (M := M)).comp continuous_fst
  simpa [logCFTKMSCanonical,
    TopologicalMonodromyKMSBridge.unipotentMonodromyReadoutDatum] using
      hflow.mul continuous_snd

/--
The canonical logarithmic CFT KMS readout flow is a continuous linear
equivalence on the bounded-operator carrier, with inverse at `-t`.
-/
noncomputable def logCFTKMSCanonical_flowEquiv
    (M : InfoGeometry.Physics.Algebra.ContinuousMonodromyOperator H)
    (t : ℝ) :
    EndH ≃L[ℝ] EndH := by
  let e : EndH ≃ₗ[ℝ] EndH :=
    { toLinearMap :=
        ContinuousLinearMap.mul ℝ EndH
          (InfoGeometry.Physics.Algebra.continuousUnipotentFlow M t)
      invFun :=
        ContinuousLinearMap.mul ℝ EndH
          (InfoGeometry.Physics.Algebra.continuousUnipotentFlow M (-t))
      left_inv := by
        intro T
        ext x
        change ((InfoGeometry.Physics.Algebra.continuousUnipotentFlow M (-t) *
            InfoGeometry.Physics.Algebra.continuousUnipotentFlow M t) * T) x = T x
        rw [InfoGeometry.Physics.Algebra.continuousUnipotentFlow_neg_mul (M := M) t]
        simp [ContinuousLinearMap.mul_apply]
      right_inv := by
        intro T
        ext x
        change ((InfoGeometry.Physics.Algebra.continuousUnipotentFlow M t *
            InfoGeometry.Physics.Algebra.continuousUnipotentFlow M (-t)) * T) x = T x
        rw [InfoGeometry.Physics.Algebra.continuousUnipotentFlow_mul_neg (M := M) t]
        simp [ContinuousLinearMap.mul_apply] }
  exact ContinuousLinearEquiv.mk e
    (ContinuousLinearMap.mul ℝ EndH
      (InfoGeometry.Physics.Algebra.continuousUnipotentFlow M t)).continuous
    (ContinuousLinearMap.mul ℝ EndH
      (InfoGeometry.Physics.Algebra.continuousUnipotentFlow M (-t))).continuous

@[simp] theorem logCFTKMSCanonical_flowEquiv_symm_apply_apply
    (M : InfoGeometry.Physics.Algebra.ContinuousMonodromyOperator H)
    (t : ℝ) (T : EndH) :
    (logCFTKMSCanonical_flowEquiv (H := H) M t).symm
        ((logCFTKMSCanonical (H := H) M).readout.flow t T) = T := by
  simpa [logCFTKMSCanonical_flowEquiv, logCFTKMSCanonical] using
    (ContinuousLinearEquiv.symm_apply_apply
      (logCFTKMSCanonical_flowEquiv (H := H) M t) T)

end

end InfoGeometry.Physics.Thermodynamics
