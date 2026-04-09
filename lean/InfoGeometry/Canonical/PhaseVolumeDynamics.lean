import InfoGeometry.Quantum.SuperchargeMultiplet
import InfoGeometry.Krein.Superphysics
import InfoGeometry.Canonical.ModularHessian

open scoped InnerProductSpace

/-!
# InfoGeometry.Canonical.PhaseVolumeDynamics

The Second Movement of the Operator Symphony: Mirror J and Phase K.
-/

namespace InfoGeometry.Canonical.PhaseVolumeDynamics

open InfoGeometry.Krein
open InfoGeometry.Quantum
open InfoGeometry.Canonical.RelationalInformationCore
open InfoGeometry.Canonical.ModularHessian

variable {E : Type 0}
variable [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

local notation "H₂" => DoubledSpace E
local notation "EndH" => H₂ →L[ℝ] H₂

/-- 
The Modular Mirror (J): The operator that connects source and sink.
In the canonical multiplet, this is the modular mirror J.
It represents the 'Mirror' that reverses the causal cone.
-/
@[rep_depth transport]
noncomputable def modularMirror 
    (_ : SuperchargeMultiplet (E := E)) : EndH :=
  modular_j (E := E)

/--
The Spectral Orientation (ε): The choice of chiral orientation.
In the canonical multiplet, this is the modular supercharge Q_J.
-/
@[rep_depth transport]
noncomputable def spectralOrientation 
    (M : SuperchargeMultiplet (E := E)) : EndH :=
  M.modular.Q

/--
The Phase-Volume Axis (K = Jε): The dynamic flow generator.
This is the 'time note' that turns the static geometry into flow.
It generates the phase of the informational wave function.
-/
@[rep_depth transport]
noncomputable def phaseVolumeAxis 
    (_ : SuperchargeMultiplet (E := E)) : EndH :=
  complex_i (E := E)

/--
Dynamic Rotation:
The Phase-Volume Axis K acts on the Modular Hessian to generate the 
informational flow. This is the 'Second Movement' where the static 
Fisher metric is rotated into the antisymmetric Vortex curvature.
-/
@[rep_depth transport]
def IsDynamicRotation
    (M : SuperchargeMultiplet (E := E)) (R : RelationalInformationDatum (E := E)) : Prop :=
  -- The flow is stationary when the Hessian is invariant under K-rotation.
  -- This links the static 'weight' (Fisher) to the dynamic 'vortex'.
  ∀ (X Y : PerturbationChannel E),
    (modularHessian R) ((phaseVolumeAxis M).comp X) Y + (modularHessian R) X ((phaseVolumeAxis M).comp Y) = 0

end InfoGeometry.Canonical.PhaseVolumeDynamics
