import InfoGeometry.Quantum.SuperchargeMultiplet
import InfoGeometry.Krein.Superphysics
import InfoGeometry.Canonical.ModularHessian
import InfoGeometry.Meta.Vacuity

open scoped InnerProductSpace

/-!
# InfoGeometry.Canonical.PhaseVolumeDynamics

Expository phase-volume naming surface over the doubled-carrier transport lane.

This file keeps older phase/mirror vocabulary as thin wrappers over already
owned doubled-carrier and modular-Hessian structure.
-/

namespace PhaseVolumeDynamics

open InfoGeometry.Krein
open InfoGeometry.Quantum
open InfoGeometry.Canonical.RelationalInformationCore
open InfoGeometry.Canonical.ModularHessian

variable {E : Type 0}
variable [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

local notation "H₂" => DoubledSpace E
local notation "EndH" => H₂ →L[ℝ] H₂

/--
The modular mirror `J` on the doubled carrier.
-/
@[rep_depth transport]
noncomputable def modularMirror 
    (_ : SuperchargeMultiplet (E := E)) : EndH :=
  modular_j (E := E)

/--
The spectral orientation `ε` on the doubled carrier.
-/
@[rep_depth transport]
noncomputable def spectralOrientation 
    (M : SuperchargeMultiplet (E := E)) : EndH :=
  M.modular.Q

/--
The phase-volume axis `K = Jε`.
-/
@[rep_depth transport]
noncomputable def phaseVolumeAxis 
    (_ : SuperchargeMultiplet (E := E)) : EndH :=
  complex_i (E := E)

/--
Compatibility predicate expressing Hessian invariance under `K`-rotation.
-/
@[rep_depth transport]
def IsDynamicRotation
    (M : SuperchargeMultiplet (E := E)) (R : RelationalInformationDatum (E := E)) : Prop :=
  ∀ (X Y : PerturbationChannel E),
    (modularHessian R) ((phaseVolumeAxis M).comp X) Y + (modularHessian R) X ((phaseVolumeAxis M).comp Y) = 0

attribute [expository]
  modularMirror
  spectralOrientation
  phaseVolumeAxis
  IsDynamicRotation

end PhaseVolumeDynamics
