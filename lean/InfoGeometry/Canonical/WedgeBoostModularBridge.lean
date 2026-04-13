import InfoGeometry.Canonical.RealTomitaCore
import InfoGeometry.Canonical.TomitaTakesakiRealStandardForm
import InfoGeometry.Dynamics.UnruhKMS
import InfoGeometry.Meta.Architecture

open scoped InnerProductSpace

/-!
# InfoGeometry.Canonical.WedgeBoostModularBridge

Wedge/Rindler parameter bridge in the repo-native real doubled language.

This file packages the conversion between modular time and wedge-boost rapidity,
and links the Unruh flow owner to the real modular-time normalization.
-/

namespace InfoGeometry.Canonical.WedgeBoostModularBridge

open InfoGeometry.Krein
open InfoGeometry.Canonical.RealTomitaCore
open InfoGeometry.Canonical.TomitaTakesakiRealStandardForm
open InfoGeometry.Dynamics
open InfoGeometry.Canonical.BogoliubovTransport

section Core

variable {E : Type 0}
variable [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

local notation "H₂" => DoubledSpace E
local notation "EndH" => H₂ →L[ℝ] H₂

noncomputable local instance : NormedRing EndH := inferInstance
noncomputable local instance : NormedAlgebra ℝ EndH := inferInstance
local instance : IsTopologicalRing EndH := inferInstance
local instance : CompleteSpace EndH := inferInstance
local instance : SMulCommClass ℝ EndH EndH := inferInstance
local instance : IsScalarTower ℝ EndH EndH := inferInstance

/-- Unruh flow reparameterized by modular time `τ_mod`. -/
@[rep_depth transport]
noncomputable def unruhFlowOfModularTime (τmod : ℝ) : EndH :=
  InfoGeometry.Dynamics.unruhFlow (E := E)
    (RealTomitaCore.wedgeBoostParameter τmod)

@[rep_depth transport, simp]
theorem unruhFlowOfModularTime_eq_unruhFlow (τmod : ℝ) :
    unruhFlowOfModularTime τmod
      =
    InfoGeometry.Dynamics.unruhFlow (E := E)
      (RealTomitaCore.wedgeBoostParameter τmod) := by
  rfl

/-- Unruh flow in modular time has the canonical hyperbolic polynomial form. -/
@[rep_depth transport]
theorem unruhFlowOfModularTime_eq_modular_polynomial (τmod : ℝ) :
    unruhFlowOfModularTime τmod
      = (Real.cosh (RealTomitaCore.wedgeBoostParameter τmod))
          • (ContinuousLinearMap.id ℝ H₂)
        + (Real.sinh (RealTomitaCore.wedgeBoostParameter τmod))
          • InfoGeometry.Dynamics.modularHamiltonian (E := E) := by
  simpa [unruhFlowOfModularTime] using
    (InfoGeometry.Dynamics.unruhFlow_is_modular_flow
      (E := E) (θ := RealTomitaCore.wedgeBoostParameter τmod))

/-- `τ_mod ↦ τ_wedge` and `τ_wedge ↦ τ_mod` are inverse maps (first direction). -/
@[rep_depth transport]
theorem modularTime_roundtrip (τmod : ℝ) :
    RealTomitaCore.modularTimeOfWedgeBoost
      (RealTomitaCore.wedgeBoostParameter τmod)
      = τmod := by
  simpa using
    (RealTomitaCore.modularTimeOfWedgeBoost_wedgeBoostParameter τmod)

/-- `τ_mod ↦ τ_wedge` and `τ_wedge ↦ τ_mod` are inverse maps (second direction). -/
@[rep_depth transport]
theorem wedgeBoost_roundtrip (τwedge : ℝ) :
    RealTomitaCore.wedgeBoostParameter
      (RealTomitaCore.modularTimeOfWedgeBoost τwedge)
      = τwedge := by
  unfold RealTomitaCore.wedgeBoostParameter RealTomitaCore.modularTimeOfWedgeBoost
  have hpi : (2 * Real.pi) ≠ 0 := by
    have h2 : (2 : ℝ) ≠ 0 := by norm_num
    exact mul_ne_zero h2 Real.pi_ne_zero
  field_simp [hpi]

/-- RealTomita and real-standard-form wedge normalization coincide. -/
@[rep_depth transport]
theorem wedgeBoostParameter_agrees_with_standardForm (t : ℝ) :
    RealTomitaCore.wedgeBoostParameter t
      = TomitaTakesakiRealStandardForm.wedgeBoostParameter t := by
  rfl

/-- RealTomita and real-standard-form inverse normalization coincide. -/
@[rep_depth transport]
theorem modularTimeOfWedgeBoost_agrees_with_standardForm (τ : ℝ) :
    RealTomitaCore.modularTimeOfWedgeBoost τ
      = TomitaTakesakiRealStandardForm.modularTimeOfWedgeBoost τ := by
  rfl

/--
Compatibility witness: modular transport flow is identified with Unruh flow
under wedge-normalized time.
-/
@[rep_depth transport]
def FlowEqUnruh (modularSeed : EndH) : Prop :=
  ∀ τmod : ℝ,
    modularTransportFlow (E := E) modularSeed τmod
      = unruhFlowOfModularTime τmod

/--
Direct wedge bridge from the single flow-equivalence theorem, without packaging
it into a compatibility witness structure.
-/
@[rep_depth transport]
theorem flow_at_wedgeParameter_of_flowEqUnruh
    {modularSeed : EndH}
    (hFlowEqUnruh : FlowEqUnruh (E := E) modularSeed)
    (τwedge : ℝ) :
    modularTransportFlow (E := E) modularSeed
      (RealTomitaCore.modularTimeOfWedgeBoost τwedge)
      = InfoGeometry.Dynamics.unruhFlow (E := E) τwedge := by
  calc
    modularTransportFlow (E := E) modularSeed
        (RealTomitaCore.modularTimeOfWedgeBoost τwedge)
        = unruhFlowOfModularTime
            (RealTomitaCore.modularTimeOfWedgeBoost τwedge) := by
              simpa [FlowEqUnruh] using hFlowEqUnruh
                (RealTomitaCore.modularTimeOfWedgeBoost τwedge)
    _ = InfoGeometry.Dynamics.unruhFlow (E := E)
          (RealTomitaCore.wedgeBoostParameter
            (RealTomitaCore.modularTimeOfWedgeBoost τwedge)) := by
          rfl
    _ = InfoGeometry.Dynamics.unruhFlow (E := E) τwedge := by
          rw [wedgeBoost_roundtrip τwedge]

/--
Compatibility witness: modular transport flow is identified with Unruh flow
under wedge-normalized time.
-/
@[rep_depth transport]
structure WedgeBoostModularCompatibility where
  modularSeed : EndH
  hFlowEqUnruh : FlowEqUnruh (E := E) modularSeed

namespace WedgeBoostModularCompatibility

variable (W : WedgeBoostModularCompatibility (E := E))

/-- Under compatibility, modular-time flow equals wedge-rapidity Unruh flow. -/
@[rep_depth transport]
theorem flow_at_wedgeParameter (τwedge : ℝ) :
    modularTransportFlow (E := E) W.modularSeed
      (RealTomitaCore.modularTimeOfWedgeBoost τwedge)
      = InfoGeometry.Dynamics.unruhFlow (E := E) τwedge := by
  exact flow_at_wedgeParameter_of_flowEqUnruh
    (E := E) (modularSeed := W.modularSeed) W.hFlowEqUnruh τwedge

end WedgeBoostModularCompatibility

end Core

end InfoGeometry.Canonical.WedgeBoostModularBridge
