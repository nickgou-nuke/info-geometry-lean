import InfoGeometry.Canonical.RealTomitaCore
import InfoGeometry.Canonical.YangMillsContinuum
import InfoGeometry.Canonical.GlobalChiralDecomposition
import InfoGeometry.Canonical.SingularDecompositionSurrogate
import InfoGeometry.Volume.ConnesCocycle
import InfoGeometry.Meta.Architecture

open scoped InnerProductSpace

/-!
# InfoGeometry.Canonical.TypeIIIContinuousCoreReal

Type-III continuous-core interface in the repo-native real doubled language.

This file does not construct crossed products internally. It provides a strict,
compiled interface layer that packages:

- base Type-III modular data,
- modular-flow/additive-flow laws,
- bridge hook into the real Tomita `δ = log Δ` lane,
- an abstract continuous-core API (dual action + trace invariance).
-/

namespace InfoGeometry.Canonical.TypeIIIContinuousCoreReal

open InfoGeometry.Canonical
open InfoGeometry.Canonical.YangMillsContinuum
open InfoGeometry.Canonical.RealTomitaCore

section Core

variable {E : Type 0}
variable [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

local notation "EndH" => YangMillsContinuum.EndH E

noncomputable local instance : NormedRing EndH := inferInstance
noncomputable local instance : NormedAlgebra ℝ EndH := inferInstance
local instance : IsTopologicalRing EndH := inferInstance
local instance : CompleteSpace EndH := inferInstance

/-- Base Type-III modular package on the real doubled carrier. -/
@[rep_depth transport]
structure RealTypeIIIModularData where
  rn : ModularRadonNikodymData E
  hTypeIII : ModularRadonNikodymData.TypeIIIModularInterface (E := E) rn

namespace RealTypeIIIModularData

variable (R : RealTypeIIIModularData (E := E))

/-- Real additive modular flow from the Type-III RN owner. -/
@[rep_depth transport]
noncomputable def additiveFlow : InfoGeometry.Volume.ConnesCocycle.AdditiveModularFlow (H := E) :=
  R.rn.toAdditiveModularFlow

@[rep_depth transport, simp]
theorem additiveFlow_apply (t : ℝ) (A : EndH) :
    R.additiveFlow t A = ModularRadonNikodymData.modularAutomorphismGroup R.rn t A := by
  rfl

/-- Modular flow on endomorphisms from RN data. -/
@[rep_depth transport]
noncomputable def modularFlow : ℝ → EndH → EndH :=
  ModularRadonNikodymData.modularAutomorphismGroup R.rn

@[rep_depth transport, simp]
theorem modularFlow_zero (A : EndH) :
    R.modularFlow 0 A = A := by
  simpa [modularFlow] using (ModularRadonNikodymData.modularAutomorphismGroup_zero (M := R.rn) A)

@[rep_depth transport]
theorem modularFlow_add (s t : ℝ) (A : EndH) :
    R.modularFlow (s + t) A = R.modularFlow s (R.modularFlow t A) := by
  simpa [modularFlow] using
    (R.hTypeIII.modularAutomorphismGroup_additive s t A)

/-- The Type-III modular generator on the RN lane. -/
@[rep_depth transport]
noncomputable def modularGenerator : EndH := R.rn.modularHamiltonian

@[rep_depth transport]
theorem modularOperator_eq_rn :
    R.rn.modularOperator = R.rn.rnDerivative • YangMillsContinuum.idEndH E :=
  R.hTypeIII.modularOperator_eq_rn

@[rep_depth transport]
theorem modularHamiltonian_eq_neg_log_rn :
    R.rn.modularHamiltonian = (-Real.log R.rn.rnDerivative) • YangMillsContinuum.idEndH E :=
  R.hTypeIII.modularHamiltonian_eq_neg_log_rn

/--
Bridge hook into the real Tomita `δ = log Δ` package.

`hExp` is the explicit witness that the chosen generator exponentiates to `Δ`.
-/
@[rep_depth transport]
noncomputable def toRealModularLogData
    (hExp : NormedSpace.exp R.modularGenerator = R.rn.modularOperator) :
    RealTomitaCore.RealModularLogData (E := E) where
  Delta := R.rn.modularOperator
  deltaLog := R.modularGenerator
  exp_deltaLog := by
    simpa [modularGenerator] using hExp

@[rep_depth transport]
theorem modularTransportFlow_eq_realTomitaFlow
    (hExp : NormedSpace.exp R.modularGenerator = R.rn.modularOperator)
    (t : ℝ) :
    InfoGeometry.Canonical.BogoliubovTransport.modularTransportFlow (E := E) R.modularGenerator t
      = (R.toRealModularLogData hExp).flow t := by
  rfl

end RealTypeIIIModularData

/--
Abstract real continuous-core interface:
`Core` + dual action + trace invariant under the dual action.
-/
@[rep_depth transport]
structure RealContinuousCoreInterface where
  base : RealTypeIIIModularData (E := E)
  Core : Type
  toCore : EndH → Core
  dualAction : ℝ → Core → Core
  coreTrace : Core → ℝ
  dualAction_zero : ∀ x : Core, dualAction 0 x = x
  dualAction_add : ∀ s t : ℝ, ∀ x : Core,
    dualAction (s + t) x = dualAction s (dualAction t x)
  trace_dualAction_invariant : ∀ t : ℝ, ∀ x : Core,
    coreTrace (dualAction t x) = coreTrace x

namespace RealContinuousCoreInterface

variable (C : RealContinuousCoreInterface (E := E))

/-- Core fixed-point predicate for the dual action. -/
@[rep_depth transport]
def IsDualFixed (x : C.Core) : Prop :=
  ∀ t : ℝ, C.dualAction t x = x

/-- Modular fixed-point predicate on the base operator lane. -/
@[rep_depth transport]
def IsModularFixed (A : EndH) : Prop :=
  ∀ t : ℝ, C.base.modularFlow t A = A

/-- Dual action preserves its fixed-point sector. -/
@[rep_depth transport]
theorem dualAction_preserves_dualFixed
    (x : C.Core)
    (hfix : C.IsDualFixed x)
    (s : ℝ) :
    C.IsDualFixed (C.dualAction s x) := by
  intro t
  have hs : C.dualAction s x = x := hfix s
  calc
    C.dualAction t (C.dualAction s x) = C.dualAction t x := by rw [hs]
    _ = x := hfix t
    _ = C.dualAction s x := by simpa [hs]

/-- Base modular flow preserves its fixed-point sector. -/
@[rep_depth transport]
theorem modularFlow_preserves_modularFixed
    (A : EndH)
    (hfix : C.IsModularFixed A)
    (s : ℝ) :
    C.IsModularFixed (C.base.modularFlow s A) := by
  intro t
  calc
    C.base.modularFlow t (C.base.modularFlow s A)
        = C.base.modularFlow (t + s) A := by
            symm
            exact C.base.modularFlow_add t s A
    _ = A := hfix (t + s)
    _ = C.base.modularFlow s A := by
          symm
          exact hfix s

/-- Dual-action invariance of trace extends to the dual-fixed sector. -/
@[rep_depth transport]
theorem trace_constant_on_dualFixed
    (x : C.Core)
    (_hfix : C.IsDualFixed x)
    (t : ℝ) :
    C.coreTrace (C.dualAction t x) = C.coreTrace x := by
  simpa using C.trace_dualAction_invariant t x

/--
Downstream CP-003 consumer on the Type-III core lane:
if an operator commutes with the active projector, its core-trace equals the
core-trace of the singular polar/KAN surrogate split from
`GlobalChiralDecomposition`.
-/
@[rep_depth transport]
theorem coreTrace_eq_singularPolar_split_of_commute
    (CIK : CertifiedInverseKernel (InfoGeometry.Krein.DoubledSpace E))
    (A : EndH)
    (hComm : Commute CIK.spectralProjector A) :
    C.coreTrace (C.toCore A)
      =
    C.coreTrace
      (C.toCore
        (CIK.spectralComplementaryProjector * A * CIK.spectralComplementaryProjector
          + CIK.spectralProjector * A * CIK.spectralProjector)) := by
  have hSplit :
      A
        =
      CIK.spectralComplementaryProjector * A * CIK.spectralComplementaryProjector
        + CIK.spectralProjector * A * CIK.spectralProjector := by
    exact
      (InfoGeometry.Canonical.GlobalChiralDecomposition.singularPolarKAN_replacement_of_commute
        (E := E) (CIK := CIK) (R := A) hComm).1
  exact congrArg (fun X => C.coreTrace (C.toCore X)) hSplit

/--
Dual-action trace form of the CP-003 consumer:
trace invariance transports the singular split equality to every dual-action
time.
-/
@[rep_depth transport]
theorem coreTrace_dualAction_eq_singularPolar_split_of_commute
    (CIK : CertifiedInverseKernel (InfoGeometry.Krein.DoubledSpace E))
    (A : EndH)
    (hComm : Commute CIK.spectralProjector A)
    (t : ℝ) :
    C.coreTrace (C.dualAction t (C.toCore A))
      =
    C.coreTrace
      (C.dualAction t
        (C.toCore
          (CIK.spectralComplementaryProjector * A * CIK.spectralComplementaryProjector
            + CIK.spectralProjector * A * CIK.spectralProjector))) := by
  rw [C.trace_dualAction_invariant, C.trace_dualAction_invariant]
  exact C.coreTrace_eq_singularPolar_split_of_commute (CIK := CIK) (A := A) hComm

/--
Wedge-calibrated downstream CP-003 consumer on the Type-III core lane:
the canonical bounded relative modular representative has the same core-trace as
its active/apex projector-compressed surrogate split.
-/
@[rep_depth transport]
theorem coreTrace_eq_singularPolar_split_of_wedgeCalibrated
    (CIK : CertifiedInverseKernel (InfoGeometry.Krein.DoubledSpace E))
    {W : InfoGeometry.Canonical.ModularSpectralWedge.HasModularSpectralWedge E}
    (Cw :
      InfoGeometry.Canonical.ModularSpectralWedgeBridge.WedgeCalibrated
        (E := E)
        (T := InfoGeometry.Canonical.ModularSuperchargeClosure.canonicalTomitaLogData (E := E) CIK)
        (W := W)
        (owned_epsilon := InfoGeometry.Krein.spectral_epsilon (E := E))
        (owned_P_D := CIK.spectralComplementaryProjector))
    (τ : ℝ) :
    C.coreTrace
      (C.toCore
        (InfoGeometry.Canonical.RelativeModularScaleShapeSplit.canonicalRelativeModularOperator
          (E := E) CIK τ))
      =
    C.coreTrace
      (C.toCore
        (CIK.spectralComplementaryProjector
            * InfoGeometry.Canonical.RelativeModularScaleShapeSplit.canonicalRelativeModularOperator
                (E := E) CIK τ
            * CIK.spectralComplementaryProjector
          +
          CIK.spectralProjector
            * InfoGeometry.Canonical.RelativeModularScaleShapeSplit.canonicalRelativeModularOperator
                (E := E) CIK τ
            * CIK.spectralProjector)) := by
  have hSplit :
      InfoGeometry.Canonical.RelativeModularScaleShapeSplit.canonicalRelativeModularOperator
          (E := E) CIK τ
        =
      CIK.spectralComplementaryProjector
          * InfoGeometry.Canonical.RelativeModularScaleShapeSplit.canonicalRelativeModularOperator
              (E := E) CIK τ
          * CIK.spectralComplementaryProjector
        +
      CIK.spectralProjector
          * InfoGeometry.Canonical.RelativeModularScaleShapeSplit.canonicalRelativeModularOperator
              (E := E) CIK τ
          * CIK.spectralProjector := by
    exact
      (InfoGeometry.Canonical.SingularDecompositionSurrogate.canonicalRelativeModularOperator_singular_surrogate_package_of_wedgeCalibrated
        (E := E) (CIK := CIK) (W := W) Cw τ).1
  exact congrArg (fun X => C.coreTrace (C.toCore X)) hSplit

/--
Dual-action trace form of the wedge-calibrated CP-003 consumer.
-/
@[rep_depth transport]
theorem coreTrace_dualAction_eq_singularPolar_split_of_wedgeCalibrated
    (CIK : CertifiedInverseKernel (InfoGeometry.Krein.DoubledSpace E))
    {W : InfoGeometry.Canonical.ModularSpectralWedge.HasModularSpectralWedge E}
    (Cw :
      InfoGeometry.Canonical.ModularSpectralWedgeBridge.WedgeCalibrated
        (E := E)
        (T := InfoGeometry.Canonical.ModularSuperchargeClosure.canonicalTomitaLogData (E := E) CIK)
        (W := W)
        (owned_epsilon := InfoGeometry.Krein.spectral_epsilon (E := E))
        (owned_P_D := CIK.spectralComplementaryProjector))
    (τ t : ℝ) :
    C.coreTrace
      (C.dualAction t
        (C.toCore
          (InfoGeometry.Canonical.RelativeModularScaleShapeSplit.canonicalRelativeModularOperator
            (E := E) CIK τ)))
      =
    C.coreTrace
      (C.dualAction t
        (C.toCore
          (CIK.spectralComplementaryProjector
              * InfoGeometry.Canonical.RelativeModularScaleShapeSplit.canonicalRelativeModularOperator
                  (E := E) CIK τ
              * CIK.spectralComplementaryProjector
            +
            CIK.spectralProjector
              * InfoGeometry.Canonical.RelativeModularScaleShapeSplit.canonicalRelativeModularOperator
                  (E := E) CIK τ
              * CIK.spectralProjector))) := by
  rw [C.trace_dualAction_invariant, C.trace_dualAction_invariant]
  exact C.coreTrace_eq_singularPolar_split_of_wedgeCalibrated
    (CIK := CIK) (W := W) Cw τ

end RealContinuousCoreInterface

end Core

end InfoGeometry.Canonical.TypeIIIContinuousCoreReal
