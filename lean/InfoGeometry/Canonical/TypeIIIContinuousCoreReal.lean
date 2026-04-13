import InfoGeometry.Canonical.RealTomitaCore
import InfoGeometry.Canonical.YangMillsContinuum
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

end RealContinuousCoreInterface

end Core

end InfoGeometry.Canonical.TypeIIIContinuousCoreReal
