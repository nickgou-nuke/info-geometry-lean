import InfoGeometry.Canonical.ModularOrientationContract
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Canonical.BogoliubovTransport
import InfoGeometry.Canonical.StandardFormCore
import InfoGeometry.Meta.Architecture

open scoped InnerProductSpace

/-!
# InfoGeometry.Canonical.RealTomitaCore

Real-doubled Tomita core in the owned `(H₂, J, ε, K)` language.

This file provides:
- commutant action via `J`,
- a `δ = log Δ` interface,
- real modular flow and adjoint flow,
- orientation-flip law: `δ ↦ -δ` is equivalent to `τ ↦ -τ`.
-/

namespace InfoGeometry.Canonical.RealTomitaCore

open InfoGeometry.Krein
open InfoGeometry.Canonical.BogoliubovTransport
open InfoGeometry.Canonical.ModularOrientationContract
open InfoGeometry.Canonical.StandardFormCore

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

/-- Real commutant action by the modular conjugation axis `J`. -/
@[rep_depth operator]
noncomputable def commutantAction (A : EndH) : EndH :=
  (modular_j (E := E)) * A * (modular_j (E := E))

/-- `J ↦ -J` is a pure gauge for commutant action. -/
@[rep_depth operator]
theorem commutantAction_invariant_under_J_flip
    (A : EndH) :
    ((-(modular_j (E := E))) * A * (-(modular_j (E := E))))
      = commutantAction (E := E) A := by
  let _ : CompleteSpace E := inferInstance
  unfold commutantAction
  exact
    (ModularOrientationContract.commutantAction_invariant_under_modular_j_flip
      (E := E) A)

/-- Minimal real-doubled `δ = log Δ` interface. -/
@[rep_depth krein]
structure RealModularLogData where
  Delta : EndH
  deltaLog : EndH
  exp_deltaLog : NormedSpace.exp deltaLog = Delta

namespace RealModularLogData

variable (T : RealModularLogData (E := E))

/-- True modular generator in the doubled-real transport lane: `A := δ ∘ K`. -/
@[rep_depth krein]
noncomputable def generator : EndH :=
  modularTransportGenerator (E := E) T.deltaLog

/-- Real modular flow `σ_τ = exp(τ • A)`. -/
@[rep_depth krein]
noncomputable def flow (τ : ℝ) : EndH :=
  modularTransportFlow (E := E) T.deltaLog τ

/-- Real modular adjoint flow on observables. -/
@[rep_depth krein]
noncomputable def adjointFlow (τ : ℝ) (A : EndH) : EndH :=
  T.flow τ * A * T.flow (-τ)

@[rep_depth krein, simp]
theorem flow_zero : T.flow 0 = 1 := by
  let _ : CompleteSpace E := inferInstance
  unfold flow
  exact modularTransportFlow_zero (E := E) T.deltaLog

@[rep_depth krein]
theorem flow_add (s t : ℝ) :
    T.flow (s + t) = T.flow s * T.flow t := by
  simpa [flow] using modularTransportFlow_add (E := E) T.deltaLog s t

@[rep_depth krein]
theorem flow_neg_mul (t : ℝ) :
    T.flow (-t) * T.flow t = 1 := by
  have hAdd := modularTransportFlow_add (E := E) T.deltaLog (-t) t
  have hZero : modularTransportFlow (E := E) T.deltaLog 0 = 1 :=
    modularTransportFlow_zero (E := E) T.deltaLog
  calc
    T.flow (-t) * T.flow t
        = modularTransportFlow (E := E) T.deltaLog (-t)
            * modularTransportFlow (E := E) T.deltaLog t := by
              rfl
    _ = modularTransportFlow (E := E) T.deltaLog ((-t) + t) := by
          simpa [flow] using hAdd.symm
    _ = modularTransportFlow (E := E) T.deltaLog 0 := by simp
    _ = 1 := hZero

@[rep_depth krein]
theorem flow_mul_neg (t : ℝ) :
    T.flow t * T.flow (-t) = 1 := by
  have hAdd := modularTransportFlow_add (E := E) T.deltaLog t (-t)
  have hZero : modularTransportFlow (E := E) T.deltaLog 0 = 1 :=
    modularTransportFlow_zero (E := E) T.deltaLog
  calc
    T.flow t * T.flow (-t)
        = modularTransportFlow (E := E) T.deltaLog t
            * modularTransportFlow (E := E) T.deltaLog (-t) := by
              rfl
    _ = modularTransportFlow (E := E) T.deltaLog (t + (-t)) := by
          simpa [flow] using hAdd.symm
    _ = modularTransportFlow (E := E) T.deltaLog 0 := by simp
    _ = 1 := hZero

@[rep_depth krein, simp]
theorem adjointFlow_zero (A : EndH) :
    T.adjointFlow 0 A = A := by
  unfold adjointFlow
  simp [flow_zero]

/-- Orientation gauge law: `δ ↦ -δ` is equivalent to `τ ↦ -τ`. -/
@[rep_depth transport]
theorem flow_negLog_eq_time_reverse (τ : ℝ) :
    modularTransportFlow (E := E) (-T.deltaLog) τ = T.flow (-τ) := by
  simpa [flow] using
    (ModularOrientationContract.modularTransportFlow_neg_generator_eq_time_reverse
      (E := E) T.deltaLog τ)

end RealModularLogData

/-- Wedge/boost normalization map `τ_wedge = 2π τ_mod`. -/
@[rep_depth transport]
noncomputable def wedgeBoostParameter (τmod : ℝ) : ℝ := (2 * Real.pi) * τmod

/-- Inverse normalization map `τ_mod = τ_wedge / (2π)`. -/
@[rep_depth transport]
noncomputable def modularTimeOfWedgeBoost (τwedge : ℝ) : ℝ := ((2 * Real.pi)⁻¹) * τwedge

/-- The wedge/boost normalization maps are inverse. -/
@[rep_depth transport]
theorem modularTimeOfWedgeBoost_wedgeBoostParameter (τmod : ℝ) :
    modularTimeOfWedgeBoost (wedgeBoostParameter τmod) = τmod := by
  unfold modularTimeOfWedgeBoost wedgeBoostParameter
  have hpi : (2 * Real.pi) ≠ 0 := by
    have h2 : (2 : ℝ) ≠ 0 := by norm_num
    exact mul_ne_zero h2 Real.pi_ne_zero
  field_simp [hpi]

end Core

end InfoGeometry.Canonical.RealTomitaCore
