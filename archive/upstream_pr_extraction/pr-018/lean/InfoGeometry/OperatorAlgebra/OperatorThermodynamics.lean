/-
InfoGeometry/OperatorAlgebra/OperatorThermodynamics.lean

KMS thermodynamics from modular restriction.

This module separates three facts:

1. KMS thermality is modular/operator-algebraic.
2. Partial trace is only the finite/type-I shadow.
3. Hawking/Unruh thermality requires a geometric horizon calibration
   identifying modular flow with physical time/boost flow.

In particular, the KMS theorem is a Tomita-Takesaki theorem, not a theorem of
`Cl(1,1)` non-orientability by itself.  At this layer we prove only
witness-gated consequences: once an observer reduction is supplied together
with a KMS state for the modular flow, the local observer readout is KMS.
Horizon radiation interpretations require a separate boost/Killing-flow
calibration witness.
-/

import Mathlib
import InfoGeometry.OperatorAlgebra.ModularWeightTrace
import InfoGeometry.OperatorAlgebra.SymmetryInvariants
import InfoGeometry.OperatorAlgebra.TomitaCartanSplit

noncomputable section

namespace InfoGeometry.OperatorAlgebra.OperatorThermodynamics

open InfoGeometry.OperatorAlgebra.TomitaCartanSplit

/-! ## 1. States and flows -/

/--
A scalar state/evaluation functional on an ambient algebra.

This is deliberately minimal. Concrete modules may add positivity, normality,
faithfulness, continuity, or GNS data.
-/
structure AlgebraicState
    (Op : Type*) [Mul Op] where
  /-- Evaluation of the state. -/
  eval : Op → ℂ

  /-- Positivity/normality/faithfulness certificate, abstract at this layer. -/
  state_certificates : Prop

/--
A one-parameter automorphism-like flow.

For type III and AQFT models this is usually a modular flow.
-/
structure OperatorFlow
    (Op : Type*) [Mul Op] where
  /-- The time-parametrized flow. -/
  flow : ℝ → Op → Op

  /-- Time zero acts trivially. -/
  flow_zero :
    ∀ x : Op, flow 0 x = x

  /-- Additive flow law. -/
  flow_add :
    ∀ s t x, flow (s + t) x = flow s (flow t x)

  /-- Multiplicativity/covariance certificate. -/
  multiplicative : Prop

namespace OperatorFlow

variable {Op : Type*} [Mul Op]
variable (σ : OperatorFlow Op)

@[simp]
theorem flow_zero_apply
    (x : Op) :
    σ.flow 0 x = x :=
  σ.flow_zero x

theorem flow_add_apply
    (s t : ℝ)
    (x : Op) :
    σ.flow (s + t) x = σ.flow s (σ.flow t x) :=
  σ.flow_add s t x

end OperatorFlow

/-! ## 2. KMS state socket -/

/--
KMS state at inverse temperature `beta`.

The analytic strip condition is proof-carrying. In concrete analytic models,
this field should be replaced or refined by the usual holomorphic strip
boundary condition.
-/
structure KMSState
    (Op : Type*) [Mul Op]
    (σ : OperatorFlow Op)
    (beta : ℝ) where
  /-- The underlying state. -/
  state : AlgebraicState Op

  /-- Real-time invariance of the state under the flow. -/
  flow_invariant :
    ∀ t x, state.eval (σ.flow t x) = state.eval x

  /--
  KMS analytic boundary condition.

  Morally:
    `F(t) = omega(A sigma_t(B))`
    `F(t + i beta) = omega(sigma_t(B) A)`

  The analytic details are model-dependent, so they are stored as a certificate.
  -/
  kms_boundary_condition : Prop

  /-- Evidence for the KMS analytic boundary condition. -/
  kms_boundary_condition_holds :
    kms_boundary_condition

namespace KMSState

variable {Op : Type*} [Mul Op]
variable {σ : OperatorFlow Op}
variable {beta : ℝ}
variable (K : KMSState Op σ beta)

/-- Re-export flow invariance. -/
theorem invariant
    (t : ℝ)
    (x : Op) :
    K.state.eval (σ.flow t x) = K.state.eval x :=
  K.flow_invariant t x

/-- Re-export the analytic KMS boundary certificate. -/
theorem kms_boundary_holds :
    K.kms_boundary_condition :=
  K.kms_boundary_condition_holds

end KMSState

/-! ## 3. Restriction instead of naive partial trace -/

/--
Restriction of a global state to an observable subalgebra.

This is the type-III-safe replacement for the finite-dimensional phrase
"trace out the commutant".
-/
structure StateRestriction
    (Global Local : Type*)
    [Mul Global] [Mul Local] where
  /-- Embedding of the local algebra into the global algebra. -/
  includeMap : Local → Global

  /-- Global state. -/
  globalState : AlgebraicState Global

  /-- Restricted local state. -/
  localState : AlgebraicState Local

  /-- The local state is the global state evaluated on the inclusion. -/
  restrict_eq :
    ∀ a : Local,
      localState.eval a = globalState.eval (includeMap a)

namespace StateRestriction

variable {Global Local : Type*} [Mul Global] [Mul Local]
variable (R : StateRestriction Global Local)

/-- Re-export the restriction equation. -/
theorem local_eval_eq_global
    (a : Local) :
    R.localState.eval a = R.globalState.eval (R.includeMap a) :=
  R.restrict_eq a

end StateRestriction

/--
Finite/type-I shadow of state restriction.

In finite tensor-product models this may be implemented by a partial trace.
In type III models this should not be used as primitive structure.
-/
structure FinitePartialTraceShadow
    (Global Local Hidden : Type*)
    [Mul Global] [Mul Local] [Mul Hidden] where
  /-- State restriction, the type-III-safe primitive. -/
  restriction : StateRestriction Global Local

  /-- Partial-trace operation, meaningful only in finite/type-I models. -/
  partialTrace : AlgebraicState Global → AlgebraicState Local

  /-- Agreement of the finite partial-trace formula with restriction. -/
  partialTrace_agrees_with_restriction : Prop

/-! ## 4. Tomita observer reduction and KMS thermalization -/

/--
Proof-carrying KMS boundary predicate for a concrete evaluation functional.

The true KMS condition is an analytic strip-boundary condition. This structure
keeps that content as supplied evidence instead of making it definitionally
`True`.
-/
structure KMSAnalyticBoundary
    {Op : Type*} [Mul Op]
    (_eval : Op → ℂ)
    (_σ : OperatorFlow Op)
    (_beta : ℝ) where
  /-- Analytic strip-boundary statement for the supplied readout and flow. -/
  boundaryCondition : Prop

  /-- Evidence that the boundary condition holds. -/
  boundaryCondition_holds :
    boundaryCondition

/--
Observer reduction from a global algebraic state to the observable algebra
side of a Tomita pair.

In finite type-I shadows this may be implemented by a partial trace.  In type
III/Tomita settings it should be understood as restriction or modular
reduction to the observable algebra, backed by a modular weight, core trace,
conditional expectation, or another concrete backend.
-/
structure ObserverReduction
    (Op : Type*) [Ring Op]
    (T : TomitaCommutantDatum Op) where
  /-- Global state/expectation readout. -/
  globalEval : Op → ℂ

  /-- Local observer readout on the observable algebra. -/
  observableEval : Op → ℂ

  /-- On observable elements, local and global readouts agree. -/
  agrees_on_observable :
    ∀ A : Op, A ∈ T.M → observableEval A = globalEval A

  /-- Law: the commutant is inaccessible to the local observer. -/
  commutant_inaccessible_law : Prop

  /-- Evidence that the commutant is inaccessible to the local observer. -/
  commutant_inaccessible :
    commutant_inaccessible_law

  /-- Law for the selected restriction/reduction backend. -/
  reduction_backend_law : Prop

  /-- Evidence for the selected restriction/reduction backend. -/
  reduction_backend_valid :
    reduction_backend_law

namespace ObserverReduction

variable {Op : Type*} [Ring Op]
variable {T : TomitaCommutantDatum Op}
variable (R : ObserverReduction Op T)

/-- Re-export agreement of the observer readout with the global readout on `M`. -/
theorem observable_agrees
    {A : Op}
    (hA : A ∈ T.M) :
    R.observableEval A = R.globalEval A :=
  R.agrees_on_observable A hA

end ObserverReduction

/--
Witness that an observer reduction is thermal with respect to a modular flow.

This is the precise replacement for the finite-dimensional slogan "trace out
the commutant."  The reduced observer state is explicitly supplied as a KMS
state for the selected modular flow.
-/
structure TomitaKMSThermalization
    (Op : Type*) [Ring Op]
    (T : TomitaCommutantDatum Op)
    (σ : OperatorFlow Op)
    (beta : ℝ) where
  /-- Observer reduction/restriction. -/
  reduction : ObserverReduction Op T

  /-- The thermal/KMS state seen by the local observer. -/
  thermal : KMSState Op σ beta

  /-- The thermal state is exactly the reduced observer state. -/
  thermal_eq_reduction :
    ∀ A : Op, thermal.state.eval A = reduction.observableEval A

  /-- Law that the modular flow is the Tomita flow of the pair/state. -/
  modular_origin_law : Prop

  /-- Evidence that the modular flow is the Tomita flow of the pair/state. -/
  modular_origin :
    modular_origin_law

  /-- Optional geometric/horizon law, e.g. wedge or Killing horizon data. -/
  horizon_or_wedge_origin_law : Prop

  /-- Evidence for the optional geometric/horizon law. -/
  horizon_or_wedge_origin :
    horizon_or_wedge_origin_law

namespace TomitaKMSThermalization

variable {Op : Type*} [Ring Op]
variable {T : TomitaCommutantDatum Op}
variable {σ : OperatorFlow Op}
variable {beta : ℝ}
variable (Θ : TomitaKMSThermalization Op T σ beta)

/-- The observer-reduced state is represented by a KMS state. -/
theorem exists_kms_state_for_observer :
    ∃ ω : KMSState Op σ beta,
      ω.state.eval = Θ.reduction.observableEval := by
  refine ⟨Θ.thermal, ?_⟩
  funext A
  exact Θ.thermal_eq_reduction A

/-- The observer-reduced state carries the named KMS boundary certificate. -/
def reduced_state_is_kms :
    KMSAnalyticBoundary Θ.reduction.observableEval σ beta where
  boundaryCondition := Θ.thermal.kms_boundary_condition
  boundaryCondition_holds := Θ.thermal.kms_boundary_condition_holds

/-- The local observer's readout is invariant under real modular time. -/
theorem reduced_state_flow_invariant
    (t : ℝ)
    (A : Op) :
    Θ.reduction.observableEval (σ.flow t A) =
      Θ.reduction.observableEval A := by
  calc
    Θ.reduction.observableEval (σ.flow t A)
        = Θ.thermal.state.eval (σ.flow t A) := by
            rw [← Θ.thermal_eq_reduction]
    _ = Θ.thermal.state.eval A :=
            Θ.thermal.invariant t A
    _ = Θ.reduction.observableEval A :=
            Θ.thermal_eq_reduction A

/-- On observable algebra elements, the thermal KMS state agrees with the global state. -/
theorem thermal_agrees_with_global_on_observable
    {A : Op}
    (hA : A ∈ T.M) :
    Θ.thermal.state.eval A = Θ.reduction.globalEval A := by
  calc
    Θ.thermal.state.eval A
        = Θ.reduction.observableEval A :=
            Θ.thermal_eq_reduction A
    _ = Θ.reduction.globalEval A :=
            Θ.reduction.observable_agrees hA

end TomitaKMSThermalization

/--
A horizon or topological boundary that routes observable degrees of freedom
toward the commutant.

The boundary/twist does not by itself create a KMS state; it supplies geometric
partition data to which a modular thermalization witness may be applied.
-/
structure HorizonCommutantBoundary
    (Op : Type*) [Ring Op]
    (T : TomitaCommutantDatum Op) where
  /-- Boundary map/readout. -/
  boundary : Op → Op

  /-- Observable elements hitting the boundary are routed to the commutant. -/
  boundary_maps_observable_to_commutant :
    ∀ A : Op, A ∈ T.M → boundary A ∈ T.Mcomm

  /-- Law saying this boundary is the intended defect/horizon locus. -/
  boundary_is_defect_locus_law : Prop

  /-- Evidence that this boundary is the intended defect/horizon locus. -/
  boundary_is_defect_locus :
    boundary_is_defect_locus_law

/--
Full thermodynamic horizon witness:

Tomita algebra/commutant routing, horizon boundary, observer reduction, and KMS
thermalization of the reduced state.
-/
structure HorizonKMSThermodynamics
    (Op : Type*) [Ring Op]
    (T : TomitaCommutantDatum Op)
    (σ : OperatorFlow Op)
    (beta : ℝ) where
  /-- Boundary routing observables toward the commutant. -/
  boundary : HorizonCommutantBoundary Op T

  /-- KMS thermalization of the reduced observer state. -/
  thermalization : TomitaKMSThermalization Op T σ beta

namespace HorizonKMSThermodynamics

variable {Op : Type*} [Ring Op]
variable {T : TomitaCommutantDatum Op}
variable {σ : OperatorFlow Op}
variable {beta : ℝ}
variable (H : HorizonKMSThermodynamics Op T σ beta)

/-- Boundary-routed observable data lands in the commutant sector. -/
theorem observable_boundary_in_commutant
    {A : Op}
    (hA : A ∈ T.M) :
    H.boundary.boundary A ∈ T.Mcomm :=
  H.boundary.boundary_maps_observable_to_commutant A hA

/-- The local observer sees a KMS state. -/
theorem observer_sees_kms :
    ∃ ω : KMSState Op σ beta,
      ω.state.eval = H.thermalization.reduction.observableEval :=
  H.thermalization.exists_kms_state_for_observer

/-- The reduced observer state carries a KMS boundary certificate. -/
def reduced_state_is_kms :
    KMSAnalyticBoundary
      H.thermalization.reduction.observableEval σ beta :=
  H.thermalization.reduced_state_is_kms

end HorizonKMSThermodynamics

/-! ## 5. Modular KMS theorem socket -/

/--
A modular KMS datum.

This is the formal Tomita-Takesaki socket: the state restricted to the
observable algebra is KMS for its modular flow.
-/
structure ModularKMSDatum
    (Op : Type*) [Mul Op] where
  /-- Modular flow. -/
  modularFlow : OperatorFlow Op

  /-- Inverse temperature normalization. Usually `1` for abstract modular time. -/
  beta : ℝ

  /-- The modular/KMS state. -/
  kms : KMSState Op modularFlow beta

  /-- Tomita-Takesaki modular theorem certificate. -/
  tomita_takesaki_certificate : Prop

/-! ## 6. Horizon / Unruh / Hawking calibration -/

/--
A geometric calibration identifying modular time with physical horizon time.

Without this field, the KMS state is modular-thermal but not yet physically
identified as Unruh or Hawking radiation.
-/
structure HorizonFlowCalibration
    (Op : Type*) [Mul Op]
    (σ : OperatorFlow Op) where
  /-- Physical flow, e.g. boost or Killing horizon flow. -/
  physicalFlow : OperatorFlow Op

  /-- Relation between modular time and physical time. -/
  time_rescaling : ℝ

  /-- Calibration: modular flow equals the physical flow after rescaling. -/
  modular_eq_physical_after_rescaling :
    ∀ t x,
      σ.flow t x =
        physicalFlow.flow (time_rescaling * t) x

  /--
  Geometric theorem certificate.

  Intended examples include Bisognano-Wichmann for Rindler wedge/Unruh and
  horizon/Killing-flow calibration for Hawking.
  -/
  geometric_calibration_certificate : Prop

/--
Emergent thermal radiation datum.

This does not claim to prove Hawking radiation from topology alone. It records
that a modular KMS state plus a horizon-flow calibration yields a physical
thermal readout.
-/
structure EmergentThermalRadiation
    (Op : Type*) [Mul Op] where
  /-- Modular KMS theorem socket. -/
  modularKMS : ModularKMSDatum Op

  /-- Horizon/boost-flow calibration. -/
  horizonCalibration :
    HorizonFlowCalibration Op modularKMS.modularFlow

  /-- Physical inverse temperature after the geometric rescaling. -/
  physicalBeta : ℝ

  /--
  Certificate relating `physicalBeta` to modular beta and the time rescaling.
  The exact formula depends on conventions.
  -/
  beta_calibration : Prop

namespace EmergentThermalRadiation

variable {Op : Type*} [Mul Op]
variable (E : EmergentThermalRadiation Op)

/-- The local state is KMS before geometric interpretation. -/
def modularThermalState :
    KMSState Op E.modularKMS.modularFlow E.modularKMS.beta :=
  E.modularKMS.kms

/-- Thermality as seen by the calibrated physical observer starts from KMS. -/
theorem has_modular_kms_state :
    Nonempty (KMSState Op E.modularKMS.modularFlow E.modularKMS.beta) :=
  ⟨E.modularThermalState⟩

end EmergentThermalRadiation

/-! ## 7. Raw modular restriction compatibility sockets -/

/--
Raw KMS condition for a supplied flow function.

This is a proof-carrying analytic socket.  It is useful when a concrete model
has not yet packaged its flow as `OperatorFlow`.
-/
structure KMSCondition
    (Op : Type*) [Mul Op]
    (flow : ℝ → Op → Op)
    (beta : ℝ)
    (eval : Op → ℂ) where
  /-- Real-time invariance of the readout. -/
  flow_invariant :
    ∀ t : ℝ, ∀ a : Op, eval (flow t a) = eval a

  /-- Analytic strip statement. -/
  analyticStrip : Prop

  /-- KMS boundary relation on analytic elements. -/
  boundaryRelation : Prop

/--
A doubled/global state for a Tomita commutant pair.

The exact positivity, normality, and weight hypotheses are carried as a
certificate at this algebraic layer.
-/
structure BipartiteTomitaState
    (Op : Type*) [Ring Op]
    (T : TomitaCommutantDatum Op) where
  /-- Global state/readout. -/
  eval : Op → ℂ

  /-- State/weight certificate. -/
  state_certificate : Prop

  /-- Certificate that the state is adapted to the Tomita pair. -/
  tomita_pair_certificate : Prop

/--
Accessible restriction backend.

This is the type-III-safe replacement for a universal partial trace.  Concrete
finite type-I models may instantiate it by a literal trace-out operation.
-/
structure AccessibleRestrictionDatum
    (Op : Type*) [Ring Op]
    (T : TomitaCommutantDatum Op) where
  /-- Restrict a doubled/global state to the observable algebra readout. -/
  restrict : BipartiteTomitaState Op T → Op → ℂ

  /-- Observable-domain predicate for the selected backend. -/
  observable_domain :
    ∀ _vac : BipartiteTomitaState Op T, Prop

  /-- Backend certificate: restriction, conditional expectation, weight, etc. -/
  restrictionCertificate : Prop

/--
Modular thermalization witness for an observer restricted to the visible
Tomita side.

The supplied witness says the restricted readout is a KMS state for the
packaged modular flow.
-/
structure ModularThermalizationWitness
    (Op : Type*) [Ring Op]
    (T : TomitaCommutantDatum Op) where
  /-- Modular/operator flow. -/
  flow : OperatorFlow Op

  /-- Inverse temperature. -/
  beta : ℝ

  /-- Restriction backend. -/
  restriction : AccessibleRestrictionDatum Op T

  /-- Restricted states are KMS for the flow. -/
  restriction_is_kms :
    ∀ vac : BipartiteTomitaState Op T,
      ∃ thermal : KMSState Op flow beta,
        thermal.state.eval = restriction.restrict vac

namespace ModularThermalizationWitness

variable {Op : Type*} [Ring Op]
variable {T : TomitaCommutantDatum Op}
variable (M : ModularThermalizationWitness Op T)

/-- A restricted observer state admits a KMS witness. -/
theorem observer_restriction_is_kms
    (vac : BipartiteTomitaState Op T) :
    ∃ thermal : KMSState Op M.flow M.beta,
      thermal.state.eval = M.restriction.restrict vac :=
  M.restriction_is_kms vac

end ModularThermalizationWitness

/--
Hawking/Unruh KMS readout datum.

This adds the geometric horizon/surface-gravity calibration to modular KMS
thermalization.  The calibration is a witness, not a theorem of topology alone.
-/
structure HawkingKMSReadoutDatum
    (Op : Type*) [Ring Op]
    (T : TomitaCommutantDatum Op) where
  /-- Modular KMS thermalization. -/
  thermalization : ModularThermalizationWitness Op T

  /-- Horizon surface gravity. -/
  surfaceGravity : ℝ

  /-- Positivity of surface gravity. -/
  surfaceGravity_pos :
    0 < surfaceGravity

  /-- Hawking inverse-temperature law in the chosen normalization. -/
  hawkingBetaLaw :
    thermalization.beta = (2 * Real.pi) / surfaceGravity

  /-- Geometric calibration: modular flow is the horizon/wedge flow. -/
  geometricHorizonFlow : Prop

  /-- Radiation interpretation certificate. -/
  radiationInterpretation : Prop

namespace HawkingKMSReadoutDatum

variable {Op : Type*} [Ring Op]
variable {T : TomitaCommutantDatum Op}
variable (H : HawkingKMSReadoutDatum Op T)

/-- The observer restriction has a KMS state before applying the horizon interpretation. -/
theorem observer_restriction_is_kms
    (vac : BipartiteTomitaState Op T) :
    ∃ thermal : KMSState Op H.thermalization.flow H.thermalization.beta,
      thermal.state.eval = H.thermalization.restriction.restrict vac :=
  H.thermalization.observer_restriction_is_kms vac

end HawkingKMSReadoutDatum

/-! ## 7. Kleinian twist compatibility socket -/

/--
Compatibility between the Kleinian/Tomita twist and modular thermodynamics.

The twist says how the observable algebra is mirrored into the commutant; the
KMS datum says the restricted observable state is thermal for the modular flow.
-/
structure KleinianThermodynamicCompatibility
    (Op : Type*) [Ring Op] where
  /-- Observable/commutant Tomita-Cartan data. -/
  tomita_cartan : Prop

  /-- Non-orientable or projective boundary twist certificate. -/
  kleinian_twist : Prop

  /-- Modular KMS thermodynamics. -/
  modular_thermodynamics :
    ModularKMSDatum Op

  /--
  Compatibility certificate saying that the twist and KMS flow are the same
  physical boundary mechanism in the concrete model.
  -/
  compatibility : Prop

/-! ## 8. Owner targets -/

/-- Owner target for modular thermodynamics. -/
def ModularThermodynamicsOwnerTarget
    (Op : Type*) [Mul Op] : Prop :=
  Nonempty (ModularKMSDatum Op)

/-- Owner target for calibrated horizon thermality. -/
def EmergentThermalRadiationOwnerTarget
    (Op : Type*) [Mul Op] : Prop :=
  Nonempty (EmergentThermalRadiation Op)

/--
Compatibility data sufficient to construct a Tomita/KMS thermalization witness.

A concrete theorem needs a von Neumann algebra representation, cyclic and
separating state/vector, modular automorphism group, and a valid observer
reduction backend.
-/
structure TomitaKMSThermalizationCompatibility
    (Op : Type*) [Ring Op]
    (T : TomitaCommutantDatum Op)
    (σ : OperatorFlow Op)
    (beta : ℝ) where
  /-- Supplied thermalization witness. -/
  witness :
    TomitaKMSThermalization Op T σ beta

/-- Owner target for the modular KMS theorem interface. -/
def TomitaKMSThermalizationOwnerTarget : Prop :=
  ∀ (Op : Type*) [Ring Op],
  ∀ (T : TomitaCommutantDatum Op),
  ∀ (σ : OperatorFlow Op),
  ∀ (beta : ℝ),
    TomitaKMSThermalizationCompatibility Op T σ beta →
      Nonempty (TomitaKMSThermalization Op T σ beta)

/--
The modular KMS owner target is constructible once compatibility supplies the
thermalization witness.
-/
theorem tomitaKMSThermalizationOwnerTarget :
    TomitaKMSThermalizationOwnerTarget := by
  intro Op _ T σ beta h
  exact ⟨h.witness⟩

/--
Compatibility data sufficient to construct a horizon/Hawking/Unruh KMS bridge.

A concrete theorem must supply geometric modular-flow identification: Rindler
boosts, Killing horizon, Hartle-Hawking state, or an analogous horizon modular
localization theorem.
-/
structure HorizonKMSThermodynamicsCompatibility
    (Op : Type*) [Ring Op]
    (T : TomitaCommutantDatum Op)
    (σ : OperatorFlow Op)
    (beta : ℝ) where
  /-- Supplied horizon thermodynamics witness. -/
  witness :
    HorizonKMSThermodynamics Op T σ beta

/-- Owner target for the horizon/KMS thermodynamic bridge. -/
def HorizonKMSThermodynamicsOwnerTarget : Prop :=
  ∀ (Op : Type*) [Ring Op],
  ∀ (T : TomitaCommutantDatum Op),
  ∀ (σ : OperatorFlow Op),
  ∀ (beta : ℝ),
    HorizonKMSThermodynamicsCompatibility Op T σ beta →
      Nonempty (HorizonKMSThermodynamics Op T σ beta)

/--
The horizon KMS owner target is constructible once compatibility supplies the
horizon thermodynamics witness.
-/
theorem horizonKMSThermodynamicsOwnerTarget :
    HorizonKMSThermodynamicsOwnerTarget := by
  intro Op _ T σ beta h
  exact ⟨h.witness⟩

end InfoGeometry.OperatorAlgebra.OperatorThermodynamics

namespace InfoGeometry.OperatorAlgebra.Thermodynamics

open InfoGeometry.OperatorAlgebra.TomitaCartanSplit

/-! ## 1. Flows and states -/

/--
A real one-parameter flow on an operator algebra.

In concrete Tomita-Takesaki applications this is the modular automorphism flow
`sigma_t(A) = Delta^{it} A Delta^{-it}`.
-/
structure FlowDatum
    (Op : Type*) where
  /-- Time-parametrized flow. -/
  flow : ℝ → Op → Op

  /-- Time zero is the identity. -/
  flow_zero :
    ∀ x : Op, flow 0 x = x

  /-- Additive flow law. -/
  flow_add :
    ∀ s t x, flow (s + t) x = flow s (flow t x)

namespace FlowDatum

variable {Op : Type*}
variable (σ : FlowDatum Op)

@[simp]
theorem flow_zero_apply
    (x : Op) :
    σ.flow 0 x = x :=
  σ.flow_zero x

theorem flow_add_apply
    (s t : ℝ)
    (x : Op) :
    σ.flow (s + t) x = σ.flow s (σ.flow t x) :=
  σ.flow_add s t x

end FlowDatum

/-! ## 1b. Ring-level modular automorphism flow -/

/--
A one-parameter automorphism-like flow on an operator algebra.

At this roadmap layer, the flow is recorded algebraically.  Concrete modules
may strengthen this with continuity, normality, strong continuity, or von
Neumann algebra automorphism data.
-/
structure ModularFlow
    (Op : Type*) [Ring Op] where
  /-- Modular time evolution. -/
  flow : ℝ → Op ≃+* Op

  /-- Time zero is the identity. -/
  flow_zero :
    ∀ A : Op, flow 0 A = A

  /-- Additive flow law. -/
  flow_add :
    ∀ s t A, flow (s + t) A = flow s (flow t A)

namespace ModularFlow

variable {Op : Type*} [Ring Op]
variable (σ : ModularFlow Op)

@[simp]
theorem flow_zero_apply
    (A : Op) :
    σ.flow 0 A = A :=
  σ.flow_zero A

theorem flow_add_apply
    (s t : ℝ)
    (A : Op) :
    σ.flow (s + t) A = σ.flow s (σ.flow t A) :=
  σ.flow_add s t A

theorem flow_mul_apply
    (t : ℝ)
    (A B : Op) :
    σ.flow t (A * B) = σ.flow t A * σ.flow t B :=
  (σ.flow t).map_mul A B

/-- Forget the multiplicative law and regard a modular flow as a plain flow datum. -/
def toFlowDatum :
    FlowDatum Op where
  flow := fun t A => σ.flow t A
  flow_zero := σ.flow_zero
  flow_add := σ.flow_add

end ModularFlow

/--
A complex-valued state/readout on an operator algebra.

Positivity, normality, and normalization are proof fields because their exact
shape depends on the concrete algebraic category.
-/
structure StateFunctional
    (Op : Type*) where
  /-- Complex-valued state/readout. -/
  eval : Op → ℂ

  /-- Positivity certificate. -/
  positive : Prop

  /-- Normalization certificate. -/
  normalized : Prop

  /-- Normality certificate. -/
  normality : Prop

/-! ## 2. KMS condition -/

/--
A proof-carrying KMS analytic certificate.

The true KMS condition is an analytic strip-boundary condition.  This algebraic
layer records it as named data, not as an automatically true proposition.
-/
structure KMSAnalyticCertificate
    {Op : Type*}
    (σ : FlowDatum Op)
    (β : ℝ)
    (ω : StateFunctional Op) where
  /--
  Analytic strip-boundary statement, morally:
  `F(t) = omega(A * sigma_t(B))` and
  `F(t + i beta) = omega(sigma_t(B) * A)`.
  -/
  boundaryCondition : Prop

  /-- Certificate that the boundary condition holds. -/
  boundaryCondition_holds :
    boundaryCondition

/-- A KMS state for a given flow and inverse temperature. -/
structure KMSState
    (Op : Type*)
    (σ : FlowDatum Op)
    (β : ℝ) where
  /-- Underlying state/readout. -/
  state : StateFunctional Op

  /-- Invariance under real modular/thermal time. -/
  flow_invariant :
    ∀ t : ℝ, ∀ A : Op,
      state.eval (σ.flow t A) = state.eval A

  /-- Analytic KMS strip-boundary condition. -/
  kms :
    KMSAnalyticCertificate σ β state

namespace KMSState

variable {Op : Type*} {σ : FlowDatum Op} {β : ℝ}
variable (ω : KMSState Op σ β)

/-- Re-export real-time invariance. -/
theorem flow_invariant_apply
    (t : ℝ)
    (A : Op) :
    ω.state.eval (σ.flow t A) = ω.state.eval A :=
  ω.flow_invariant t A

/-- Re-export the KMS boundary condition. -/
theorem kms_boundary_holds :
    ω.kms.boundaryCondition :=
  ω.kms.boundaryCondition_holds

end KMSState

/-! ## 2b. KMS boundary for ring-level modular flows -/

/--
Proof-carrying KMS boundary predicate for a concrete evaluation functional and
a ring-level modular flow.

The true analytic content is supplied as evidence, not inferred from the
ambient algebraic data.
-/
structure KMSAnalyticBoundary
    {Op : Type*} [Ring Op]
    (_eval : Op → ℂ)
    (_σ : ModularFlow Op)
    (_β : ℝ) where
  /-- Analytic strip-boundary statement for the supplied readout and flow. -/
  boundaryCondition : Prop

  /-- Evidence that the boundary condition holds. -/
  boundaryCondition_holds :
    boundaryCondition

/-! ## 3. Tomita-KMS datum -/

/--
Tomita-KMS datum.

This is the abstract socket for the Tomita-Takesaki theorem: a faithful normal
state is KMS with respect to its modular automorphism group.  The analytic
theorem itself is supplied here as the `kms` certificate.
-/
structure TomitaKMSDatum
    (Op : Type*) where
  /-- The modular state/readout. -/
  state : StateFunctional Op

  /-- The modular flow. -/
  modularFlow : FlowDatum Op

  /-- Inverse temperature normalization, usually `1` for modular time. -/
  beta : ℝ

  /-- Faithful-normal certificate. -/
  faithfulNormal : Prop

  /-- Certificate that `modularFlow` is the Tomita-Takesaki modular flow. -/
  tomitaModularFlow : Prop

  /-- State invariance under real modular time. -/
  modular_invariant :
    ∀ t : ℝ, ∀ A : Op,
      state.eval (modularFlow.flow t A) = state.eval A

  /-- KMS analytic certificate. -/
  kms :
    KMSAnalyticCertificate modularFlow beta state

namespace TomitaKMSDatum

variable {Op : Type*}
variable (T : TomitaKMSDatum Op)

/-- Tomita-KMS data produce a KMS state. -/
def toKMSState :
    KMSState Op T.modularFlow T.beta where
  state := T.state
  flow_invariant := T.modular_invariant
  kms := T.kms

@[simp]
theorem toKMSState_eval
    (A : Op) :
    T.toKMSState.state.eval A = T.state.eval A :=
  rfl

theorem toKMSState_is_KMS :
    T.toKMSState.kms.boundaryCondition :=
  KMSState.kms_boundary_holds T.toKMSState

end TomitaKMSDatum

/-! ## 4. Observable restriction instead of type-III partial trace -/

/--
Restriction of a global state/readout to an observable algebra.

This is the type-III-safe replacement for the informal phrase "trace out the
commutant."  In type I finite-dimensional situations, a separate module may
instantiate this restriction by an actual partial trace.
-/
structure ObservableRestrictionDatum
    (Global Visible : Type*) where
  /-- Embedding of visible observables into the global carrier. -/
  embedVisible : Visible → Global

  /-- Global state/readout. -/
  globalState : StateFunctional Global

  /-- Visible restricted state/readout. -/
  visibleState : StateFunctional Visible

  /-- The visible state is the restriction of the global state. -/
  visible_eq_restriction :
    ∀ A : Visible,
      visibleState.eval A = globalState.eval (embedVisible A)

  /-- Certificate that the hidden/commutant sector is inaccessible to the observer. -/
  hiddenSectorInaccessible : Prop

namespace ObservableRestrictionDatum

variable {Global Visible : Type*}
variable (R : ObservableRestrictionDatum Global Visible)

/-- Re-export visible evaluation as restricted global evaluation. -/
theorem visible_eval_eq_global_eval
    (A : Visible) :
    R.visibleState.eval A = R.globalState.eval (R.embedVisible A) :=
  R.visible_eq_restriction A

end ObservableRestrictionDatum

/-! ## 4b. Tomita observer reduction instead of bare partial trace -/

/--
Observer reduction from a global algebraic state to the observable algebra
side of a Tomita pair.

In finite bipartite systems this may be implemented by a partial trace.  In
type III/Tomita settings it should be understood as restriction or modular
reduction to the observable algebra, not as a bare trace over a tensor factor.
-/
structure ObserverReduction
    (Op : Type*) [Ring Op]
    (T : TomitaCommutantDatum Op) where
  /-- Global state/expectation readout. -/
  globalEval : Op → ℂ

  /-- Local observer readout on the observable algebra. -/
  observableEval : Op → ℂ

  /-- On observable elements, the local readout agrees with the global readout. -/
  agrees_on_observable :
    ∀ A : Op, A ∈ T.M → observableEval A = globalEval A

  /-- Law: the commutant is inaccessible to the local observer. -/
  commutant_inaccessible_law : Prop

  /-- Evidence that the commutant is inaccessible to the local observer. -/
  commutant_inaccessible :
    commutant_inaccessible_law

  /--
  Law that the reduction is implemented by the selected backend:
  finite partial trace, restriction, conditional expectation, modular weight,
  or core trace.
  -/
  reduction_backend_law : Prop

  /-- Evidence for the selected reduction backend law. -/
  reduction_backend_valid :
    reduction_backend_law

namespace ObserverReduction

variable {Op : Type*} [Ring Op]
variable {T : TomitaCommutantDatum Op}
variable (R : ObserverReduction Op T)

/-- Re-export agreement of the observer readout with the global readout on `M`. -/
theorem observable_agrees
    {A : Op}
    (hA : A ∈ T.M) :
    R.observableEval A = R.globalEval A :=
  R.agrees_on_observable A hA

end ObserverReduction

/--
Witness that an observer reduction is thermal with respect to a modular flow.

This is the precise replacement for the slogan "tracing out the commutant
gives a thermal state."  The finite-dimensional phrase "partial trace" is not
built into the theorem.
-/
structure TomitaKMSThermalization
    (Op : Type*) [Ring Op]
    (T : TomitaCommutantDatum Op)
    (σ : ModularFlow Op)
    (β : ℝ) where
  /-- Observer reduction/restriction. -/
  reduction :
    ObserverReduction Op T

  /-- The thermal/KMS state seen by the local observer. -/
  thermal :
    KMSState Op σ.toFlowDatum β

  /-- The thermal state is exactly the reduced observer state. -/
  thermal_eq_reduction :
    ∀ A : Op, thermal.state.eval A = reduction.observableEval A

  /-- Law that the modular flow is the Tomita flow of the pair/state. -/
  modular_origin_law : Prop

  /-- Evidence that the modular flow is the Tomita flow of the pair/state. -/
  modular_origin :
    modular_origin_law

  /-- Optional geometric/horizon law, e.g. wedge or Killing horizon data. -/
  horizon_or_wedge_origin_law : Prop

  /-- Evidence for the optional geometric/horizon law. -/
  horizon_or_wedge_origin :
    horizon_or_wedge_origin_law

namespace TomitaKMSThermalization

variable {Op : Type*} [Ring Op]
variable {T : TomitaCommutantDatum Op}
variable {σ : ModularFlow Op}
variable {β : ℝ}
variable (Θ : TomitaKMSThermalization Op T σ β)

/-- The observer-reduced state is represented by a KMS state. -/
theorem exists_kms_state_for_observer :
    ∃ ω : KMSState Op σ.toFlowDatum β,
      ω.state.eval = Θ.reduction.observableEval := by
  refine ⟨Θ.thermal, ?_⟩
  funext A
  exact Θ.thermal_eq_reduction A

/-- The observer-reduced state carries the named KMS boundary certificate. -/
def reduced_state_is_kms :
    KMSAnalyticBoundary Θ.reduction.observableEval σ β where
  boundaryCondition := Θ.thermal.kms.boundaryCondition
  boundaryCondition_holds := Θ.thermal.kms.boundaryCondition_holds

/-- The local observer's readout is invariant under real modular time. -/
theorem reduced_state_flow_invariant
    (t : ℝ)
    (A : Op) :
    Θ.reduction.observableEval (σ.flow t A) =
      Θ.reduction.observableEval A := by
  calc
    Θ.reduction.observableEval (σ.flow t A)
        = Θ.thermal.state.eval (σ.flow t A) := by
            rw [← Θ.thermal_eq_reduction]
    _ = Θ.thermal.state.eval A := by
            simpa [ModularFlow.toFlowDatum] using
              Θ.thermal.flow_invariant_apply t A
    _ = Θ.reduction.observableEval A :=
            Θ.thermal_eq_reduction A

/-- On observable algebra elements, the thermal KMS state agrees with the global state. -/
theorem thermal_agrees_with_global_on_observable
    {A : Op}
    (hA : A ∈ T.M) :
    Θ.thermal.state.eval A = Θ.reduction.globalEval A := by
  calc
    Θ.thermal.state.eval A
        = Θ.reduction.observableEval A :=
            Θ.thermal_eq_reduction A
    _ = Θ.reduction.globalEval A :=
            Θ.reduction.observable_agrees hA

end TomitaKMSThermalization

/--
A horizon or topological boundary that routes observable degrees of freedom
toward the commutant.

The boundary/twist does not by itself create a KMS state; it supplies geometric
partition data to which a modular thermalization witness may be applied.
-/
structure HorizonCommutantBoundary
    (Op : Type*) [Ring Op]
    (T : TomitaCommutantDatum Op) where
  /-- Boundary map/readout. -/
  boundary : Op → Op

  /-- Observable elements hitting the boundary are routed to the commutant. -/
  boundary_maps_observable_to_commutant :
    ∀ A : Op, A ∈ T.M → boundary A ∈ T.Mcomm

  /-- Law saying this boundary is the intended Drazin/null/horizon locus. -/
  boundary_is_defect_locus_law : Prop

  /-- Evidence that this boundary is the intended Drazin/null/horizon locus. -/
  boundary_is_defect_locus :
    boundary_is_defect_locus_law

/--
Full thermodynamic horizon witness:

Tomita algebra/commutant routing, horizon boundary, observer reduction, and KMS
thermalization of the reduced state.
-/
structure HorizonKMSThermodynamics
    (Op : Type*) [Ring Op]
    (T : TomitaCommutantDatum Op)
    (σ : ModularFlow Op)
    (β : ℝ) where
  /-- Boundary routing observables toward the commutant. -/
  boundary :
    HorizonCommutantBoundary Op T

  /-- KMS thermalization of the reduced observer state. -/
  thermalization :
    TomitaKMSThermalization Op T σ β

namespace HorizonKMSThermodynamics

variable {Op : Type*} [Ring Op]
variable {T : TomitaCommutantDatum Op}
variable {σ : ModularFlow Op}
variable {β : ℝ}
variable (H : HorizonKMSThermodynamics Op T σ β)

/-- Boundary-routed observable data lands in the commutant sector. -/
theorem observable_boundary_in_commutant
    {A : Op}
    (hA : A ∈ T.M) :
    H.boundary.boundary A ∈ T.Mcomm :=
  H.boundary.boundary_maps_observable_to_commutant A hA

/-- The local observer sees a KMS state. -/
theorem observer_sees_kms :
    ∃ ω : KMSState Op σ.toFlowDatum β,
      ω.state.eval = H.thermalization.reduction.observableEval :=
  H.thermalization.exists_kms_state_for_observer

/-- The reduced observer state carries a KMS boundary certificate. -/
def reduced_state_is_kms :
    KMSAnalyticBoundary
      H.thermalization.reduction.observableEval σ β :=
  H.thermalization.reduced_state_is_kms

end HorizonKMSThermodynamics

/-! ## 5. Thermodynamic emergence across an observable/commutant split -/

/--
Thermalization witness for an observer restricted to the visible algebra.

The state seen by the observer is KMS with respect to the visible modular flow.
This replaces the heuristic "tracing out the commutant produces a thermal
state."
-/
structure ObservableKMSReduction
    (Global Visible : Type*) where
  /-- Observable restriction. -/
  restriction :
    ObservableRestrictionDatum Global Visible

  /-- Visible modular flow. -/
  visibleFlow :
    FlowDatum Visible

  /-- Inverse temperature. -/
  beta :
    ℝ

  /-- KMS witness for the visible state. -/
  visibleKMS :
    KMSState Visible visibleFlow beta

  /-- The KMS state is the restricted visible state. -/
  kms_eval_eq_visible :
    ∀ A : Visible,
      visibleKMS.state.eval A =
        restriction.visibleState.eval A

  /-- Modular/Tomita interpretation of the reduction. -/
  tomitaReductionCertificate : Prop

namespace ObservableKMSReduction

variable {Global Visible : Type*}
variable (R : ObservableKMSReduction Global Visible)

/-- The restricted visible state is KMS. -/
theorem restricted_state_is_KMS :
    R.visibleKMS.kms.boundaryCondition :=
  KMSState.kms_boundary_holds R.visibleKMS

/-- The KMS readout agrees with the visible restriction. -/
theorem thermal_eval_eq_restricted_eval
    (A : Visible) :
    R.visibleKMS.state.eval A =
      R.restriction.visibleState.eval A :=
  R.kms_eval_eq_visible A

/-- The visible thermal readout agrees with the restricted global readout. -/
theorem thermal_eval_eq_global_visible_eval
    (A : Visible) :
    R.visibleKMS.state.eval A =
      R.restriction.globalState.eval (R.restriction.embedVisible A) := by
  rw [R.thermal_eval_eq_restricted_eval A]
  exact R.restriction.visible_eval_eq_global_eval A

end ObservableKMSReduction

/-! ## 6. Horizon/Hawking-Unruh calibration socket -/

/--
Geometric calibration turning modular KMS thermality into a Hawking/Unruh
readout.

This is not automatic from the algebraic KMS state alone.  It requires a
geometric statement identifying modular time with physical horizon or wedge
time.
-/
structure HorizonThermalCalibration
    (Visible : Type*) where
  /-- Physical inverse temperature. -/
  betaPhysical : ℝ

  /-- Certificate that modular flow is physical horizon/wedge time. -/
  modularFlow_is_horizon_time : Prop

  /-- Certificate that the KMS state is interpreted as Hawking/Unruh radiation. -/
  KMS_is_hawking_unruh_readout : Prop

/-- A Hawking/Unruh branch is visible KMS reduction plus geometric calibration. -/
structure HawkingUnruhBranch
    (Global Visible : Type*) where
  /-- Visible KMS reduction. -/
  reduction :
    ObservableKMSReduction Global Visible

  /-- Horizon/wedge calibration. -/
  calibration :
    HorizonThermalCalibration Visible

  /-- The reduction temperature agrees with the calibrated physical temperature. -/
  beta_matches :
    reduction.beta = calibration.betaPhysical

namespace HawkingUnruhBranch

variable {Global Visible : Type*}
variable (H : HawkingUnruhBranch Global Visible)

/-- The observer sees a KMS state. -/
theorem observer_state_is_KMS :
    H.reduction.visibleKMS.kms.boundaryCondition :=
  H.reduction.restricted_state_is_KMS

/-- The observer thermal readout is the restricted global readout. -/
theorem observer_thermal_eval_eq_global_visible_eval
    (A : Visible) :
    H.reduction.visibleKMS.state.eval A =
      H.reduction.restriction.globalState.eval
        (H.reduction.restriction.embedVisible A) :=
  H.reduction.thermal_eval_eq_global_visible_eval A

end HawkingUnruhBranch

/-! ## 7. Optional type-I partial trace socket -/

/--
A type-I/tensor-factor partial trace datum.

This is deliberately separate from the type-III-safe observable restriction
above.  Use this only when a concrete tensor-factor model is available.
-/
structure TypeIPartialTraceDatum
    (Global Visible Hidden : Type*) where
  /-- Partial trace over the hidden factor. -/
  partialTraceHidden :
    StateFunctional Global → StateFunctional Visible

  /-- Certificate that this is the ordinary type-I partial trace over `Hidden`. -/
  isTypeIPartialTrace : Prop

/-! ## 8. Owner targets -/

/-- Owner target: Tomita-KMS data produce a KMS state. -/
def TomitaKMSOwnerTarget : Prop :=
  ∀ Op : Type*,
  ∀ T : TomitaKMSDatum Op,
    Nonempty (KMSState Op T.modularFlow T.beta)

/-- The Tomita-KMS owner target is constructible from the supplied certificate. -/
theorem tomitaKMSOwnerTarget :
    TomitaKMSOwnerTarget := by
  intro Op T
  exact ⟨T.toKMSState⟩

/--
Owner target: an observable KMS reduction gives thermal readouts on the visible
algebra.
-/
def ObservableKMSReductionOwnerTarget : Prop :=
  ∀ Global Visible : Type*,
  ∀ R : ObservableKMSReduction Global Visible,
    R.visibleKMS.kms.boundaryCondition ∧
    ∀ A : Visible,
      R.visibleKMS.state.eval A =
        R.restriction.globalState.eval (R.restriction.embedVisible A)

/-- The observable KMS reduction owner target follows from the witness. -/
theorem observableKMSReductionOwnerTarget :
    ObservableKMSReductionOwnerTarget := by
  intro Global Visible R
  exact ⟨
    R.restricted_state_is_KMS,
    fun A => R.thermal_eval_eq_global_visible_eval A
  ⟩

/-! ## 9. Tomita/horizon owner targets -/

/--
Compatibility data sufficient to construct a Tomita/KMS thermalization witness.

A concrete theorem needs a von Neumann algebra representation, cyclic and
separating state/vector, modular automorphism group, and a valid observer
reduction backend.
-/
structure TomitaKMSThermalizationCompatibility
    (Op : Type*) [Ring Op]
    (T : TomitaCommutantDatum Op)
    (σ : ModularFlow Op)
    (β : ℝ) where
  /-- Supplied thermalization witness. -/
  witness :
    TomitaKMSThermalization Op T σ β

/-- Owner target for the modular KMS theorem interface. -/
def TomitaKMSThermalizationOwnerTarget : Prop :=
  ∀ (Op : Type*) [Ring Op],
  ∀ (T : TomitaCommutantDatum Op),
  ∀ (σ : ModularFlow Op),
  ∀ (β : ℝ),
    TomitaKMSThermalizationCompatibility Op T σ β →
      Nonempty (TomitaKMSThermalization Op T σ β)

/--
The modular KMS owner target is constructible once compatibility supplies the
thermalization witness.
-/
theorem tomitaKMSThermalizationOwnerTarget :
    TomitaKMSThermalizationOwnerTarget := by
  intro Op _ T σ β h
  exact ⟨h.witness⟩

/--
Compatibility data sufficient to construct a horizon/Hawking/Unruh KMS bridge.

A concrete theorem must supply geometric modular-flow identification: Rindler
boosts, Killing horizon, Hartle-Hawking state, or an analogous horizon modular
localization theorem.
-/
structure HorizonKMSThermodynamicsCompatibility
    (Op : Type*) [Ring Op]
    (T : TomitaCommutantDatum Op)
    (σ : ModularFlow Op)
    (β : ℝ) where
  /-- Supplied horizon thermodynamics witness. -/
  witness :
    HorizonKMSThermodynamics Op T σ β

/-- Owner target for the horizon/KMS thermodynamic bridge. -/
def HorizonKMSThermodynamicsOwnerTarget : Prop :=
  ∀ (Op : Type*) [Ring Op],
  ∀ (T : TomitaCommutantDatum Op),
  ∀ (σ : ModularFlow Op),
  ∀ (β : ℝ),
    HorizonKMSThermodynamicsCompatibility Op T σ β →
      Nonempty (HorizonKMSThermodynamics Op T σ β)

/--
The horizon KMS owner target is constructible once compatibility supplies the
horizon thermodynamics witness.
-/
theorem horizonKMSThermodynamicsOwnerTarget :
    HorizonKMSThermodynamicsOwnerTarget := by
  intro Op _ T σ β h
  exact ⟨h.witness⟩

end InfoGeometry.OperatorAlgebra.Thermodynamics
