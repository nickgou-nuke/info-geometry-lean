import InfoGeometry.Canonical.BerryConnection
import InfoGeometry.Canonical.NoetherInference
import InfoGeometry.Canonical.OnsagerSpineBridge
import InfoGeometry.Canonical.ThermodynamicGenerator

open scoped InnerProductSpace

/-!
# InfoGeometry.Canonical.OperatorSuperKaehlerLift

Thin operatorial lift of the finite Souriau/Massieu shadow.

This file does not assert a new geometry. It packages the maintained operator
owners already present in the canonical trunk:

- operatorial grand-canonical Massieu/log-generating potentials;
- symmetric Onsager Hessian response and skew Casimir response;
- `K = Jε` phase-as-metric-twist response;
- the super-Hestenes-Kaehler compatibility datum on the doubled carrier;
- the Noether/Fisher readout equality with the relational Krein channel metric.

Finite count thermodynamics remains a shadow. The owner lane here is the
operator algebra on `DoubledSpace E`.
-/

namespace InfoGeometry.Canonical.OperatorSuperKaehlerLift

open InfoGeometry.Canonical.BerryPhase
open InfoGeometry.Canonical.NoetherInference
open InfoGeometry.Canonical.OnsagerReciprocity
open InfoGeometry.Canonical.RelationalInformationDynamics
open InfoGeometry.Canonical.ThermodynamicGenerator
open InfoGeometry.Canonical.RelativeModularPotential
open InfoGeometry.Krein
open InfoGeometry.Quantum

section Core

variable {E : Type 0}
variable [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

local notation "H₂" => DoubledSpace E
local notation "EndH" => H₂ →L[ℝ] H₂
local notation "Chan" => InfoGeometry.Canonical.RelationalInformationCore.PerturbationChannel E

noncomputable local instance : NormedRing EndH := inferInstance
noncomputable local instance : NormedAlgebra ℝ EndH := inferInstance
noncomputable local instance : NormedSpace ℝ EndH := inferInstance
local instance : IsTopologicalRing EndH := inferInstance
local instance : CompleteSpace EndH := inferInstance

/--
Operatorial super-Kaehler Massieu packet.

`H` is the operator seed, `N` is supplied by the Bogoliubov/Fock
grand-canonical generator inside `ThermodynamicGenerator`, and `μ` is the
chemical-potential coordinate in that operator generator.
-/
@[rep_depth krein]
structure OperatorSuperKaehlerMassieuPacket where
  hestenes : SuperHestenesKaehlerDatum (E := E)
  potential : PotentialDatum (E := E)
  mixing : InfoGeometry.Canonical.BogoliubovFockSuper.HyperbolicMixingParams
  observable : EndH
  chemicalPotential : ℝ

/-- Operatorial grand-canonical generator carried by the packet. -/
@[rep_depth krein]
noncomputable def massieuGenerator
    (Ω : OperatorSuperKaehlerMassieuPacket (E := E)) : EndH :=
  operatorialGrandCanonicalGenerator (E := E)
    Ω.mixing Ω.observable Ω.chemicalPotential

/-- Operatorial Massieu/log-generating potential carried by the packet. -/
@[rep_depth krein]
noncomputable def massieuPotential
    (ω : EndH →L[ℝ] ℝ)
    (Ω : OperatorSuperKaehlerMassieuPacket (E := E)) : ℝ → ℝ :=
  operatorialGrandCanonicalMassieuPotential (E := E) ω
    Ω.mixing Ω.observable Ω.chemicalPotential

/-- Primitive operatorial expectation conjugate to the Massieu potential. -/
@[rep_depth krein]
noncomputable def massieuExpectation
    (ω : EndH →L[ℝ] ℝ)
    (Ω : OperatorSuperKaehlerMassieuPacket (E := E)) : ℝ :=
  operatorialGrandCanonicalMassieuExpectation ω
    Ω.mixing Ω.observable Ω.chemicalPotential

@[rep_depth krein, simp]
theorem massieuPotential_eq_operatorMassieuPotential
    (ω : EndH →L[ℝ] ℝ)
    (Ω : OperatorSuperKaehlerMassieuPacket (E := E)) :
    massieuPotential (E := E) ω Ω
      =
    operatorMassieuPotential (E := E) ω (massieuGenerator (E := E) Ω) := by
  rfl

@[rep_depth krein]
theorem massieuPotential_normalizedInfinitesimalLaw
    (ω : EndH →L[ℝ] ℝ)
    (Ω : OperatorSuperKaehlerMassieuPacket (E := E))
    (hω1 : ω (1 : EndH) = 1) :
    HasDerivAt
      (massieuPotential (E := E) ω Ω)
      (massieuExpectation ω Ω) 0 := by
  exact operatorialGrandCanonicalMassieuPotential_normalizedInfinitesimalLaw
    (E := E) (ω := ω) (hω1 := hω1)
    (B := Ω.mixing) (H := Ω.observable) (μ := Ω.chemicalPotential)

/-- Symmetric operatorial Onsager/Souriau Hessian response from the packet. -/
@[rep_depth transport]
noncomputable def metricResponse
    (Ω : OperatorSuperKaehlerMassieuPacket (E := E)) :
    LinearMap.BilinForm ℝ Chan :=
  operatorMetricHessianForm (E := E) Ω.potential (massieuGenerator (E := E) Ω)

/-- Skew operatorial Casimir/curvature response from the packet. -/
@[rep_depth transport]
noncomputable def curvatureResponse
    (Ω : OperatorSuperKaehlerMassieuPacket (E := E)) :
    LinearMap.BilinForm ℝ Chan :=
  operatorCurvatureHessianForm (E := E) Ω.potential (massieuGenerator (E := E) Ω)

/-- `K = Jε`-twisted phase response from the packet. -/
@[rep_depth transport]
noncomputable def phaseResponse
    (Ω : OperatorSuperKaehlerMassieuPacket (E := E)) :
    LinearMap.BilinForm ℝ Chan :=
  operatorPhaseHessianForm (E := E) Ω.potential (massieuGenerator (E := E) Ω)

@[rep_depth transport]
theorem metricResponse_swap
    (Ω : OperatorSuperKaehlerMassieuPacket (E := E)) (X Y : Chan) :
    metricResponse (E := E) Ω X Y
      =
    metricResponse (E := E) Ω Y X := by
  exact operatorMetricHessianForm_swap
    (E := E) Ω.potential (massieuGenerator (E := E) Ω) X Y

@[rep_depth transport]
theorem curvatureResponse_swap_neg
    (Ω : OperatorSuperKaehlerMassieuPacket (E := E)) (X Y : Chan) :
    curvatureResponse (E := E) Ω Y X
      =
    -curvatureResponse (E := E) Ω X Y := by
  exact operatorCurvatureHessianForm_swap_neg
    (E := E) Ω.potential (massieuGenerator (E := E) Ω) X Y

@[rep_depth transport, simp]
theorem phaseResponse_eq_metric_comp_channelPhaseAxis
    (Ω : OperatorSuperKaehlerMassieuPacket (E := E)) :
    phaseResponse (E := E) Ω
      =
    (metricResponse (E := E) Ω).compLeft
      InfoGeometry.Canonical.RelationalInformationCore.channelPhaseAxis := by
  rfl

@[rep_depth transport, simp]
theorem phaseResponse_apply
    (Ω : OperatorSuperKaehlerMassieuPacket (E := E)) (X Y : Chan) :
    phaseResponse (E := E) Ω X Y
      =
    metricResponse (E := E) Ω
      (InfoGeometry.Canonical.RelationalInformationCore.channelPhaseAxis X) Y := by
  rfl

/--
The packet's Hestenes-Kaehler datum keeps the operator phase readout tied to
the `K = Jε` metric twist.
-/
@[rep_depth krein]
theorem hestenes_phase_eq_metric_K
    (Ω : OperatorSuperKaehlerMassieuPacket (E := E)) (u v : H₂) :
    Ω.hestenes.phase u v = Ω.hestenes.metric (Ω.hestenes.K u) v :=
  Ω.hestenes.compat u v

/--
The packet exposes the already-owned Fisher/Krein equality when the carrier is
finite-dimensional. This is a readout identification, not a new positivity
claim.
-/
@[rep_depth krein]
theorem fisher_readout_eq_channelKreinMetric
    [FiniteDimensional ℝ E]
    (v : H₂) (X Y : EndH) :
    InfoGeometry.Canonical.NoetherInference.fisherBilinAt (E := E) v X Y
      =
    channelKreinMetricAtState (E := E) v X Y :=
  by
    rw [fisherBilinAt_apply, channelKreinMetricAtState_apply]

/--
Canonical constructor from a Quantum Geometric Tensor `Q : QGT E` and a relative modular potential datum `P`.
Sets standard unmixed Bogoliubov mixing (`θ = 0`), observable `H`, and chemical potential `μ`.
-/
@[rep_depth krein]
noncomputable def ofQGTAndPotential
    (Q : QGT E)
    (P : PotentialDatum (E := E))
    (observable : EndH)
    (chemicalPotential : ℝ) :
    OperatorSuperKaehlerMassieuPacket (E := E) where
  hestenes := SuperHestenesKaehlerDatum.ofQGT Q
  potential := P
  mixing := InfoGeometry.Canonical.BogoliubovFockSuper.HyperbolicMixingParams.ofAngle 0
  observable := observable
  chemicalPotential := chemicalPotential

/--
Canonical vacuum constructor from explicit Hestenes datum and potential datum with zero observable and zero chemical potential.
-/
@[rep_depth krein]
noncomputable def ofCanonical
    (S : SuperHestenesKaehlerDatum (E := E))
    (P : PotentialDatum (E := E)) :
    OperatorSuperKaehlerMassieuPacket (E := E) where
  hestenes := S
  potential := P
  mixing := InfoGeometry.Canonical.BogoliubovFockSuper.HyperbolicMixingParams.ofAngle 0
  observable := 0
  chemicalPotential := 0

end Core

end InfoGeometry.Canonical.OperatorSuperKaehlerLift
