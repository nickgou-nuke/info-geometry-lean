import InfoGeometry.Canonical.SouriauCoadjointOrbitMetriplecticTheorem
import InfoGeometry.Canonical.UhlmannBuresHolonomy
import InfoGeometry.Volume.ConnesCocycle
import InfoGeometry.Meta.Architecture

/-!
# InfoGeometry.Canonical.CoordinatelessSouriauKMSBridge

Coordinate-free operator-algebraic Souriau/KMS bridge.

The prose claim "spacetime is not a background, but emerges from algebraic
states" is formalized here as a narrow interface:

- observables are doubled-carrier endomorphisms `AlgebraEnd H`;
- thermodynamic states are linear functionals on that algebra;
- KMS equilibrium is a relation with an additive modular automorphism flow;
- Souriau moments are operator-valued generators, not coordinate fields;
- the Bures/SLD metric is an explicitly supplied quantum Fisher packet;
- Weyl gauge is an algebra automorphism preserving the state;
- classical coordinates appear only through an explicit emergence/readout map.

No C*-algebra/von Neumann standard form is claimed here.  This module provides
the proof-carrying corridor that such a construction must instantiate.
-/

namespace InfoGeometry.Canonical.CoordinatelessSouriauKMSBridge

open InfoGeometry.Volume.ConnesCocycle

universe u v w

section OperatorAlgebra

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

local notation "Obs" => AlgebraEnd H

/--
Coordinate-free algebraic state on the observable algebra.

`positive` and `normalized` are kept as explicit predicates because the current
repo does not provide a full C*-positive cone for arbitrary `AlgebraEnd H`.
-/
@[rep_depth operator]
structure AlgebraicState where
  functional : Obs → ℝ
  positive : Prop
  normalized : functional 1 = 1

namespace AlgebraicState

/-- The `normalized` field states that the functional evaluated at the identity is `1`. -/

theorem normalized_eq_one (s : AlgebraicState (H := H)) : s.functional 1 = 1 :=
  s.normalized

variable (ω : AlgebraicState (H := H))

/-- Evaluation notation for the algebraic thermodynamic state. -/
@[rep_depth operator]
def eval (A : Obs) : ℝ :=
  ω.functional A

@[rep_depth operator]
theorem eval_one :
    ω.eval 1 = 1 :=
  ω.normalized

end AlgebraicState

/--
Cyclic algebraic state.

This is the constructive operator-algebraic replacement for trace prose in the
coordinateless corridor: cyclicity is the exact property needed to build the
trivial-modular KMS branch and to prove SLD/Fisher symmetry.
-/
@[rep_depth operator]
structure CyclicAlgebraicState where
  state : AlgebraicState (H := H)
  cyclic : ∀ A B : Obs, state.eval (A * B) = state.eval (B * A)

namespace CyclicAlgebraicState

variable (ω : CyclicAlgebraicState (H := H))

@[rep_depth operator]
theorem eval_mul_comm (A B : Obs) :
    ω.state.eval (A * B) = ω.state.eval (B * A) :=
  ω.cyclic A B

end CyclicAlgebraicState

/-- Identity modular flow on the observable algebra. -/
@[rep_depth operator]
def identityAdditiveModularFlow : AdditiveModularFlow (H := H) where
  toFun := fun _ => 1
  map_zero' := rfl
  map_add' := by
    intro s t
    simp

/--
KMS state relative to an additive modular automorphism flow.

The KMS identity is stated directly on observables:
`ω(A σ_β(B)) = ω(B A)`.
-/
@[rep_depth operator]
structure KMSState
    (σ : AdditiveModularFlow (H := H)) (beta : ℝ) where
  state : AlgebraicState (H := H)
  kms_identity : ∀ A B : Obs, state.eval (A * σ beta B) = state.eval (B * A)

namespace KMSState

variable {σ : AdditiveModularFlow (H := H)} {beta : ℝ}
variable (K : KMSState (H := H) σ beta)

/-- KMS equilibrium replaces local temperature fields by modular-time covariance. -/
@[rep_depth operator]
theorem eval_mul_modular_eq_eval_flip (A B : Obs) :
    K.state.eval (A * σ beta B) = K.state.eval (B * A) :=
  K.kms_identity A B

/-- The underlying state remains normalized. -/
@[rep_depth operator]
theorem state_eval_one :
    K.state.eval 1 = 1 :=
  K.state.eval_one

end KMSState

namespace CyclicAlgebraicState

variable (ω : CyclicAlgebraicState (H := H))

/--
Constructive KMS state on the identity modular branch.

No density matrix or trace is introduced: the proof is exactly cyclicity of the
algebraic state.
-/
@[rep_depth operator]
def toIdentityKMSState (beta : ℝ) :
    KMSState (H := H) (identityAdditiveModularFlow (H := H)) beta where
  state := ω.state
  kms_identity := by
    intro A B
    simpa [identityAdditiveModularFlow] using ω.cyclic A B

/-!
## Alias constructor for a generic KMS state

While the `toIdentityKMSState` constructor is sufficient for the identity
modular flow, downstream code often expects a more generically named theorem
`toKMSState`.  Providing this thin wrapper does not introduce any new hypothesis
or proof burden—it simply forwards to the existing construction.  This reduces
the explicit hypothesis surface by allowing callers to use `toKMSState` without
referring to the concrete flow name.
-/
@[rep_depth operator]
def toKMSState (beta : ℝ) :
    KMSState (H := H) (identityAdditiveModularFlow (H := H)) beta :=
  ω.toIdentityKMSState beta

@[rep_depth operator]
theorem identityKMS_eval_mul_modular_eq_eval_flip (beta : ℝ) (A B : Obs) :
    (ω.toIdentityKMSState beta).state.eval
        (A * (identityAdditiveModularFlow (H := H)) beta B) =
      (ω.toIdentityKMSState beta).state.eval (B * A) :=
  (ω.toIdentityKMSState beta).eval_mul_modular_eq_eval_flip A B

end CyclicAlgebraicState

/--
Operator-valued Souriau moment map.

The Lie/coadjoint data are represented by abstract labels; the actual
observable content is the map into `Obs`.
-/
@[rep_depth operator]
structure OperatorSouriauMoment (Symmetry : Type v) where
  momentOperator : Symmetry → Obs
  geometricTemperature : Symmetry

namespace OperatorSouriauMoment

variable {Symmetry : Type v}
variable (J : OperatorSouriauMoment (H := H) Symmetry)

/-- The Souriau generator selected by the geometric temperature. -/
@[rep_depth operator]
def thermalGenerator : Obs :=
  J.momentOperator J.geometricTemperature

@[rep_depth operator]
theorem thermalGenerator_eq_moment_geometricTemperature :
    J.thermalGenerator = J.momentOperator J.geometricTemperature := rfl

end OperatorSouriauMoment

/--
Coordinate-free quantum Fisher/Bures packet.

`sld` is the symmetric logarithmic derivative assignment.  The metric is kept as
data together with its SLD readout law through the algebraic state.
-/
@[rep_depth operator]
structure QuantumFisherSLDMetric
    (Tangent : Type w) (ω : AlgebraicState (H := H)) where
  sld : Tangent → Obs
  metric : Tangent → Tangent → ℝ
  metric_eq_sld_readout :
    ∀ X Y : Tangent, metric X Y = ω.eval ((sld X) * (sld Y))
  symmetric : ∀ X Y : Tangent, metric X Y = metric Y X

namespace QuantumFisherSLDMetric

variable {Tangent : Type w} {ω : AlgebraicState (H := H)}
variable (Q : QuantumFisherSLDMetric (H := H) Tangent ω)

/-- The Fisher/Bures metric is the SLD readout supplied by the state. -/
@[rep_depth operator]
theorem metric_eq_state_sld_product (X Y : Tangent) :
    Q.metric X Y = ω.eval ((Q.sld X) * (Q.sld Y)) :=
  Q.metric_eq_sld_readout X Y

/-- Onsager/Fisher reciprocity at the SLD metric layer. -/
@[rep_depth operator]
theorem metric_symm (X Y : Tangent) :
    Q.metric X Y = Q.metric Y X :=
  Q.symmetric X Y

end QuantumFisherSLDMetric

namespace CyclicAlgebraicState

variable {Tangent : Type w}
variable (ω : CyclicAlgebraicState (H := H))

/--
Construct the coordinate-free SLD/Fisher metric from a cyclic algebraic state.

The metric symmetry is not another hypothesis: it is derived from cyclicity.
-/
@[rep_depth operator]
def sldQuantumFisherMetric (sld : Tangent → Obs) :
    QuantumFisherSLDMetric (H := H) Tangent ω.state where
  sld := sld
  metric := fun X Y => ω.state.eval ((sld X) * (sld Y))
  metric_eq_sld_readout := by
    intro X Y
    rfl
  symmetric := by
    intro X Y
    exact ω.cyclic (sld X) (sld Y)

@[rep_depth operator]
theorem sldQuantumFisherMetric_symm
    (sld : Tangent → Obs) (X Y : Tangent) :
    (ω.sldQuantumFisherMetric sld).metric X Y =
      (ω.sldQuantumFisherMetric sld).metric Y X :=
  (ω.sldQuantumFisherMetric sld).metric_symm X Y

end CyclicAlgebraicState

/--
Weyl gauge as an automorphism of the observable algebra preserving the
algebraic state.
-/
@[rep_depth operator]
structure WeylAlgebraGauge (ω : AlgebraicState (H := H)) where
  gauge : Obs ≃ₐ[ℝ] Obs
  state_invariant : ∀ A : Obs, ω.eval (gauge A) = ω.eval A

namespace WeylAlgebraGauge

variable {ω : AlgebraicState (H := H)}
variable (W : WeylAlgebraGauge (H := H) ω)

/-- Weyl gauge invariance is state invariance under algebra automorphism. -/
@[rep_depth operator]
theorem eval_gauge_eq_eval (A : Obs) :
    ω.eval (W.gauge A) = ω.eval A :=
  W.state_invariant A

/-- The Weyl gauge preserves products because it is an algebra automorphism. -/
@[rep_depth operator]
theorem gauge_map_mul (A B : Obs) :
    W.gauge (A * B) = W.gauge A * W.gauge B :=
  map_mul W.gauge A B

end WeylAlgebraGauge

/-- The identity Weyl gauge is constructively state-preserving. -/
@[rep_depth operator]
def identityWeylAlgebraGauge (ω : AlgebraicState (H := H)) :
    WeylAlgebraGauge (H := H) ω where
  gauge := 1
  state_invariant := by
    intro A
    rfl

/--
Modular-time package for a KMS state.

This is the coordinate-free replacement for an external time coordinate: time is
the additive parameter of the modular automorphism group.
-/
@[rep_depth operator]
structure ModularTimeKMSContext where
  sigma : AdditiveModularFlow (H := H)
  beta : ℝ
  kms : KMSState (H := H) sigma beta

namespace ModularTimeKMSContext

variable (M : ModularTimeKMSContext (H := H))

/-- Modular time is additive: `σ_{s+t}=σ_s σ_t`. -/
@[rep_depth operator]
theorem modular_time_add (s t : ℝ) :
    M.sigma (s + t) = M.sigma s * M.sigma t :=
  AdditiveModularFlow.map_add M.sigma s t

/-- Modular time starts at the identity automorphism. -/
@[rep_depth operator]
theorem modular_time_zero :
    M.sigma 0 = 1 :=
  AdditiveModularFlow.map_zero M.sigma

/-- KMS identity expressed through the modular-time context. -/
@[rep_depth operator]
theorem kms_eval_mul_modular_eq_eval_flip (A B : Obs) :
    M.kms.state.eval (A * M.sigma M.beta B) = M.kms.state.eval (B * A) :=
  M.kms.eval_mul_modular_eq_eval_flip A B

end ModularTimeKMSContext

@[rep_depth operator]
structure CyclicModularTimeKMSContext where
  state : CyclicAlgebraicState (H := H)
  beta : ℝ

namespace CyclicModularTimeKMSContext

variable (C : CyclicModularTimeKMSContext (H := H))

@[rep_depth operator]
def sigma (_C : CyclicModularTimeKMSContext (H := H)) :
    AdditiveModularFlow (H := H) :=
  identityAdditiveModularFlow (H := H)

@[rep_depth operator]
theorem modular_time_add (s t : ℝ) :
    C.sigma (s + t) = C.sigma s * C.sigma t :=
  AdditiveModularFlow.map_add C.sigma s t

@[rep_depth operator]
theorem modular_time_zero :
    C.sigma 0 = 1 :=
  AdditiveModularFlow.map_zero C.sigma

@[rep_depth operator]
theorem kms_eval_mul_modular_eq_eval_flip (A B : Obs) :
    C.state.state.eval (A * C.sigma C.beta B) = C.state.state.eval (B * A) := by
  simpa [CyclicModularTimeKMSContext.sigma, identityAdditiveModularFlow] using C.state.cyclic A B

/--
Compatibility adapter from the constructive cyclic modular-time branch to the
broad modular-time KMS context.

This removes the explicit `sigma` and `kms` packet from callers that already
live on the cyclic identity-flow lane: both fields are derived constructively
from the owned cyclic state.
-/
@[rep_depth operator]
def toModularTimeKMSContext :
    ModularTimeKMSContext (H := H) where
  sigma := C.sigma
  beta := C.beta
  kms := C.state.toIdentityKMSState C.beta

/-- On the adapter, the modular flow is definitionally the owned identity flow. -/
@[rep_depth operator]
theorem toModularTimeKMSContext_sigma_eq :
    C.toModularTimeKMSContext.sigma = C.sigma :=
  rfl

/-- On the adapter, the KMS state is definitionally the cyclic identity-flow KMS witness. -/
@[rep_depth operator]
theorem toModularTimeKMSContext_kms_eq :
    C.toModularTimeKMSContext.kms = C.state.toIdentityKMSState C.beta :=
  rfl

end CyclicModularTimeKMSContext

namespace CyclicAlgebraicState

variable (ω : CyclicAlgebraicState (H := H))

@[rep_depth operator]
def toCyclicModularTimeKMSContext (beta : ℝ) :
    CyclicModularTimeKMSContext (H := H) where
  state := ω
  beta := beta

/--
Direct constructive modular-time KMS context from a cyclic algebraic state.

This removes the explicit `sigma` and `kms` packet from callers on the cyclic
identity-flow branch by routing through the owned constructive adapter.
-/
@[rep_depth operator]
def toModularTimeKMSContext (beta : ℝ) :
    ModularTimeKMSContext (H := H) :=
  (ω.toCyclicModularTimeKMSContext beta).toModularTimeKMSContext

/-- On the direct constructive adapter, the modular flow is the identity flow. -/
@[rep_depth operator]
theorem toModularTimeKMSContext_sigma_eq (beta : ℝ) :
    (ω.toModularTimeKMSContext beta).sigma =
      identityAdditiveModularFlow (H := H) :=
  rfl

/-- On the direct constructive adapter, the KMS witness is the cyclic identity-flow one. -/
@[rep_depth operator]
theorem toModularTimeKMSContext_kms_eq (beta : ℝ) :
    (ω.toModularTimeKMSContext beta).kms = ω.toIdentityKMSState beta :=
  rfl

end CyclicAlgebraicState

/--
Coordinate emergence as a readout from observables.

Coordinates are not primitive in this interface.  They appear only after a
chosen readout/representation map from the observable algebra.
-/
@[rep_depth operator]
structure CoordinateEmergence (Coord : Type v) where
  readout : Obs → Coord
  emergentObservable : Coord → Obs
  readout_emergent : ∀ x : Coord, readout (emergentObservable x) = x

namespace CoordinateEmergence

variable {Coord : Type v}
variable (C : CoordinateEmergence (H := H) Coord)

/-- Coordinates are recovered from chosen observables by the readout map. -/
@[rep_depth operator]
theorem coordinate_recovers_from_observable (x : Coord) :
    C.readout (C.emergentObservable x) = x :=
  C.readout_emergent x

end CoordinateEmergence

/--
Full coordinateless Souriau/KMS/Fisher context.

This is the repo-native table from the prose: algebraic state, Souriau moment,
KMS modular time, quantum Fisher/SLD metric, Weyl gauge, and optional coordinate
readout.
-/
@[rep_depth operator]
structure CoordinatelessSouriauFisherContext
    (Symmetry : Type v) (Tangent : Type w) where
  state : AlgebraicState (H := H)
  sigma : AdditiveModularFlow (H := H)
  beta : ℝ
  kms : KMSState (H := H) sigma beta
  kms_state_eq : kms.state = state
  souriauMoment : OperatorSouriauMoment (H := H) Symmetry
  fisherMetric : QuantumFisherSLDMetric (H := H) Tangent state
  weylGauge : WeylAlgebraGauge (H := H) state

/--
Minimal broad coordinateless Souriau/KMS/Fisher context.

This removes the redundant explicit `state` and `kms_state_eq` packet from the
broad context: the algebraic state is read directly from `kms.state`.
-/
@[rep_depth operator]
structure MinimalCoordinatelessSouriauFisherContext
    (Symmetry : Type v) (Tangent : Type w) where
  sigma : AdditiveModularFlow (H := H)
  beta : ℝ
  kms : KMSState (H := H) sigma beta
  souriauMoment : OperatorSouriauMoment (H := H) Symmetry
  fisherMetric : QuantumFisherSLDMetric (H := H) Tangent kms.state
  weylGauge : WeylAlgebraGauge (H := H) kms.state

/--
Minimal broad coordinateless Souriau/KMS/Fisher context on the identity-Weyl
branch.

This removes the explicit `weylGauge` packet from the broad context when the
constructive route already chooses the identity gauge.
-/
@[rep_depth operator]
structure MinimalIdentityWeylCoordinatelessSouriauContext
    (Symmetry : Type v) (Tangent : Type w) where
  sigma : AdditiveModularFlow (H := H)
  beta : ℝ
  kms : KMSState (H := H) sigma beta
  souriauMoment : OperatorSouriauMoment (H := H) Symmetry
  fisherMetric : QuantumFisherSLDMetric (H := H) Tangent kms.state

namespace MinimalIdentityWeylCoordinatelessSouriauContext

variable {Symmetry : Type v} {Tangent : Type w}
variable (C : MinimalIdentityWeylCoordinatelessSouriauContext (H := H) Symmetry Tangent)

/-- The algebraic state is read directly from the KMS witness. -/
@[rep_depth operator]
def state : AlgebraicState (H := H) :=
  C.kms.state

/-- The Weyl-gauge packet is constructively the identity gauge on this branch. -/
@[rep_depth operator]
def weylGauge : WeylAlgebraGauge (H := H) C.state :=
  identityWeylAlgebraGauge (H := H) C.state

/--
Convert the identity-Weyl branch to the existing minimal broad coordinateless
context by constructing the removed Weyl packet definitionally.
-/
@[rep_depth operator]
def toMinimalCoordinatelessSouriauFisherContext :
    MinimalCoordinatelessSouriauFisherContext (H := H) Symmetry Tangent where
  sigma := C.sigma
  beta := C.beta
  kms := C.kms
  souriauMoment := C.souriauMoment
  fisherMetric := C.fisherMetric
  weylGauge := C.weylGauge

/--
Compatibility adapter from the identity-Weyl minimal branch to the legacy broad
coordinateless context.
-/
@[rep_depth operator]
def toFull :
    CoordinatelessSouriauFisherContext (H := H) Symmetry Tangent where
  state := C.kms.state
  sigma := C.sigma
  beta := C.beta
  kms := C.kms
  kms_state_eq := rfl
  souriauMoment := C.souriauMoment
  fisherMetric := C.fisherMetric
  weylGauge := C.weylGauge

end MinimalIdentityWeylCoordinatelessSouriauContext

namespace MinimalCoordinatelessSouriauFisherContext

variable {Symmetry : Type v} {Tangent : Type w}
variable (C : MinimalCoordinatelessSouriauFisherContext (H := H) Symmetry Tangent)

/-- The algebraic state is read directly from the KMS witness. -/
@[rep_depth operator]
def state : AlgebraicState (H := H) :=
  C.kms.state

/-- Constructor theorem for the narrowed broad KMS/Fisher lane with no explicit `state` packet. -/
@[rep_depth operator]
theorem mk_of_kms
    (sigma : AdditiveModularFlow (H := H))
    (beta : ℝ)
    (kms : KMSState (H := H) sigma beta)
    (souriauMoment : OperatorSouriauMoment (H := H) Symmetry)
  (fisherMetric : QuantumFisherSLDMetric (H := H) Tangent kms.state)
  (weylGauge : WeylAlgebraGauge (H := H) kms.state) :
  ∃ ctx : MinimalCoordinatelessSouriauFisherContext (H := H) Symmetry Tangent,
    ctx.state = kms.state := by
  refine ⟨{
    sigma := sigma
    beta := beta
    kms := kms
    souriauMoment := souriauMoment
    fisherMetric := fisherMetric
    weylGauge := weylGauge
  }, rfl⟩

/--
Constructor theorem for the narrowed KMS/Fisher lane when the Weyl gauge is the
canonical identity gauge.  This eliminates the explicit `weylGauge` hypothesis
by constructing it definitionally via `identityWeylAlgebraGauge`.
-/
@[rep_depth operator]
theorem mk_of_kms_identity
    (sigma : AdditiveModularFlow (H := H))
    (beta : ℝ)
    (kms : KMSState (H := H) sigma beta)
    (souriauMoment : OperatorSouriauMoment (H := H) Symmetry)
    (fisherMetric : QuantumFisherSLDMetric (H := H) Tangent kms.state) :
    ∃ ctx : MinimalCoordinatelessSouriauFisherContext (H := H) Symmetry Tangent,
      ctx.state = kms.state := by
  refine ⟨{
    sigma := sigma,
    beta := beta,
    kms := kms,
    souriauMoment := souriauMoment,
    fisherMetric := fisherMetric,
    weylGauge := identityWeylAlgebraGauge (H := H) kms.state,
  }, rfl⟩

/--
Compatibility adapter from the narrowed broad KMS/Fisher lane to the legacy
coordinateless context.

This keeps downstream users on the old `CoordinatelessSouriauFisherContext`
surface without carrying an extra `state` field or `kms_state_eq` proof.
-/
@[rep_depth operator]
def toCoordinatelessSouriauFisherContext :
    CoordinatelessSouriauFisherContext (H := H) Symmetry Tangent where
  state := C.kms.state
  sigma := C.sigma
  beta := C.beta
  kms := C.kms
  kms_state_eq := rfl
  souriauMoment := C.souriauMoment
  fisherMetric := C.fisherMetric
  weylGauge := C.weylGauge

/-- The compatibility adapter reads back the same algebraic state definitionally. -/
@[rep_depth operator]
theorem toCoordinatelessSouriauFisherContext_state_eq :
    C.toCoordinatelessSouriauFisherContext.state = C.state :=
  rfl

/-- The compatibility adapter reconstructs the removed `kms_state_eq` packet definitionally. -/
@[rep_depth operator]
theorem toCoordinatelessSouriauFisherContext_kms_state_eq :
    C.toCoordinatelessSouriauFisherContext.kms.state =
      C.toCoordinatelessSouriauFisherContext.state :=
  rfl

/--
Constructor theorem routing the broad compatibility packet through the narrowed
minimal coordinateless KMS/Fisher lane.

This removes the explicit `state` and `kms_state_eq` constructor surface when
callers already own a `MinimalCoordinatelessSouriauFisherContext` witness.
-/
@[rep_depth operator]
theorem mk_broad_of_minimal
    (C : MinimalCoordinatelessSouriauFisherContext (H := H) Symmetry Tangent) :
    ∃ ctx : CoordinatelessSouriauFisherContext (H := H) Symmetry Tangent,
      ctx.state = C.state :=
  ⟨C.toCoordinatelessSouriauFisherContext, rfl⟩

/--
Constructor theorem exposing the broad compatibility packet directly from the
narrowed minimal coordinateless KMS/Fisher witness.

This keeps the legacy broad surface available while removing the explicit
`state` and `kms_state_eq` theorem arguments from the constructor route.
-/
@[rep_depth operator]
theorem mk_of_minimal_kms
    (C : MinimalCoordinatelessSouriauFisherContext (H := H) Symmetry Tangent) :
    ∃ ctx : CoordinatelessSouriauFisherContext (H := H) Symmetry Tangent,
      ctx.state = C.state :=
  C.mk_broad_of_minimal

end MinimalCoordinatelessSouriauFisherContext

namespace CoordinatelessSouriauFisherContext

variable {Symmetry : Type v} {Tangent : Type w}
variable (C : CoordinatelessSouriauFisherContext (H := H) Symmetry Tangent)

/-- Convenience lemma: the `state` field equals the KMS state's `state`. -/
@[rep_depth operator]
theorem state_eq_kms_state :
    C.state = C.kms.state := by
  simpa using C.kms_state_eq.symm

/--
Project a broad coordinateless Souriau/KMS/Fisher packet onto the narrowed
minimal branch.

This removes the explicit `state` and `kms_state_eq` fields for downstream
consumers that only need the KMS witness itself.
-/
@[rep_depth operator]
def toMinimalCoordinatelessSouriauFisherContext :
    MinimalCoordinatelessSouriauFisherContext (H := H) Symmetry Tangent where
  sigma := C.sigma
  beta := C.beta
  kms := C.kms
  souriauMoment := C.souriauMoment
  fisherMetric := by
    simpa [C.state_eq_kms_state] using C.fisherMetric
  weylGauge := by
    simpa [C.state_eq_kms_state] using C.weylGauge

/-- The narrowed minimal branch reads back the original state propositionally. -/
@[rep_depth operator]
theorem toMinimalCoordinatelessSouriauFisherContext_state_eq :
    C.toMinimalCoordinatelessSouriauFisherContext.state = C.state := by
  exact C.kms_state_eq

/-- The selected Souriau moment is an operator, not a coordinate field. -/
@[rep_depth operator]
theorem souriau_thermalGenerator_eq_moment :
    C.souriauMoment.thermalGenerator =
      C.souriauMoment.momentOperator C.souriauMoment.geometricTemperature :=
  C.souriauMoment.thermalGenerator_eq_moment_geometricTemperature

/-- KMS equilibrium in the coordinateless context. -/
@[rep_depth operator]
theorem kms_identity (A B : Obs) :
    C.state.eval (A * C.sigma C.beta B) = C.state.eval (B * A) :=
  by
    calc
      C.state.eval (A * C.sigma C.beta B)
          = C.kms.state.eval (A * C.sigma C.beta B) := by
            rw [C.kms_state_eq]
      _ = C.kms.state.eval (B * A) :=
            C.kms.eval_mul_modular_eq_eval_flip A B
      _ = C.state.eval (B * A) := by
            rw [C.kms_state_eq]

/-- Fisher/Bures metric is the supplied SLD state readout. -/
@[rep_depth operator]
theorem fisher_metric_eq_sld_readout (X Y : Tangent) :
    C.fisherMetric.metric X Y =
      C.state.eval ((C.fisherMetric.sld X) * (C.fisherMetric.sld Y)) :=
  C.fisherMetric.metric_eq_state_sld_product X Y

/-- Fisher/Bures metric symmetry. -/
@[rep_depth operator]
theorem fisher_metric_symm (X Y : Tangent) :
    C.fisherMetric.metric X Y = C.fisherMetric.metric Y X :=
  C.fisherMetric.metric_symm X Y

/-- Weyl gauge invariance is an algebraic state-invariance statement. -/
@[rep_depth operator]
theorem weyl_state_invariant (A : Obs) :
    C.state.eval (C.weylGauge.gauge A) = C.state.eval A :=
  C.weylGauge.eval_gauge_eq_eval A

/-- Modular time is additive in the operator-algebraic context. -/
@[rep_depth operator]
theorem modular_time_add (s t : ℝ) :
    C.sigma (s + t) = C.sigma s * C.sigma t :=
  AdditiveModularFlow.map_add C.sigma s t

end CoordinatelessSouriauFisherContext

/--
Minimal constructive coordinateless Souriau context on the cyclic identity
modular branch.

This strips the remaining explicit Fisher-metric and Weyl-gauge packets from the
constructive branch: both are derived canonically from the cyclic state and the
chosen SLD readout.
-/
@[rep_depth operator]
structure MinimalCyclicCoordinatelessSouriauContext
    (Symmetry : Type v) (Tangent : Type w) where
  state : CyclicAlgebraicState (H := H)
  beta : ℝ
  souriauMoment : OperatorSouriauMoment (H := H) Symmetry
  sld : Tangent → Obs

namespace MinimalCyclicCoordinatelessSouriauContext

variable {Symmetry : Type v} {Tangent : Type w}
variable (C : MinimalCyclicCoordinatelessSouriauContext (H := H) Symmetry Tangent)

/-- The modular automorphism group is the owned identity flow on this branch. -/
@[rep_depth operator]
def sigma (_C : MinimalCyclicCoordinatelessSouriauContext (H := H) Symmetry Tangent) :
    AdditiveModularFlow (H := H) :=
  identityAdditiveModularFlow (H := H)

/-- Fisher/Bures metric canonically derived from the cyclic state and SLD readout. -/
@[rep_depth operator]
def fisherMetric : QuantumFisherSLDMetric (H := H) Tangent C.state.state :=
  C.state.sldQuantumFisherMetric C.sld

/-- Weyl gauge canonically collapses to the identity gauge on this branch. -/
@[rep_depth operator]
def weylGauge : WeylAlgebraGauge (H := H) C.state.state :=
  identityWeylAlgebraGauge (H := H) C.state.state

/-- The selected Souriau moment is an operator, not a coordinate field. -/
@[rep_depth operator]
theorem souriau_thermalGenerator_eq_moment :
    C.souriauMoment.thermalGenerator =
      C.souriauMoment.momentOperator C.souriauMoment.geometricTemperature :=
  C.souriauMoment.thermalGenerator_eq_moment_geometricTemperature

/-- KMS identity on the constructive cyclic identity-modular branch. -/
@[rep_depth operator]
theorem kms_identity (A B : Obs) :
    C.state.state.eval (A * C.sigma C.beta B) = C.state.state.eval (B * A) := by
  simpa [MinimalCyclicCoordinatelessSouriauContext.sigma, identityAdditiveModularFlow] using C.state.cyclic A B

/-- Fisher/Bures metric is the canonical SLD state readout. -/
@[rep_depth operator]
theorem fisher_metric_eq_sld_readout (X Y : Tangent) :
    C.fisherMetric.metric X Y =
      C.state.state.eval ((C.fisherMetric.sld X) * (C.fisherMetric.sld Y)) :=
  C.fisherMetric.metric_eq_state_sld_product X Y

/-- Fisher/Bures metric symmetry. -/
@[rep_depth operator]
theorem fisher_metric_symm (X Y : Tangent) :
    C.fisherMetric.metric X Y = C.fisherMetric.metric Y X :=
  C.fisherMetric.metric_symm X Y

/-- Weyl gauge invariance is an algebraic state-invariance statement. -/
@[rep_depth operator]
theorem weyl_state_invariant (A : Obs) :
    C.state.state.eval (C.weylGauge.gauge A) = C.state.state.eval A :=
  C.weylGauge.eval_gauge_eq_eval A

/-- Modular time is additive in the constructive operator-algebraic context. -/
@[rep_depth operator]
theorem modular_time_add (s t : ℝ) :
    C.sigma (s + t) = C.sigma s * C.sigma t :=
  AdditiveModularFlow.map_add C.sigma s t

/-- Modular time starts at the identity automorphism. -/
@[rep_depth operator]
theorem modular_time_zero :
    C.sigma 0 = 1 :=
  AdditiveModularFlow.map_zero C.sigma

/-- Search-facing theorem packet for the minimal fully constructive cyclic branch. -/
@[rep_depth operator]
theorem coordinateless_constructive_packet
    (A B : Obs) (X Y : Tangent) :
    C.state.state.eval 1 = 1 ∧
    C.state.state.eval (A * C.sigma C.beta B) = C.state.state.eval (B * A) ∧
    C.souriauMoment.thermalGenerator =
      C.souriauMoment.momentOperator C.souriauMoment.geometricTemperature ∧
    C.fisherMetric.metric X Y = C.fisherMetric.metric Y X ∧
    C.state.state.eval (C.weylGauge.gauge A) = C.state.state.eval A := by
  exact ⟨
    C.state.state.eval_one,
    C.kms_identity A B,
    C.souriau_thermalGenerator_eq_moment,
    C.fisher_metric_symm X Y,
    C.weyl_state_invariant A⟩

end MinimalCyclicCoordinatelessSouriauContext

/--
Observable-tangent specialization of the minimal constructive Souriau branch.
This is the smallest honest owner lane that removes the explicit `sld` packet:
the tangent carrier is the observable carrier itself, so the SLD assignment is
constructively the identity.
-/
@[rep_depth operator]
structure ObservableMinimalCyclicCoordinatelessSouriauContext
    (Symmetry : Type v) where
  state : CyclicAlgebraicState (H := H)
  beta : ℝ
  souriauMoment : OperatorSouriauMoment (H := H) Symmetry

namespace ObservableMinimalCyclicCoordinatelessSouriauContext

variable {Symmetry : Type v}
variable (C : ObservableMinimalCyclicCoordinatelessSouriauContext (H := H) Symmetry)

/-- The modular automorphism group is the owned identity flow on this branch. -/
@[rep_depth operator]
def sigma (_C : ObservableMinimalCyclicCoordinatelessSouriauContext (H := H) Symmetry) :
    AdditiveModularFlow (H := H) :=
  identityAdditiveModularFlow (H := H)

/-- Observable-tangent SLD is constructively the identity assignment. -/
@[rep_depth operator]
def fisherMetric : QuantumFisherSLDMetric (H := H) Obs C.state.state :=
  C.state.sldQuantumFisherMetric (fun A => A)

/-- Weyl gauge canonically collapses to the identity gauge on this branch. -/
@[rep_depth operator]
def weylGauge : WeylAlgebraGauge (H := H) C.state.state :=
  identityWeylAlgebraGauge (H := H) C.state.state

/-- The SLD assignment is the identity on the observable tangent branch. -/
@[rep_depth operator]
theorem fisherMetric_sld_eq_id (A : Obs) :
    C.fisherMetric.sld A = A := rfl

/-- The selected Souriau moment is an operator, not a coordinate field. -/
@[rep_depth operator]
theorem souriau_thermalGenerator_eq_moment :
    C.souriauMoment.thermalGenerator =
      C.souriauMoment.momentOperator C.souriauMoment.geometricTemperature :=
  C.souriauMoment.thermalGenerator_eq_moment_geometricTemperature

/-- KMS identity on the constructive cyclic identity-modular branch. -/
@[rep_depth operator]
theorem kms_identity (A B : Obs) :
    C.state.state.eval (A * C.sigma C.beta B) = C.state.state.eval (B * A) := by
  simpa [ObservableMinimalCyclicCoordinatelessSouriauContext.sigma, identityAdditiveModularFlow] using C.state.cyclic A B

/-- Fisher/Bures metric is the canonical identity-SLD state readout. -/
@[rep_depth operator]
theorem fisher_metric_eq_sld_readout (A B : Obs) :
    C.fisherMetric.metric A B =
      C.state.state.eval ((C.fisherMetric.sld A) * (C.fisherMetric.sld B)) :=
  C.fisherMetric.metric_eq_state_sld_product A B

/-- Fisher/Bures metric symmetry. -/
@[rep_depth operator]
theorem fisher_metric_symm (A B : Obs) :
    C.fisherMetric.metric A B = C.fisherMetric.metric B A :=
  C.fisherMetric.metric_symm A B

/-- Weyl gauge invariance is an algebraic state-invariance statement. -/
@[rep_depth operator]
theorem weyl_state_invariant (A : Obs) :
    C.state.state.eval (C.weylGauge.gauge A) = C.state.state.eval A :=
  C.weylGauge.eval_gauge_eq_eval A

/-- Search-facing theorem packet for the observable-tangent identity-SLD branch. -/
@[rep_depth operator]
theorem coordinateless_constructive_packet
    (A B : Obs) :
    C.state.state.eval 1 = 1 ∧
    C.state.state.eval (A * C.sigma C.beta B) = C.state.state.eval (B * A) ∧
    C.souriauMoment.thermalGenerator =
      C.souriauMoment.momentOperator C.souriauMoment.geometricTemperature ∧
    C.fisherMetric.metric A B = C.fisherMetric.metric B A ∧
    C.state.state.eval (C.weylGauge.gauge A) = C.state.state.eval A := by
  exact ⟨
    C.state.state.eval_one,
    C.kms_identity A B,
    C.souriau_thermalGenerator_eq_moment,
    C.fisher_metric_symm A B,
    C.weyl_state_invariant A⟩

end ObservableMinimalCyclicCoordinatelessSouriauContext

/--
Observable-tangent specialization of the fully constructive cyclic
Souriau context.
-/
@[rep_depth operator]
structure ObservableCyclicCoordinatelessSouriauFisherContext
    (Symmetry : Type v) where
  state : CyclicAlgebraicState (H := H)
  beta : ℝ
  souriauMoment : OperatorSouriauMoment (H := H) Symmetry

namespace ObservableCyclicCoordinatelessSouriauFisherContext

variable {Symmetry : Type v}
variable (C : ObservableCyclicCoordinatelessSouriauFisherContext (H := H) Symmetry)

/-- The modular automorphism group is the owned identity flow on this branch. -/
@[rep_depth operator]
def sigma (_C : ObservableCyclicCoordinatelessSouriauFisherContext (H := H) Symmetry) :
    AdditiveModularFlow (H := H) :=
  identityAdditiveModularFlow (H := H)

/-- Observable-tangent SLD is constructively the identity assignment. -/
@[rep_depth operator]
def fisherMetric : QuantumFisherSLDMetric (H := H) Obs C.state.state :=
  C.state.sldQuantumFisherMetric (fun A => A)

/-- Weyl gauge canonically collapses to the identity gauge on this branch. -/
@[rep_depth operator]
def weylGauge : WeylAlgebraGauge (H := H) C.state.state :=
  identityWeylAlgebraGauge (H := H) C.state.state

/-- The SLD assignment is the identity on the observable tangent branch. -/
@[rep_depth operator]
theorem fisherMetric_sld_eq_id (A : Obs) :
    C.fisherMetric.sld A = A := rfl

/-- The selected Souriau moment is an operator, not a coordinate field. -/
@[rep_depth operator]
theorem souriau_thermalGenerator_eq_moment :
    C.souriauMoment.thermalGenerator =
      C.souriauMoment.momentOperator C.souriauMoment.geometricTemperature :=
  C.souriauMoment.thermalGenerator_eq_moment_geometricTemperature

/-- KMS identity on the constructive cyclic identity-modular branch. -/
@[rep_depth operator]
theorem kms_identity (A B : Obs) :
    C.state.state.eval (A * C.sigma C.beta B) = C.state.state.eval (B * A) := by
  simpa [ObservableCyclicCoordinatelessSouriauFisherContext.sigma, identityAdditiveModularFlow] using C.state.cyclic A B

/-- Fisher/Bures metric is the canonical identity-SLD state readout. -/
@[rep_depth operator]
theorem fisher_metric_eq_sld_readout (A B : Obs) :
    C.fisherMetric.metric A B =
      C.state.state.eval ((C.fisherMetric.sld A) * (C.fisherMetric.sld B)) :=
  C.fisherMetric.metric_eq_state_sld_product A B

/-- Fisher/Bures metric symmetry. -/
@[rep_depth operator]
theorem fisher_metric_symm (A B : Obs) :
    C.fisherMetric.metric A B = C.fisherMetric.metric B A :=
  C.fisherMetric.metric_symm A B

/-- Weyl gauge invariance is an algebraic state-invariance statement. -/
@[rep_depth operator]
theorem weyl_state_invariant (A : Obs) :
    C.state.state.eval (C.weylGauge.gauge A) = C.state.state.eval A :=
  C.weylGauge.eval_gauge_eq_eval A

/-- Search-facing theorem packet for the observable-tangent identity-SLD branch. -/
@[rep_depth operator]
theorem coordinateless_constructive_packet
    (A B : Obs) :
    C.state.state.eval 1 = 1 ∧
    C.state.state.eval (A * C.sigma C.beta B) = C.state.state.eval (B * A) ∧
    C.souriauMoment.thermalGenerator =
      C.souriauMoment.momentOperator C.souriauMoment.geometricTemperature ∧
    C.fisherMetric.metric A B = C.fisherMetric.metric B A ∧
    C.state.state.eval (C.weylGauge.gauge A) = C.state.state.eval A := by
  exact ⟨
    C.state.state.eval_one,
    C.kms_identity A B,
    C.souriau_thermalGenerator_eq_moment,
    C.fisherMetric.metric_symm A B,
    C.weyl_state_invariant A⟩

/--
Compatibility adapter from the observable-tangent constructive branch to the
observable-tangent cyclic constructive branch.

This removes the remaining explicit `fisherMetric` and `weylGauge` packets from
callers already living on `ObservableMinimalCyclicCoordinatelessSouriauContext`:
both are computed canonically from the cyclic state on the identity-flow lane.
-/
@[rep_depth operator]
def ofObservableMinimal
    (C : ObservableMinimalCyclicCoordinatelessSouriauContext (H := H) Symmetry) :
    ObservableCyclicCoordinatelessSouriauFisherContext (H := H) Symmetry where
  state := C.state
  beta := C.beta
  souriauMoment := C.souriauMoment

/-- On the observable-tangent adapter, the Fisher metric is definitionally canonical. -/
@[rep_depth operator]
theorem ofObservableMinimal_fisherMetric_eq
    (C : ObservableMinimalCyclicCoordinatelessSouriauContext (H := H) Symmetry) :
    (ofObservableMinimal (H := H) C).fisherMetric = C.fisherMetric :=
  rfl

/-- On the observable-tangent adapter, the Weyl gauge is definitionally the identity gauge. -/
@[rep_depth operator]
theorem ofObservableMinimal_weylGauge_eq
    (C : ObservableMinimalCyclicCoordinatelessSouriauContext (H := H) Symmetry) :
    (ofObservableMinimal (H := H) C).weylGauge = C.weylGauge :=
  rfl

/--
Constructive KMS witness on the observable-tangent cyclic identity-flow lane.

This removes the need for callers on this branch to carry an explicit `kms`
packet: the KMS witness is computed directly from cyclicity and the owned
identity modular flow.
-/
@[rep_depth operator]
def toIdentityKMSState :
    KMSState (H := H) (identityAdditiveModularFlow (H := H)) C.beta :=
  C.state.toIdentityKMSState C.beta

/-- The constructive observable-cyclic KMS witness records the same underlying state. -/
@[rep_depth operator]
theorem toIdentityKMSState_state_eq :
    C.toIdentityKMSState.state = C.state.state :=
  rfl

end ObservableCyclicCoordinatelessSouriauFisherContext

namespace ObservableMinimalCyclicCoordinatelessSouriauContext

variable {Symmetry : Type v}
variable (C : ObservableMinimalCyclicCoordinatelessSouriauContext (H := H) Symmetry)

/--
Compatibility adapter from the observable-minimal constructive branch to the
observable-tangent cyclic Souriau/Fisher context.

This removes the remaining explicit `sigma`, `fisherMetric`, and `weylGauge`
surfaces from callers that already live on the observable-tangent
identity-SLD branch: those objects are computed canonically from the owned
cyclic identity-flow lane.
-/
@[rep_depth operator]
def toObservableCyclicCoordinatelessSouriauFisherContext :
    ObservableCyclicCoordinatelessSouriauFisherContext (H := H) Symmetry :=
  ObservableCyclicCoordinatelessSouriauFisherContext.ofObservableMinimal (H := H) C

/-- On the adapter, the modular flow is definitionally the owned identity flow. -/
@[rep_depth operator]
theorem toObservableCyclicCoordinatelessSouriauFisherContext_sigma_eq :
    C.toObservableCyclicCoordinatelessSouriauFisherContext.sigma = C.sigma :=
  rfl

/-- On the adapter, the Fisher metric is definitionally the canonical identity-SLD readout. -/
@[rep_depth operator]
theorem toObservableCyclicCoordinatelessSouriauFisherContext_fisherMetric_eq :
    C.toObservableCyclicCoordinatelessSouriauFisherContext.fisherMetric = C.fisherMetric :=
  rfl

/-- On the adapter, the Weyl gauge is definitionally the canonical identity gauge. -/
@[rep_depth operator]
theorem toObservableCyclicCoordinatelessSouriauFisherContext_weylGauge_eq :
    C.toObservableCyclicCoordinatelessSouriauFisherContext.weylGauge = C.weylGauge :=
  rfl

/--
Constructive KMS witness on the observable-minimal cyclic identity-flow lane.

This removes the remaining explicit `kms` surface for callers that already live
on the observable-minimal branch.
-/
@[rep_depth operator]
def toIdentityKMSState :
    KMSState (H := H) (identityAdditiveModularFlow (H := H)) C.beta :=
  C.toObservableCyclicCoordinatelessSouriauFisherContext.toIdentityKMSState

/-- Read back the algebraic state on the observable-minimal constructive KMS adapter. -/
@[rep_depth operator]
theorem toObservableCyclicCoordinatelessSouriauFisherContext_toIdentityKMSState_state_eq :
    C.toIdentityKMSState.state = C.state.state :=
  rfl

/--
Compatibility adapter from the observable-minimal cyclic branch to the modular-time
KMS context.

This removes the remaining explicit `sigma` and `kms` packets from callers that
already live on the observable-minimal identity-SLD lane: both are computed
constructively from cyclicity and the owned identity modular flow.
-/
@[rep_depth operator]
def toModularTimeKMSContext :
    ModularTimeKMSContext (H := H) where
  sigma := C.sigma
  beta := C.beta
  kms := C.toIdentityKMSState

/-- On the observable-minimal modular-time adapter, the modular flow is definitionally the owned identity flow. -/
@[rep_depth operator]
theorem toModularTimeKMSContext_sigma_eq :
    C.toModularTimeKMSContext.sigma = C.sigma :=
  rfl

/-- On the observable-minimal modular-time adapter, the KMS witness is definitionally the constructive identity-flow one. -/
@[rep_depth operator]
theorem toModularTimeKMSContext_kms_eq :
    C.toModularTimeKMSContext.kms = C.toIdentityKMSState :=
  rfl

/--
Compatibility adapter from the observable-minimal cyclic branch to the narrowed
broad coordinateless Souriau/KMS/Fisher context.

This removes the remaining explicit `sigma`, `kms`, `fisherMetric`, and
`weylGauge` packets from callers that already live on the observable-minimal
identity-SLD lane.
-/
@[rep_depth operator]
def toObservableMinimalCoordinatelessSouriauFisherContext :
    MinimalCoordinatelessSouriauFisherContext (H := H) Symmetry Obs where
  sigma := C.sigma
  beta := C.beta
  kms := C.toIdentityKMSState
  souriauMoment := C.souriauMoment
  fisherMetric := C.fisherMetric
  weylGauge := C.weylGauge

/-- On the narrowed observable adapter, the modular flow is definitionally the owned identity flow. -/
@[rep_depth operator]
theorem toObservableMinimalCoordinatelessSouriauFisherContext_sigma_eq :
    C.toObservableMinimalCoordinatelessSouriauFisherContext.sigma = C.sigma :=
  rfl

/--
Constructor theorem routing the narrowed observable coordinateless packet
through the observable-minimal cyclic constructive branch.

This removes the explicit `sigma`, `kms`, `fisherMetric`, and `weylGauge`
constructor surface for callers that already own an
`ObservableMinimalCyclicCoordinatelessSouriauContext` witness.
-/
@[rep_depth operator]
theorem mk_observable_minimal_of_cyclic :
    ∃ ctx : MinimalCoordinatelessSouriauFisherContext (H := H) Symmetry Obs,
      ctx.state = C.state.state :=
  ⟨C.toObservableMinimalCoordinatelessSouriauFisherContext, rfl⟩

/--
Compatibility adapter from the observable-minimal cyclic branch to the full
coordinateless Souriau/KMS/Fisher context.

This keeps downstream users on the legacy broad surface while routing through
the theorem-backed narrowed observable branch.
-/
@[rep_depth operator]
def toObservableCoordinatelessSouriauFisherContext :
    CoordinatelessSouriauFisherContext (H := H) Symmetry Obs :=
  C.toObservableMinimalCoordinatelessSouriauFisherContext.toCoordinatelessSouriauFisherContext

/-- On the broad observable adapter, the modular flow is definitionally the owned identity flow. -/
@[rep_depth operator]
theorem toObservableCoordinatelessSouriauFisherContext_sigma_eq :
    C.toObservableCoordinatelessSouriauFisherContext.sigma = C.sigma :=
  rfl

/--
Constructor theorem routing the legacy observable broad packet through the
observable-minimal cyclic constructive branch.

This keeps the broad compatibility surface available while removing the explicit
`sigma`, `kms`, `kms_state_eq`, `fisherMetric`, and `weylGauge` constructor
surface on the owned observable identity-SLD lane.
-/
@[rep_depth operator]
theorem mk_observable_broad_of_cyclic :
    ∃ ctx : CoordinatelessSouriauFisherContext (H := H) Symmetry Obs,
      ctx.state = C.state.state :=
  ⟨C.toObservableCoordinatelessSouriauFisherContext, rfl⟩

end ObservableMinimalCyclicCoordinatelessSouriauContext

/--
Fully constructive coordinateless Souriau/KMS/Fisher context on the cyclic
identity-modular branch.

Unlike `CoordinatelessSouriauFisherContext`, this branch carries no explicit
`KMSState` packet and no state-equality witness.  The KMS identity is derived
from cyclicity together with the owned identity modular flow.
-/
@[rep_depth operator]
structure CyclicCoordinatelessSouriauFisherContext
    (Symmetry : Type v) (Tangent : Type w) where
  state : CyclicAlgebraicState (H := H)
  beta : ℝ
  souriauMoment : OperatorSouriauMoment (H := H) Symmetry
  fisherMetric : QuantumFisherSLDMetric (H := H) Tangent state.state
  weylGauge : WeylAlgebraGauge (H := H) state.state

namespace CyclicCoordinatelessSouriauFisherContext

variable {Symmetry : Type v} {Tangent : Type w}
variable (C : CyclicCoordinatelessSouriauFisherContext (H := H) Symmetry Tangent)

/-- The modular automorphism group is the owned identity flow on this branch. -/
@[rep_depth operator]
def sigma (_C : CyclicCoordinatelessSouriauFisherContext (H := H) Symmetry Tangent) :
    AdditiveModularFlow (H := H) :=
  identityAdditiveModularFlow (H := H)

/-- The selected Souriau moment is an operator, not a coordinate field. -/
@[rep_depth operator]
theorem souriau_thermalGenerator_eq_moment :
    C.souriauMoment.thermalGenerator =
      C.souriauMoment.momentOperator C.souriauMoment.geometricTemperature :=
  C.souriauMoment.thermalGenerator_eq_moment_geometricTemperature

/-- KMS identity on the constructive cyclic identity-modular branch. -/
@[rep_depth operator]
theorem kms_identity (A B : Obs) :
    C.state.state.eval (A * C.sigma C.beta B) = C.state.state.eval (B * A) := by
  simpa [CyclicCoordinatelessSouriauFisherContext.sigma, identityAdditiveModularFlow] using C.state.cyclic A B

/-- Fisher/Bures metric is the supplied SLD state readout. -/
@[rep_depth operator]
theorem fisher_metric_eq_sld_readout (X Y : Tangent) :
    C.fisherMetric.metric X Y =
      C.state.state.eval ((C.fisherMetric.sld X) * (C.fisherMetric.sld Y)) :=
  C.fisherMetric.metric_eq_state_sld_product X Y

/-- Fisher/Bures metric symmetry. -/
@[rep_depth operator]
theorem fisher_metric_symm (X Y : Tangent) :
    C.fisherMetric.metric X Y = C.fisherMetric.metric Y X :=
  C.fisherMetric.metric_symm X Y

/-- Weyl gauge invariance is an algebraic state-invariance statement. -/
@[rep_depth operator]
theorem weyl_state_invariant (A : Obs) :
    C.state.state.eval (C.weylGauge.gauge A) = C.state.state.eval A :=
  C.weylGauge.eval_gauge_eq_eval A

/-- Modular time is additive in the constructive operator-algebraic context. -/
@[rep_depth operator]
theorem modular_time_add (s t : ℝ) :
    C.sigma (s + t) = C.sigma s * C.sigma t :=
  AdditiveModularFlow.map_add C.sigma s t

/-- Modular time starts at the identity automorphism. -/
@[rep_depth operator]
theorem modular_time_zero :
    C.sigma 0 = 1 :=
  AdditiveModularFlow.map_zero C.sigma

/-- Search-facing theorem packet for the fully constructive cyclic branch. -/
@[rep_depth operator]
theorem coordinateless_constructive_packet
    (A B : Obs) (X Y : Tangent) :
    C.state.state.eval 1 = 1 ∧
    C.state.state.eval (A * C.sigma C.beta B) = C.state.state.eval (B * A) ∧
    C.souriauMoment.thermalGenerator =
      C.souriauMoment.momentOperator C.souriauMoment.geometricTemperature ∧
    C.fisherMetric.metric X Y = C.fisherMetric.metric Y X ∧
    C.state.state.eval (C.weylGauge.gauge A) = C.state.state.eval A := by
  exact ⟨
    C.state.state.eval_one,
    C.kms_identity A B,
    C.souriau_thermalGenerator_eq_moment,
    C.fisher_metric_symm X Y,
    C.weyl_state_invariant A⟩

end CyclicCoordinatelessSouriauFisherContext

namespace CyclicCoordinatelessSouriauFisherContext

variable {Symmetry : Type v} {Tangent : Type w}

/--
Convert a cyclic coordinateless Souriau/Fisher context to the minimal cyclic
form by retaining only the generating state, inverse-temperature parameter,
Souriau moment, and SLD readout.
-/
@[rep_depth operator]
def toMinimalCyclicCoordinatelessSouriauContext
    (C : CyclicCoordinatelessSouriauFisherContext (H := H) Symmetry Tangent) :
    MinimalCyclicCoordinatelessSouriauContext (H := H) Symmetry Tangent where
  state := C.state
  beta := C.beta
  souriauMoment := C.souriauMoment
  sld := fun A => C.fisherMetric.sld A

end CyclicCoordinatelessSouriauFisherContext

namespace MinimalCyclicCoordinatelessSouriauContext

variable {Symmetry : Type v} {Tangent : Type w}
variable (C : MinimalCyclicCoordinatelessSouriauContext (H := H) Symmetry Tangent)

/-- Compatibility adapter from the minimal constructive branch to the broader cyclic Fisher context. -/
@[rep_depth operator]
def toCyclicCoordinatelessSouriauFisherContext :
    CyclicCoordinatelessSouriauFisherContext (H := H) Symmetry Tangent where
  state := C.state
  beta := C.beta
  souriauMoment := C.souriauMoment
  fisherMetric := C.fisherMetric
  weylGauge := C.weylGauge

/-- On the adapter, the Fisher metric is definitionally the canonical derived one. -/
@[rep_depth operator]
theorem toCyclicCoordinatelessSouriauFisherContext_fisherMetric_eq :
    C.toCyclicCoordinatelessSouriauFisherContext.fisherMetric = C.fisherMetric :=
  rfl

/-- On the adapter, the Weyl gauge is definitionally the canonical identity gauge. -/
@[rep_depth operator]
theorem toCyclicCoordinatelessSouriauFisherContext_weylGauge_eq :
    C.toCyclicCoordinatelessSouriauFisherContext.weylGauge = C.weylGauge :=
  rfl

/--
Compatibility adapter from the minimal constructive branch to the full
coordinateless Souriau/KMS/Fisher context.

This removes the explicit `sigma`, `kms`, `kms_state_eq`, `fisherMetric`, and
`weylGauge` packet from callers that already live on the minimal cyclic branch:
all of those fields are computed from the owned cyclic identity-flow lane.
-/
@[rep_depth operator]
def toMinimalCoordinatelessSouriauFisherContext :
    MinimalCoordinatelessSouriauFisherContext (H := H) Symmetry Tangent where
  sigma := C.sigma
  beta := C.beta
  kms := C.state.toIdentityKMSState C.beta
  souriauMoment := C.souriauMoment
  fisherMetric := C.fisherMetric
  weylGauge := C.weylGauge

/-- On the narrowed adapter, the modular flow is definitionally the owned identity flow. -/
@[rep_depth operator]
theorem toMinimalCoordinatelessSouriauFisherContext_sigma_eq :
    C.toMinimalCoordinatelessSouriauFisherContext.sigma = C.sigma :=
  rfl

/--
Constructor theorem routing the narrowed broad packet directly through the
minimal cyclic constructive branch.

This removes the explicit `sigma`, `kms`, `fisherMetric`, and `weylGauge`
constructor surface for callers that already own a
`MinimalCyclicCoordinatelessSouriauContext` witness.
-/
@[rep_depth operator]
theorem mk_minimal_of_cyclic :
    ∃ ctx : MinimalCoordinatelessSouriauFisherContext (H := H) Symmetry Tangent,
      ctx.state = C.state.state :=
  ⟨C.toMinimalCoordinatelessSouriauFisherContext, rfl⟩

/--
Compatibility adapter from the minimal constructive branch to the full
coordinateless Souriau/KMS/Fisher context.

This removes the explicit `sigma`, `kms`, `kms_state_eq`, `fisherMetric`, and
`weylGauge` packet from callers that already live on the minimal cyclic branch:
all of those fields are computed from the owned cyclic identity-flow lane.
-/
@[rep_depth operator]
def toCoordinatelessSouriauFisherContext :
    CoordinatelessSouriauFisherContext (H := H) Symmetry Tangent :=
  C.toMinimalCoordinatelessSouriauFisherContext.toCoordinatelessSouriauFisherContext

/-- On the adapter, the modular flow is definitionally the owned identity flow. -/
@[rep_depth operator]
theorem toCoordinatelessSouriauFisherContext_sigma_eq :
    C.toCoordinatelessSouriauFisherContext.sigma = C.sigma :=
  rfl

/-- On the adapter, the Fisher metric is definitionally the canonical derived one. -/
@[rep_depth operator]
theorem toCoordinatelessSouriauFisherContext_fisherMetric_eq :
    C.toCoordinatelessSouriauFisherContext.fisherMetric = C.fisherMetric :=
  rfl

/-- On the adapter, the Weyl gauge is definitionally the canonical identity gauge. -/
@[rep_depth operator]
theorem toCoordinatelessSouriauFisherContext_weylGauge_eq :
    C.toCoordinatelessSouriauFisherContext.weylGauge = C.weylGauge :=
  rfl

/--
Constructor theorem routing the legacy broad packet directly through the minimal
cyclic constructive branch.

This keeps the broad compatibility surface available while removing the explicit
`sigma`, `kms`, `kms_state_eq`, `fisherMetric`, and `weylGauge` constructor
surface on the owned cyclic lane.
-/
@[rep_depth operator]
theorem mk_broad_of_cyclic :
    ∃ ctx : CoordinatelessSouriauFisherContext (H := H) Symmetry Tangent,
      ctx.state = C.state.state :=
  ⟨C.toCoordinatelessSouriauFisherContext, rfl⟩

end MinimalCyclicCoordinatelessSouriauContext

namespace CyclicAlgebraicState

variable {Symmetry : Type v} {Tangent : Type w}
variable (ω : CyclicAlgebraicState (H := H))

/-- Minimal constructive coordinateless Souriau context from cyclic state and SLD readout. -/
@[rep_depth operator]
def toMinimalCyclicCoordinatelessSouriauContext
    (beta : ℝ)
    (J : OperatorSouriauMoment (H := H) Symmetry)
    (sld : Tangent → Obs) :
    MinimalCyclicCoordinatelessSouriauContext (H := H) Symmetry Tangent where
  state := ω
  beta := beta
  souriauMoment := J
  sld := sld

/-- Observable-tangent constructive Souriau context with identity SLD. -/
@[rep_depth operator]
def toObservableMinimalCyclicCoordinatelessSouriauContext
    (beta : ℝ)
    (J : OperatorSouriauMoment (H := H) Symmetry) :
    ObservableMinimalCyclicCoordinatelessSouriauContext (H := H) Symmetry where
  state := ω
  beta := beta
  souriauMoment := J

/-- Observable-tangent constructive Souriau context with identity SLD. -/
@[rep_depth operator]
def toObservableCyclicCoordinatelessSouriauFisherContext
    (beta : ℝ)
    (J : OperatorSouriauMoment (H := H) Symmetry) :
    ObservableCyclicCoordinatelessSouriauFisherContext (H := H) Symmetry where
  state := ω
  beta := beta
  souriauMoment := J

/--
Observable-tangent constructive coordinateless Souriau/KMS/Fisher packet on the
narrowed broad branch.

This removes the explicit observable `sld`, `sigma`, `kms`, `fisherMetric`, and
`weylGauge` packets from callers that already live on the cyclic identity-flow
lane with observable tangent carrier.
-/
@[rep_depth operator]
def toObservableMinimalCoordinatelessSouriauFisherContext
    (beta : ℝ)
    (J : OperatorSouriauMoment (H := H) Symmetry) :
    MinimalCoordinatelessSouriauFisherContext (H := H) Symmetry Obs :=
  (ω.toObservableMinimalCyclicCoordinatelessSouriauContext beta J).toObservableMinimalCoordinatelessSouriauFisherContext

/--
Observable-tangent constructive coordinateless Souriau/KMS/Fisher packet on the
legacy broad branch.

This keeps downstream users on the broad surface while routing through the
owned observable-minimal constructive branch.
-/
@[rep_depth operator]
def toObservableCoordinatelessSouriauFisherContext
    (beta : ℝ)
    (J : OperatorSouriauMoment (H := H) Symmetry) :
    CoordinatelessSouriauFisherContext (H := H) Symmetry Obs :=
  (ω.toObservableMinimalCoordinatelessSouriauFisherContext beta J).toCoordinatelessSouriauFisherContext

/--
Fully constructive coordinateless Souriau/KMS/Fisher context on the cyclic
identity-modular branch, with KMS and Weyl identity-gauge content derived from
owned constructors rather than carried as explicit packets.
-/
@[rep_depth operator]
def toCyclicCoordinatelessSouriauFisherContext
    (beta : ℝ)
    (J : OperatorSouriauMoment (H := H) Symmetry)
    (sld : Tangent → Obs) :
    CyclicCoordinatelessSouriauFisherContext (H := H) Symmetry Tangent where
  state := ω
  beta := beta
  souriauMoment := J
  fisherMetric := ω.sldQuantumFisherMetric sld
  weylGauge := identityWeylAlgebraGauge (H := H) ω.state

/--
Constructive coordinateless Souriau/KMS/Fisher packet on the cyclic identity
modular branch.

This proves the table entries that are constructible from the current repo
owners: algebraic state normalization, KMS identity, operator-valued Souriau
moment, SLD/Fisher symmetry, and Weyl identity-gauge invariance.
-/
@[rep_depth operator]
def toMinimalCoordinatelessSouriauFisherContext
    (beta : ℝ)
    (J : OperatorSouriauMoment (H := H) Symmetry)
    (sld : Tangent → Obs) :
    MinimalCoordinatelessSouriauFisherContext (H := H) Symmetry Tangent :=
  (ω.toMinimalCyclicCoordinatelessSouriauContext beta J sld).toMinimalCoordinatelessSouriauFisherContext

/--
Constructive coordinateless Souriau/KMS/Fisher packet on the cyclic identity
modular branch.

This now routes through the existing minimal constructive branch instead of
rebuilding the broad `kms`/`kms_state_eq`/Fisher/Weyl packet inline.
-/
@[rep_depth operator]
def toCoordinatelessSouriauFisherContext
    (beta : ℝ)
    (J : OperatorSouriauMoment (H := H) Symmetry)
    (sld : Tangent → Obs) :
    CoordinatelessSouriauFisherContext (H := H) Symmetry Tangent :=
  (ω.toMinimalCoordinatelessSouriauFisherContext beta J sld).toCoordinatelessSouriauFisherContext

/-- Search-facing theorem packet for the constructive coordinateless branch. -/
@[rep_depth operator]
theorem coordinateless_constructive_packet
    (beta : ℝ)
    (J : OperatorSouriauMoment (H := H) Symmetry)
    (sld : Tangent → Obs)
    (A B : Obs) (X Y : Tangent) :
    let C := ω.toCoordinatelessSouriauFisherContext beta J sld
    C.state.eval 1 = 1 ∧
    C.state.eval (A * C.sigma C.beta B) = C.state.eval (B * A) ∧
    C.souriauMoment.thermalGenerator =
      C.souriauMoment.momentOperator C.souriauMoment.geometricTemperature ∧
    C.fisherMetric.metric X Y = C.fisherMetric.metric Y X ∧
    C.state.eval (C.weylGauge.gauge A) = C.state.eval A := by
  intro C
  exact ⟨
    C.state.eval_one,
    C.kms_identity A B,
    C.souriau_thermalGenerator_eq_moment,
    C.fisher_metric_symm X Y,
    C.weyl_state_invariant A⟩

end CyclicAlgebraicState

end OperatorAlgebra

end InfoGeometry.Canonical.CoordinatelessSouriauKMSBridge
