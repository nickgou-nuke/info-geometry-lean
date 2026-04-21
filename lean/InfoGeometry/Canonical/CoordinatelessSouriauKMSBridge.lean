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

universe u v

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
    (Tangent : Type v) (ω : AlgebraicState (H := H)) where
  sld : Tangent → Obs
  metric : Tangent → Tangent → ℝ
  metric_eq_sld_readout :
    ∀ X Y : Tangent, metric X Y = ω.eval ((sld X) * (sld Y))
  symmetric : ∀ X Y : Tangent, metric X Y = metric Y X

namespace QuantumFisherSLDMetric

variable {Tangent : Type v} {ω : AlgebraicState (H := H)}
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
    (Symmetry : Type v) (Tangent : Type v) where
  state : AlgebraicState (H := H)
  sigma : AdditiveModularFlow (H := H)
  beta : ℝ
  kms : KMSState (H := H) sigma beta
  kms_state_eq : kms.state = state
  souriauMoment : OperatorSouriauMoment (H := H) Symmetry
  fisherMetric : QuantumFisherSLDMetric (H := H) Tangent state
  weylGauge : WeylAlgebraGauge (H := H) state

namespace CoordinatelessSouriauFisherContext

variable {Symmetry : Type v} {Tangent : Type v}
variable (C : CoordinatelessSouriauFisherContext (H := H) Symmetry Tangent)

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

end OperatorAlgebra

end InfoGeometry.Canonical.CoordinatelessSouriauKMSBridge
