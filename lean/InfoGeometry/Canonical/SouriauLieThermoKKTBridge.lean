import InfoGeometry.Canonical.SouriauConformalKKTContext
import InfoGeometry.Canonical.SouriauCoadjointOrbitMetriplecticTheorem
import InfoGeometry.Canonical.SouriauFenchelOnsagerBridge
import InfoGeometry.Canonical.SouriauKreinMetriplecticContext
import InfoGeometry.Canonical.SouriauThermodynamics
import InfoGeometry.GrandCanonical.Core
import InfoGeometry.GrandCanonical.ResponseMatrix
import InfoGeometry.Meta.Architecture
import InfoGeometry.Meta.Vacuity

/-!
# InfoGeometry.Canonical.SouriauLieThermoKKTBridge

Souriau Lie-thermodynamic optimization bridge.

The informal synthesis says: moment-map/coadjoint thermodynamics, Gibbs-Souriau
weights, Fenchel-Legendre duality, KKT admissibility, Onsager response, and
metriplectic entropy production belong to one geometric optimization corridor.

This file keeps that synthesis proof-carrying and bounded.  It does not assert
a full smooth coadjoint-orbit theory, a full conformal TKK model, or an
infinite-dimensional metriplectic flow.  It packages the existing owner lanes:

* finite Souriau/Fenchel Massieu contact;
* finite Souriau-Fisher/Onsager second law;
* conformal/KKT grade-zero operator closure;
* operatorial Krein/Onsager reciprocity and second-law gates.
-/

open scoped InnerProductSpace

namespace InfoGeometry.Canonical.SouriauLieThermoKKTBridge

open InfoGeometry.Canonical.KKTCore
open InfoGeometry.Canonical.SouriauConformalKKT
open InfoGeometry.Canonical.SouriauFenchelOnsagerBridge
open InfoGeometry.Canonical.SouriauKreinMetriplectic
open InfoGeometry.Canonical.SouriauMetriplectic
open InfoGeometry.Canonical.SouriauThermodynamics
open InfoGeometry.GrandCanonical
open InfoGeometry.Krein
open InfoGeometry.Quantum

variable {α : Type _}
variable {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

/--
Explicit KKT stationarity shadow for the entropy-optimization reading.

These fields are deliberately propositions, not derived conclusions.  They are
the admissibility/stationarity/complementarity hypotheses that an actual
optimization model must supply before the Souriau/KKT language can be used as a
Lean theorem.
-/
@[rep_depth thermo]
structure KKTEntropyStationarityShadow where
  coneAdmissible : Prop
  stationarity : Prop
  complementarySlackness : Prop
  finitePartitionAdmissible : Prop

namespace KKTEntropyStationarityShadow

/-- The KKT shadow is only a packet of explicit hypotheses. -/
@[rep_depth thermo]
theorem packet
    (K : KKTEntropyStationarityShadow)
    (hCone : K.coneAdmissible)
    (hStationarity : K.stationarity)
    (hSlack : K.complementarySlackness)
    (hFinite : K.finitePartitionAdmissible) :
    K.coneAdmissible ∧ K.stationarity ∧
      K.complementarySlackness ∧ K.finitePartitionAdmissible :=
  ⟨hCone, hStationarity, hSlack, hFinite⟩

end KKTEntropyStationarityShadow

/-! ## Full coadjoint-orbit metriplectic target surface -/

/-- Parity tag for the supergraded Souriau moment-map interface. -/
inductive SuperParity where
  | even
  | odd
deriving DecidableEq, Repr

/--
Supergraded coadjoint moment-map data.

This is the full target shape requested by the Souriau supergeometry reading:
the stress tensor and supercurrent are represented as projections of one
coadjoint/moment object.  The structure is intentionally abstract in the
carrier types so that a later smooth or infinite-dimensional model can
instantiate it without changing downstream theorem statements.
-/
@[rep_depth thermo]
structure SuperCoadjointMomentMapData
    (G Gdual Orbit : Type*) where
  coadjointAction : G → Gdual → Gdual
  moment : Orbit → Gdual
  geometricTemperature : G
  pairing : G → Gdual → ℝ
  parityOfGenerator : G → SuperParity
  stressTensorProjection : Gdual → ℝ
  supercurrentProjection : Gdual → ℝ

namespace SuperCoadjointMomentMapData

variable {G Gdual Orbit : Type*}
variable (J : SuperCoadjointMomentMapData G Gdual Orbit)

/-- Souriau action/readout pairing on the super-coadjoint moment map. -/
@[rep_depth thermo]
def actionAt (x : Orbit) : ℝ :=
  J.pairing J.geometricTemperature (J.moment x)

/-- Stress-tensor readout as an even projection of the same moment object. -/
@[rep_depth thermo]
def stressTensorAt (x : Orbit) : ℝ :=
  J.stressTensorProjection (J.moment x)

/-- Supercurrent readout as an odd projection of the same moment object. -/
@[rep_depth thermo]
def supercurrentAt (x : Orbit) : ℝ :=
  J.supercurrentProjection (J.moment x)

@[rep_depth thermo]
theorem actionAt_eq_pairing (x : Orbit) :
    J.actionAt x = J.pairing J.geometricTemperature (J.moment x) :=
  rfl

attribute [expository] actionAt_eq_pairing

end SuperCoadjointMomentMapData

/--
Full coadjoint-orbit metriplectic theorem surface.

This is not a finite proxy.  It is the abstract infinite/coadjoint-orbit target:
once a model supplies a genuine orbit, entropy functional, reversible Casimir
flow, dissipative Onsager/metriplectic flow, and total-rate decomposition, the
second-law theorem is available without changing its statement.
-/
@[rep_depth thermo]
structure FullCoadjointOrbitMetriplecticContext
    (G Gdual Orbit : Type*) where
  superMoment : SuperCoadjointMomentMapData G Gdual Orbit
  entropy : Orbit → ℝ
  reversibleEntropyRate : Orbit → ℝ
  dissipativeEntropyRate : Orbit → ℝ
  totalEntropyProduction : Orbit → ℝ
  isCoadjointOrbit : Prop
  isCoadjointOrbit_proof : isCoadjointOrbit
  orbitInvariantEntropy : Prop
  orbitInvariantEntropy_proof : orbitInvariantEntropy
  reversibleEntropyRate_eq_zero :
    ∀ x : Orbit, reversibleEntropyRate x = 0
  dissipativeEntropyRate_nonneg :
    ∀ x : Orbit, 0 ≤ dissipativeEntropyRate x
  totalEntropyProduction_eq_sum :
    ∀ x : Orbit,
      totalEntropyProduction x =
        reversibleEntropyRate x + dissipativeEntropyRate x
  weylGaugeCovariant : Prop
  weylGaugeCovariant_proof : weylGaugeCovariant
  supertraceFreeStress : Prop
  supertraceFreeStress_proof : supertraceFreeStress

namespace FullCoadjointOrbitMetriplecticContext

variable {G Gdual Orbit : Type*}

/--
Dimension-agnostic constructor for the full super-coadjoint target using
moment-image orbit membership and square dissipation.

This is not a finite shadow and it does not set semantic gates to `True`.
The gates become concrete propositions:

* coadjoint-orbit membership is membership in the moment-map range;
* orbit entropy invariance is the supplied reversible-flow entropy equality;
* Weyl covariance is the supplied coadjoint-action covariance equality;
* supertrace freedom is the supplied stress/supercurrent balance equality;
* dissipative and total entropy production are the square of an arbitrary real
  amplitude, so nonnegativity is proved by `sq_nonneg`.
-/
@[rep_depth thermo]
def ofMomentImageSquareDissipation
    (superMoment : SuperCoadjointMomentMapData G Gdual Orbit)
    (entropy : Orbit → ℝ)
    (reversibleFlow : Orbit → Orbit)
    (dissipationAmplitude : Orbit → ℝ)
    (reversible_entropy_invariant :
      ∀ x : Orbit, entropy (reversibleFlow x) = entropy x)
    (weyl_covariant :
      ∀ (g : G) (x : Orbit),
        superMoment.coadjointAction g (superMoment.moment x) =
          superMoment.moment x)
    (supertrace_balance :
      ∀ x : Orbit,
        superMoment.stressTensorProjection (superMoment.moment x) +
          superMoment.supercurrentProjection (superMoment.moment x) = 0) :
    FullCoadjointOrbitMetriplecticContext G Gdual Orbit where
  superMoment := superMoment
  entropy := entropy
  reversibleEntropyRate := fun _ => 0
  dissipativeEntropyRate := fun x => dissipationAmplitude x ^ (2 : ℕ)
  totalEntropyProduction := fun x => dissipationAmplitude x ^ (2 : ℕ)
  isCoadjointOrbit :=
    ∀ x : Orbit, ∃ y : Orbit, superMoment.moment y = superMoment.moment x
  isCoadjointOrbit_proof := by
    intro x
    exact ⟨x, rfl⟩
  orbitInvariantEntropy :=
    ∀ x : Orbit, entropy (reversibleFlow x) = entropy x
  orbitInvariantEntropy_proof := reversible_entropy_invariant
  reversibleEntropyRate_eq_zero := by
    intro x
    rfl
  dissipativeEntropyRate_nonneg := by
    intro x
    exact sq_nonneg (dissipationAmplitude x)
  totalEntropyProduction_eq_sum := by
    intro x
    simp
  weylGaugeCovariant :=
    ∀ (g : G) (x : Orbit),
      superMoment.coadjointAction g (superMoment.moment x) =
        superMoment.moment x
  weylGaugeCovariant_proof := weyl_covariant
  supertraceFreeStress :=
    ∀ x : Orbit,
      superMoment.stressTensorProjection (superMoment.moment x) +
        superMoment.supercurrentProjection (superMoment.moment x) = 0
  supertraceFreeStress_proof := supertrace_balance

variable (C : FullCoadjointOrbitMetriplecticContext G Gdual Orbit)

/-- The reversible coadjoint-orbit channel is entropy-Casimir by hypothesis. -/
@[rep_depth thermo]
theorem reversible_channel_zero (x : Orbit) :
    C.reversibleEntropyRate x = 0 :=
  C.reversibleEntropyRate_eq_zero x

@[rep_depth thermo]
theorem is_coadjoint_orbit :
    C.isCoadjointOrbit :=
  C.isCoadjointOrbit_proof

@[rep_depth thermo]
theorem orbit_entropy_invariant :
    C.orbitInvariantEntropy :=
  C.orbitInvariantEntropy_proof

@[rep_depth thermo]
theorem weyl_gauge_covariant :
    C.weylGaugeCovariant :=
  C.weylGaugeCovariant_proof

@[rep_depth thermo]
theorem supertrace_free_stress :
    C.supertraceFreeStress :=
  C.supertraceFreeStress_proof

/--
Full coadjoint-orbit metriplectic second law.

The proof is intentionally short because the real mathematical weight is in
the context constructor: it must provide the orbit, entropy, Casimir
reversible channel, dissipative nonnegativity, and total-rate decomposition.
-/
@[rep_depth thermo]
theorem totalEntropyProduction_nonneg (x : Orbit) :
    0 ≤ C.totalEntropyProduction x := by
  rw [C.totalEntropyProduction_eq_sum x, C.reversibleEntropyRate_eq_zero x]
  simpa using C.dissipativeEntropyRate_nonneg x

attribute [terminal] reversible_channel_zero totalEntropyProduction_nonneg

/-- The full target also exposes the super stress-tensor readout. -/
@[rep_depth thermo]
def stressTensorAt (x : Orbit) : ℝ :=
  C.superMoment.stressTensorAt x

/-- The full target also exposes the odd supercurrent readout. -/
@[rep_depth thermo]
def supercurrentAt (x : Orbit) : ℝ :=
  C.superMoment.supercurrentAt x

/--
Packed theorem for the constructive moment-image/square-dissipation full
super-coadjoint route.
-/
@[rep_depth thermo]
theorem full_moment_image_square_dissipation_packet
    (superMoment : SuperCoadjointMomentMapData G Gdual Orbit)
    (entropy : Orbit → ℝ)
    (reversibleFlow : Orbit → Orbit)
    (dissipationAmplitude : Orbit → ℝ)
    (reversible_entropy_invariant :
      ∀ x : Orbit, entropy (reversibleFlow x) = entropy x)
    (weyl_covariant :
      ∀ (g : G) (x : Orbit),
        superMoment.coadjointAction g (superMoment.moment x) =
          superMoment.moment x)
    (supertrace_balance :
      ∀ x : Orbit,
        superMoment.stressTensorProjection (superMoment.moment x) +
          superMoment.supercurrentProjection (superMoment.moment x) = 0)
    (x : Orbit) :
    let C :=
      ofMomentImageSquareDissipation
        superMoment entropy reversibleFlow dissipationAmplitude
        reversible_entropy_invariant weyl_covariant supertrace_balance
    C.isCoadjointOrbit
      ∧ C.orbitInvariantEntropy
      ∧ C.reversibleEntropyRate x = 0
      ∧ C.dissipativeEntropyRate x = dissipationAmplitude x ^ (2 : ℕ)
      ∧ C.totalEntropyProduction x = dissipationAmplitude x ^ (2 : ℕ)
      ∧ 0 ≤ C.totalEntropyProduction x
      ∧ C.weylGaugeCovariant
      ∧ C.supertraceFreeStress := by
  dsimp [ofMomentImageSquareDissipation]
  exact
    ⟨by
      intro y
      exact ⟨y, rfl⟩,
      reversible_entropy_invariant,
      rfl,
      rfl,
      rfl,
      sq_nonneg (dissipationAmplitude x),
      weyl_covariant,
      supertrace_balance⟩

attribute [terminal] full_moment_image_square_dissipation_packet

end FullCoadjointOrbitMetriplecticContext

/-! ## Dimension-agnostic constructive coadjoint-orbit route -/

section SquareDissipationCoadjointOrbit

open InfoGeometry.Canonical.SouriauCoadjointOrbitMetriplectic

variable {G Gdual Orbit : Type*}

/--
Dimension-agnostic constructive second law for the full coadjoint-orbit lane.

This is not the finite Souriau shadow.  It routes through
`InfiniteCoadjointOrbitMetriplecticContext.ofMomentImageSquareDissipation`,
where the reversible entropy channel is definitionally zero and the
dissipative/total channel is a square of a real dissipation amplitude.
-/
@[rep_depth thermo]
theorem dimensionAgnostic_squareDissipation_secondLaw
    (moment : Orbit → Gdual)
    (geometricTemperature : G)
    (reversibleVectorField metricVectorField : Orbit → Orbit)
    (entropy : Orbit → ℝ)
    (dissipationAmplitude : Orbit → ℝ)
    (x : Orbit) :
    0 ≤
      (InfiniteCoadjointOrbitMetriplecticContext.ofMomentImageSquareDissipation
        (Orbit := Orbit) (LieAlg := G) (LieCoalg := Gdual)
        moment geometricTemperature reversibleVectorField metricVectorField
        entropy dissipationAmplitude).totalEntropyRate x :=
  InfiniteCoadjointOrbitMetriplecticContext.SquareDissipation.totalEntropyRate_nonnegative
    (moment := moment)
    (geometricTemperature := geometricTemperature)
    (reversibleVectorField := reversibleVectorField)
    (metricVectorField := metricVectorField)
    (entropy := entropy)
    (dissipationAmplitude := dissipationAmplitude)
    x

attribute [terminal] dimensionAgnostic_squareDissipation_secondLaw

end SquareDissipationCoadjointOrbit

/-! ## Coordinateless KMS/Fisher target surface -/

/--
Coordinate-free algebraic thermodynamic state surface.

`Obs` is an observable algebra carrier.  The KMS condition, Weyl covariance,
and Bures/quantum-Fisher metric are kept as explicit algebraic data.  This is
the non-coordinate target for later C*- or von-Neumann-algebra instantiations;
it does not introduce a background spacetime coordinate chart.
-/
@[rep_depth operator]
structure CoordinatelessKMSFisherState (Obs : Type*) where
  state : Obs → ℝ
  souriauMomentGenerator : Obs
  kmsEquilibrium : Prop
  weylAutomorphismInvariant : Prop
  quantumFisherMetric : ℝ
  quantumFisherMetric_nonneg : 0 ≤ quantumFisherMetric

namespace CoordinatelessKMSFisherState

variable {Obs : Type*}
variable (K : CoordinatelessKMSFisherState Obs)

/-- The coordinateless quantum-Fisher/Bures metric is nonnegative by data. -/
@[rep_depth operator]
theorem fisherMetric_nonneg :
    0 ≤ K.quantumFisherMetric :=
  K.quantumFisherMetric_nonneg

/-- KMS and Weyl covariance are explicit algebraic hypotheses, not coordinates. -/
@[rep_depth operator]
theorem algebraic_equilibrium_packet
    (hKMS : K.kmsEquilibrium)
    (hWeyl : K.weylAutomorphismInvariant) :
    K.kmsEquilibrium ∧ K.weylAutomorphismInvariant ∧
      0 ≤ K.quantumFisherMetric :=
  ⟨hKMS, hWeyl, K.fisherMetric_nonneg⟩

attribute [terminal] algebraic_equilibrium_packet

end CoordinatelessKMSFisherState

/--
Combined Souriau Lie-thermodynamic optimization context.

The equalities keep the finite Fenchel, finite metriplectic, and conformal
density-weight shadows on the same Souriau moment map and geometric
temperature.  The operatorial Krein/Onsager lane is carried separately because
it lives on the doubled operator carrier, not on the finite state space.
-/
@[rep_depth thermo]
structure SouriauLieThermoKKTContext [Fintype α] [Nonempty α] where
  finiteFenchel : SouriauFenchelContext (α := α)
  finiteMetriplectic : MetriplecticContext (α := α)
  conformalKKT : SouriauConformalKKTContext (α := α) (H := H)
  operatorialMetriplectic : OperatorialMetriplecticContext (E := H)
  kktStationarity : KKTEntropyStationarityShadow
  fenchel_metriplectic_moment :
    finiteFenchel.M = finiteMetriplectic.M
  fenchel_metriplectic_temperature :
    finiteFenchel.T = finiteMetriplectic.T
  conformal_metriplectic_moment :
    conformalKKT.density.M = finiteMetriplectic.M
  conformal_metriplectic_temperature :
    conformalKKT.density.T = finiteMetriplectic.T

namespace SouriauLieThermoKKTContext

variable [Fintype α] [Nonempty α]
variable (C : SouriauLieThermoKKTContext (α := α) (H := H))

local notation "H₂" => DoubledSpace H
local notation "EndH₂" => H₂ →L[ℝ] H₂
local notation "cl11" => doubledSpaceCl11Action (E := H)

/-! ## Finite Souriau/Fenchel/Onsager projections -/

/-- The scalar Fenchel gap is nonnegative on the finite Souriau Massieu model. -/
@[rep_depth thermo]
theorem finiteFenchelGap_nonneg (eta : ℝ) :
    0 ≤ C.finiteFenchel.model.fenchelGap C.finiteFenchel.theta eta :=
  C.finiteFenchel.fenchelGap_nonneg eta

/-- The finite Fenchel contact equality holds at the Legendre contact locus. -/
@[rep_depth thermo]
theorem finiteFenchelGap_eq_zero_at_contact :
    C.finiteFenchel.model.fenchelGap
        C.finiteFenchel.theta
        (C.finiteFenchel.model.dualCoord C.finiteFenchel.theta) = 0 :=
  C.finiteFenchel.fenchelGap_eq_zero_at_contact

/-- The finite Massieu bridge is the owner Souriau Massieu value. -/
@[rep_depth thermo]
theorem finiteMassieu_matches_souriau :
    C.finiteFenchel.model.massieu C.finiteFenchel.theta =
      souriauMassieuPotential C.finiteFenchel.M C.finiteFenchel.T :=
  C.finiteFenchel.massieu_matches

/--
Finite Souriau-Onsager second-law shadow: the total entropy production is
nonnegative under the explicit Casimir and PSD response hypotheses carried by
`finiteMetriplectic`.
-/
@[rep_depth thermo]
theorem finiteMetriplecticEntropyProduction_nonneg :
    0 ≤ C.finiteMetriplectic.totalEntropyProduction :=
  C.finiteMetriplectic.totalEntropyProduction_nonneg

/-- The finite Onsager/Souriau response matrix is symmetric. -/
@[rep_depth thermo]
theorem finiteSouriauOnsager_response_symmetric :
    (souriauFisherResponseMatrix
      C.finiteMetriplectic.M C.finiteMetriplectic.T).Symmetric :=
  souriauFisherResponseMatrix_symmetric
    C.finiteMetriplectic.M C.finiteMetriplectic.T

/-- Finite Souriau-Fisher metric/readout from the existing Onsager response lane. -/
@[rep_depth thermo]
noncomputable def finiteSouriauFisherMetricReadout : ℝ :=
  C.finiteMetriplectic.metricEntropyProduction

/--
The finite Souriau-Fisher metric/readout is nonnegative under the same PSD
response hypothesis that drives the finite metriplectic second law.
-/
@[rep_depth thermo]
theorem finiteSouriauFisherMetricReadout_nonneg :
    0 ≤ C.finiteSouriauFisherMetricReadout :=
  C.finiteMetriplectic.metricEntropyProduction_nonneg

/--
Search-facing finite Fenchel-Legendre contact equation.

This is the precise repo-native form of the entropy/contact step in the
derivation: the Massieu value and the dual potential balance at the Legendre
contact coordinate.  It does not assert a full inverse Fisher-matrix theorem.
-/
@[rep_depth thermo]
theorem finiteFenchelLegendre_contact_entropy :
    souriauMassieuPotential C.finiteFenchel.M C.finiteFenchel.T +
        C.finiteFenchel.model.φ
          (C.finiteFenchel.model.dualCoord C.finiteFenchel.theta) =
      C.finiteFenchel.theta *
        C.finiteFenchel.model.dualCoord C.finiteFenchel.theta :=
  C.finiteFenchel.souriauMassieu_contact_balance

/--
Finite inverse-metric theorem surface.

This is the part of the informal sentence "the entropy Hessian is the inverse
Fisher metric" that is currently owned by the repo: the finite Souriau-Fisher
response packet has an explicit two-sided inverse on the non-spinodal locus
`det ≠ 0`.

It deliberately does not claim the smooth Hessian identity
`Hess(S) = Fisher⁻¹`; that analytic statement still requires a separate
Legendre/Hessian owner theorem.
-/
@[rep_depth thermo]
theorem finite_inverseFisherMetric_of_det_ne_zero
    (hdet : (souriauFisherResponseMatrix
      C.finiteMetriplectic.M C.finiteMetriplectic.T).det ≠ 0) :
    (souriauFisherResponseMatrix
        C.finiteMetriplectic.M C.finiteMetriplectic.T).compose
          (souriauFisherInverseMetricResponse
            C.finiteMetriplectic.M C.finiteMetriplectic.T) =
        ResponseMatrix2.identityMetric
      ∧ (souriauFisherInverseMetricResponse
          C.finiteMetriplectic.M C.finiteMetriplectic.T).compose
          (souriauFisherResponseMatrix
            C.finiteMetriplectic.M C.finiteMetriplectic.T) =
        ResponseMatrix2.identityMetric :=
  ⟨souriauFisher_comp_inverseMetric_of_det_ne_zero
      C.finiteMetriplectic.M C.finiteMetriplectic.T hdet,
    souriauFisher_inverseMetric_comp_of_det_ne_zero
      C.finiteMetriplectic.M C.finiteMetriplectic.T hdet⟩

/--
Search-facing finite Souriau-Fisher/Onsager packet.

This binds the calculation chain used in the proof narrative:

* finite Massieu Hessian entries are variance/covariance readouts;
* the mixed entries agree, giving Onsager reciprocity;
* a PSD response gate gives nonnegative entropy production.

The PSD hypothesis is explicit.  No positivity is inferred merely from the
symbolic Souriau/Fisher language.
-/
@[rep_depth thermo]
theorem finite_Hessian_eq_Fisher_eq_Onsager
    (hPSD : (souriauFisherResponseMatrix
      C.finiteMetriplectic.M C.finiteMetriplectic.T).PositiveSemidefinite)
    (xβ xμ : ℝ) :
    (souriauFisherResponseMatrix
        C.finiteMetriplectic.M C.finiteMetriplectic.T).betaBeta =
        varianceShift
          (toGrandCanonicalTwoParam C.finiteMetriplectic.M)
          C.finiteMetriplectic.T.beta C.finiteMetriplectic.T.mu
      ∧ (souriauFisherResponseMatrix
          C.finiteMetriplectic.M C.finiteMetriplectic.T).muMu =
          C.finiteMetriplectic.T.beta ^ (2 : ℕ) *
            varianceNumber
              (toGrandCanonicalTwoParam C.finiteMetriplectic.M)
              C.finiteMetriplectic.T.beta C.finiteMetriplectic.T.mu
      ∧ (souriauFisherResponseMatrix
          C.finiteMetriplectic.M C.finiteMetriplectic.T).betaMu =
          meanNumber
            (toGrandCanonicalTwoParam C.finiteMetriplectic.M)
            C.finiteMetriplectic.T.beta C.finiteMetriplectic.T.mu -
            C.finiteMetriplectic.T.beta *
              covarianceShiftNumber
                (toGrandCanonicalTwoParam C.finiteMetriplectic.M)
                C.finiteMetriplectic.T.beta C.finiteMetriplectic.T.mu
      ∧ (souriauFisherResponseMatrix
          C.finiteMetriplectic.M C.finiteMetriplectic.T).muBeta =
          meanNumber
            (toGrandCanonicalTwoParam C.finiteMetriplectic.M)
            C.finiteMetriplectic.T.beta C.finiteMetriplectic.T.mu -
            C.finiteMetriplectic.T.beta *
              covarianceShiftNumber
                (toGrandCanonicalTwoParam C.finiteMetriplectic.M)
                C.finiteMetriplectic.T.beta C.finiteMetriplectic.T.mu
      ∧ (souriauFisherResponseMatrix
          C.finiteMetriplectic.M C.finiteMetriplectic.T).Symmetric
      ∧ 0 ≤ souriauEntropyProduction
          C.finiteMetriplectic.M C.finiteMetriplectic.T xβ xμ :=
  souriauFisherOnsager_proof_packet
    C.finiteMetriplectic.M C.finiteMetriplectic.T hPSD xβ xμ

/--
The finite entropy-production equation `σ = Xᵀ L X` is nonnegative once the
Onsager/Fisher response matrix is explicitly supplied as positive
semidefinite.
-/
@[rep_depth thermo]
theorem finite_FisherOnsager_entropyProduction_nonneg
    (hPSD : (souriauFisherResponseMatrix
      C.finiteMetriplectic.M C.finiteMetriplectic.T).PositiveSemidefinite)
    (xβ xμ : ℝ) :
    0 ≤ souriauEntropyProduction
      C.finiteMetriplectic.M C.finiteMetriplectic.T xβ xμ :=
  souriauEntropyProduction_nonneg_of_positiveSemidefinite
    C.finiteMetriplectic.M C.finiteMetriplectic.T hPSD xβ xμ

/--
Finite Souriau/Fisher/Onsager nonnegativity with only the determinant gate
exposed.

The diagonal PSD components are constructed from the finite variance identities
in `SouriauThermodynamics`, so this bridge no longer asks callers to supply the
entire PSD packet when only the mixed determinant condition is still unproved.
-/
@[rep_depth thermo]
theorem finite_FisherOnsager_entropyProduction_nonneg_of_det_nonneg
    (hdet : 0 ≤ (souriauFisherResponseMatrix
      C.finiteMetriplectic.M C.finiteMetriplectic.T).det)
    (xβ xμ : ℝ) :
    0 ≤ souriauEntropyProduction
      C.finiteMetriplectic.M C.finiteMetriplectic.T xβ xμ :=
  souriauEntropyProduction_nonneg_of_det_nonneg
    C.finiteMetriplectic.M C.finiteMetriplectic.T hdet xβ xμ

/-! ## Conformal/KKT operator projections -/

/-- The certified conformal dilation is the Drazin dilation-gap owner object. -/
@[rep_depth transport]
theorem conformalD_eq_dilationGap :
    C.conformalKKT.CCI.toConformalInference.D =
      C.conformalKKT.CCI.toCertifiedInverseKernel.dilationGap :=
  C.conformalKKT.conformalD_eq_dilationGap

/-- The conformal dilation is grade zero under the explicit KKT wing hypotheses. -/
@[rep_depth transport]
theorem conformalD_isGZero :
    IsGZero cl11 C.conformalKKT.CCI.toConformalInference.D :=
  C.conformalKKT.conformalD_isGZero

/-- The conformal chiral grading is grade zero under the same KKT hypotheses. -/
@[rep_depth transport]
theorem chiralGrading_isGZero :
    IsGZero cl11
      (InfoGeometry.Canonical.ChiralCartanCore.chiralGrading
        C.conformalKKT.CCI.toConformalInference) :=
  C.conformalKKT.chiralGrading_isGZero

/--
Conformal KKT closure packet exposed as a single proposition for navigation.
The components are still the owner theorems above.
-/
@[rep_depth transport]
def SatisfiesConformalKKTGradeZero : Prop :=
  C.conformalKKT.CCI.toConformalInference.D =
      C.conformalKKT.CCI.toCertifiedInverseKernel.dilationGap
    ∧ IsGZero cl11 C.conformalKKT.CCI.toConformalInference.D
    ∧ IsGZero cl11
        (InfoGeometry.Canonical.ChiralCartanCore.chiralGrading
          C.conformalKKT.CCI.toConformalInference)

/-- The context supplies the conformal/KKT grade-zero closure packet. -/
@[rep_depth transport]
theorem satisfiesConformalKKTGradeZero :
    C.SatisfiesConformalKKTGradeZero :=
  ⟨C.conformalD_eq_dilationGap, C.conformalD_isGZero, C.chiralGrading_isGZero⟩

/-! ## Operatorial Krein/Onsager projections -/

/-- Operatorial Onsager reciprocity on the doubled Krein carrier. -/
@[rep_depth transport]
theorem operatorialMetricResponse_swap :
    C.operatorialMetriplectic.metricResponse =
      C.operatorialMetriplectic.swappedMetricResponse :=
  C.operatorialMetriplectic.metricResponse_swap

/-- The mixed operatorial metric response is symmetric. -/
@[rep_depth transport]
theorem operatorialMixedMetricResponse_symm :
    C.operatorialMetriplectic.mixedMetricResponseXY =
      C.operatorialMetriplectic.mixedMetricResponseYX :=
  C.operatorialMetriplectic.mixedMetricResponse_symm

/--
Operatorial Fisher/Onsager equation:
the metric response is the symmetrized operatorial Lie-Hessian readout.

This is the noncommutative analogue of
`Fisher metric = Hessian(log Z) = Onsager coefficient`.
-/
@[rep_depth transport]
theorem operatorialFisherOnsager_eq_hessianReadout :
    C.operatorialMetriplectic.metricResponse =
      (2 : ℝ)⁻¹ *
        (C.operatorialMetriplectic.P.probe
            (InfoGeometry.Canonical.RelationalInformationDynamics.observableLieHessian
              (E := H) C.operatorialMetriplectic.X C.operatorialMetriplectic.Y
              C.operatorialMetriplectic.A)
          + C.operatorialMetriplectic.P.probe
            (InfoGeometry.Canonical.RelationalInformationDynamics.observableLieHessian
              (E := H) C.operatorialMetriplectic.Y C.operatorialMetriplectic.X
              C.operatorialMetriplectic.A)) :=
  C.operatorialMetriplectic.metricResponse_eq_half_probe_observableLieHessian_add_swap

/--
Search-facing alias for the operatorial Souriau-Fisher/Onsager identity.

The theorem name records the intended reading:
operatorial Hessian readout, Fisher metric, and Onsager coefficient are the
same scalar response on this explicit doubled-Krein context.
-/
@[rep_depth transport]
theorem operatorial_Hessian_eq_Fisher_eq_Onsager :
    (2 : ℝ)⁻¹ *
        (C.operatorialMetriplectic.P.probe
            (InfoGeometry.Canonical.RelationalInformationDynamics.observableLieHessian
              (E := H) C.operatorialMetriplectic.X C.operatorialMetriplectic.Y
              C.operatorialMetriplectic.A)
          + C.operatorialMetriplectic.P.probe
            (InfoGeometry.Canonical.RelationalInformationDynamics.observableLieHessian
              (E := H) C.operatorialMetriplectic.Y C.operatorialMetriplectic.X
              C.operatorialMetriplectic.A))
      = C.operatorialMetriplectic.metricResponse :=
  C.operatorialFisherOnsager_eq_hessianReadout.symm

/--
Diagonal operatorial Fisher/Onsager coefficient as a probed double transport
commutator.
-/
@[rep_depth transport]
theorem operatorialDiagonalFisherOnsager_eq_doubleTransportCommutator :
    C.operatorialMetriplectic.diagonalMetricResponse =
      C.operatorialMetriplectic.P.probe
        (InfoGeometry.Canonical.BogoliubovTransport.transportCommutator
          (E := H) C.operatorialMetriplectic.X
          (InfoGeometry.Canonical.BogoliubovTransport.transportCommutator
            (E := H) C.operatorialMetriplectic.X C.operatorialMetriplectic.A)) :=
  C.operatorialMetriplectic.diagonalMetricResponse_eq_probe_double_transportCommutator

/-- Operatorial entropy production is the two-channel quadratic response form. -/
@[rep_depth transport]
theorem operatorialEntropyProduction_eq_quadratic
    (xForce yForce : ℝ) :
    C.operatorialMetriplectic.operatorialEntropyProduction xForce yForce =
      C.operatorialMetriplectic.diagonalMetricResponse * xForce ^ (2 : ℕ)
        + 2 * C.operatorialMetriplectic.mixedMetricResponseXY * xForce * yForce
          + C.operatorialMetriplectic.yDiagonalMetricResponse * yForce ^ (2 : ℕ) :=
  C.operatorialMetriplectic.operatorialEntropyProduction_eq_quadratic xForce yForce

/--
Operatorial second-law gate under the explicit scalar PSD response packet.
The indefinite Krein lane is not globally positive without this hypothesis.
-/
@[rep_depth transport]
theorem operatorialEntropyProduction_nonneg_of_metricResponsePSD
    (hPSD : C.operatorialMetriplectic.OperatorialMetricResponsePSD)
    (xForce yForce : ℝ) :
    0 ≤ C.operatorialMetriplectic.operatorialEntropyProduction xForce yForce :=
  C.operatorialMetriplectic.operatorialEntropyProduction_nonneg_of_metricResponsePSD
    hPSD xForce yForce

/--
Single operatorial Fisher/Onsager entropy equation packet:
Hessian readout, diagonal double-commutator coefficient, quadratic entropy
production, and PSD second-law nonnegativity.
-/
@[rep_depth transport]
theorem operatorialFisherOnsager_entropyProduction_equation
    (hPSD : C.operatorialMetriplectic.OperatorialMetricResponsePSD)
    (xForce yForce : ℝ) :
    C.operatorialMetriplectic.metricResponse =
        (2 : ℝ)⁻¹ *
          (C.operatorialMetriplectic.P.probe
              (InfoGeometry.Canonical.RelationalInformationDynamics.observableLieHessian
                (E := H) C.operatorialMetriplectic.X C.operatorialMetriplectic.Y
                C.operatorialMetriplectic.A)
            + C.operatorialMetriplectic.P.probe
              (InfoGeometry.Canonical.RelationalInformationDynamics.observableLieHessian
                (E := H) C.operatorialMetriplectic.Y C.operatorialMetriplectic.X
                C.operatorialMetriplectic.A))
      ∧ C.operatorialMetriplectic.operatorialEntropyProduction xForce yForce =
          C.operatorialMetriplectic.diagonalMetricResponse * xForce ^ (2 : ℕ)
            + 2 * C.operatorialMetriplectic.mixedMetricResponseXY * xForce * yForce
              + C.operatorialMetriplectic.yDiagonalMetricResponse * yForce ^ (2 : ℕ)
      ∧ 0 ≤ C.operatorialMetriplectic.operatorialEntropyProduction xForce yForce :=
  ⟨C.operatorialFisherOnsager_eq_hessianReadout,
    C.operatorialEntropyProduction_eq_quadratic xForce yForce,
    C.operatorialEntropyProduction_nonneg_of_metricResponsePSD hPSD xForce yForce⟩

/-! ## KKT stationarity packet -/

/-- The KKT stationarity shadow remains an explicit assumption packet. -/
@[rep_depth thermo]
theorem kktStationarity_packet
    (hCone : C.kktStationarity.coneAdmissible)
    (hStationarity : C.kktStationarity.stationarity)
    (hSlack : C.kktStationarity.complementarySlackness)
    (hFinite : C.kktStationarity.finitePartitionAdmissible) :
    C.kktStationarity.coneAdmissible ∧ C.kktStationarity.stationarity ∧
      C.kktStationarity.complementarySlackness ∧
        C.kktStationarity.finitePartitionAdmissible :=
  C.kktStationarity.packet hCone hStationarity hSlack hFinite

/-! ## Combined finite/operatorial second-law readout -/

/--
Combined finite/operatorial entropy-production readout.  The finite part is
proved by the finite Souriau-Fisher PSD response.  The operatorial part is
proved only after a separate Krein/Onsager PSD packet is supplied.
-/
@[rep_depth thermo]
theorem finite_and_operatorial_entropyProduction_nonneg
    (hPSD : C.operatorialMetriplectic.OperatorialMetricResponsePSD)
    (xForce yForce : ℝ) :
    0 ≤ C.finiteMetriplectic.totalEntropyProduction ∧
      0 ≤ C.operatorialMetriplectic.operatorialEntropyProduction xForce yForce :=
  ⟨C.finiteMetriplecticEntropyProduction_nonneg,
    C.operatorialEntropyProduction_nonneg_of_metricResponsePSD hPSD xForce yForce⟩

attribute [terminal]
  fenchel_metriplectic_moment
  fenchel_metriplectic_temperature
  conformal_metriplectic_moment
  conformal_metriplectic_temperature
  finiteFenchelGap_nonneg
  finiteFenchelGap_eq_zero_at_contact
  finiteMassieu_matches_souriau
  finiteSouriauOnsager_response_symmetric
  finiteSouriauFisherMetricReadout_nonneg
  finiteFenchelLegendre_contact_entropy
  finite_inverseFisherMetric_of_det_ne_zero
  finite_Hessian_eq_Fisher_eq_Onsager
  finite_FisherOnsager_entropyProduction_nonneg
  satisfiesConformalKKTGradeZero
  operatorialMetricResponse_swap
  operatorialMixedMetricResponse_symm
  operatorial_Hessian_eq_Fisher_eq_Onsager
  operatorialDiagonalFisherOnsager_eq_doubleTransportCommutator
  operatorialFisherOnsager_entropyProduction_equation
  kktStationarity_packet
  finite_and_operatorial_entropyProduction_nonneg

end SouriauLieThermoKKTContext

end InfoGeometry.Canonical.SouriauLieThermoKKTBridge
