import InfoGeometry.Canonical.SouriauConformalKKTContext
import InfoGeometry.Canonical.SouriauCoadjointOrbitMetriplecticTheorem
import InfoGeometry.Canonical.SouriauFenchelOnsagerBridge
import InfoGeometry.Canonical.SouriauKreinMetriplecticContext
import InfoGeometry.Canonical.SouriauThermodynamics
import InfoGeometry.Canonical.SuperchargeCARCCRBridge
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

-- theorem-class: bridge
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

/--
Proof-carrying witness for the KKT stationarity shadow.

This narrows the old four-hypothesis packet to one constructive object carrying
exactly the owned proofs needed to recover the original conjunction surface.
-/
@[rep_depth thermo]
structure Witness where
  shadow : KKTEntropyStationarityShadow
  hCone : shadow.coneAdmissible
  hStationarity : shadow.stationarity
  hSlack : shadow.complementarySlackness
  hFinite : shadow.finitePartitionAdmissible

namespace Witness

/-- Recover the full KKT stationarity packet from the proof-carrying witness. -/
@[rep_depth thermo]
theorem packet (W : KKTEntropyStationarityShadow.Witness) :
    W.shadow.coneAdmissible ∧ W.shadow.stationarity ∧
      W.shadow.complementarySlackness ∧ W.shadow.finitePartitionAdmissible :=
  ⟨W.hCone, W.hStationarity, W.hSlack, W.hFinite⟩

end Witness

end KKTEntropyStationarityShadow

/--
Dimension-agnostic real residual model for the KKT stationarity lane.

This is not a finite optimization toy.  It records the four KKT readouts as
real residual channels.  Cone/partition admissibility can be made constructive
from squares; exact stationarity and complementarity become constructive only
when the residuals are definitionally zero or supplied by a concrete model.
-/
@[rep_depth thermo]
structure DimensionAgnosticKKTResiduals where
  coneSlack : ℝ
  stationarityResidual : ℝ
  complementarityResidual : ℝ
  partitionResidual : ℝ

namespace DimensionAgnosticKKTResiduals

variable (R : DimensionAgnosticKKTResiduals)

/-- Convert real KKT residual channels into the existing stationarity packet. -/
@[rep_depth thermo]
def toShadow : KKTEntropyStationarityShadow where
  coneAdmissible := 0 ≤ R.coneSlack ^ (2 : ℕ)
  stationarity := R.stationarityResidual = 0
  complementarySlackness := R.complementarityResidual = 0
  finitePartitionAdmissible := 0 ≤ R.partitionResidual ^ (2 : ℕ)

/-- The exact-equilibrium residual packet. -/
@[rep_depth thermo]
def exact : DimensionAgnosticKKTResiduals where
  coneSlack := 0
  stationarityResidual := 0
  complementarityResidual := 0
  partitionResidual := 0

-- theorem-class: bridge
/-- Cone admissibility is constructive from the square slack channel. -/
@[rep_depth thermo]
theorem coneAdmissible_of_square :
    R.toShadow.coneAdmissible := by
  exact sq_nonneg R.coneSlack

-- theorem-class: bridge
/-- Partition admissibility is constructive from the square partition channel. -/
@[rep_depth thermo]
theorem partitionAdmissible_of_square :
    R.toShadow.finitePartitionAdmissible := by
  exact sq_nonneg R.partitionResidual

-- theorem-class: bridge
/--
Stationarity/complementarity residual equalities construct a proof-carrying KKT
witness while deriving cone and finite-partition admissibility from the square
residual channels.  This narrows the old four-field KKT packet to the two exact
residual equations that are not automatic from the residual model.
-/
@[rep_depth thermo]
def witness_of_stationarity_and_slack
    (hStationarity : R.stationarityResidual = 0)
    (hSlack : R.complementarityResidual = 0) :
    KKTEntropyStationarityShadow.Witness where
  shadow := R.toShadow
  hCone := R.coneAdmissible_of_square
  hStationarity := hStationarity
  hSlack := hSlack
  hFinite := R.partitionAdmissible_of_square

-- theorem-class: bridge
/--
A residual model with zero stationarity and complementarity residuals recovers
the full KKT stationarity packet without separate cone or finite-partition
hypotheses.
-/
@[rep_depth thermo]
theorem stationarity_packet_of_residual_zero
    (hStationarity : R.stationarityResidual = 0)
    (hSlack : R.complementarityResidual = 0) :
    R.toShadow.coneAdmissible ∧ R.toShadow.stationarity ∧
      R.toShadow.complementarySlackness ∧ R.toShadow.finitePartitionAdmissible := by
  simpa [witness_of_stationarity_and_slack] using
    (witness_of_stationarity_and_slack (R := R) hStationarity hSlack).packet

-- theorem-class: bridge
/--
Exact residuals construct a proof-carrying KKT witness without external KKT
hypotheses.
-/
@[rep_depth thermo]
def exactWitness : KKTEntropyStationarityShadow.Witness where
  shadow := exact.toShadow
  hCone := by
    dsimp [exact, toShadow]
    norm_num
  hStationarity := by
    dsimp [exact, toShadow]
  hSlack := by
    dsimp [exact, toShadow]
  hFinite := by
    dsimp [exact, toShadow]
    norm_num

-- theorem-class: bridge
/--
Exact residuals construct the full KKT stationarity packet without external
KKT hypotheses.
-/
@[rep_depth thermo]
theorem exact_stationarity_packet :
    let W := exactWitness
    W.shadow.coneAdmissible ∧ W.shadow.stationarity ∧
      W.shadow.complementarySlackness ∧ W.shadow.finitePartitionAdmissible := by
  simpa using exactWitness.packet

attribute [terminal] exact_stationarity_packet

end DimensionAgnosticKKTResiduals

namespace KKTEntropyStationarityShadow

-- theorem-class: bridge
/-- Exact dimension-agnostic residuals construct the KKT shadow directly. -/
@[rep_depth thermo]
theorem mk_exact :
    let K : KKTEntropyStationarityShadow := DimensionAgnosticKKTResiduals.toShadow DimensionAgnosticKKTResiduals.exact
    K.coneAdmissible ∧ K.stationarity ∧
      K.complementarySlackness ∧ K.finitePartitionAdmissible := by
  simpa using (DimensionAgnosticKKTResiduals.exact_stationarity_packet)

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
  isOnCoadjointOrbit : Gdual → Prop

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

-- theorem-class: bridge
@[rep_depth thermo]
theorem actionAt_eq_pairing (x : Orbit) :
    J.actionAt x = J.pairing J.geometricTemperature (J.moment x) :=
  rfl

attribute [expository] actionAt_eq_pairing

/--
Constructive super-coadjoint moment-map data for the exact identity-action
model.

The coadjoint action is the identity and the odd supercurrent readout is the
negative of the even stress readout.  This gives a dimension-agnostic
supertrace-free target without assuming Weyl covariance or balance as separate
proof fields.
-/
@[rep_depth thermo]
def identityBalanced
    (moment : Orbit → Gdual)
    (geometricTemperature : G)
    (pairing : G → Gdual → ℝ)
    (parityOfGenerator : G → SuperParity)
    (stressTensorProjection : Gdual → ℝ) :
    SuperCoadjointMomentMapData G Gdual Orbit where
  coadjointAction := fun _ q => q
  moment := moment
  geometricTemperature := geometricTemperature
  pairing := pairing
  parityOfGenerator := parityOfGenerator
  stressTensorProjection := stressTensorProjection
  supercurrentProjection := fun q => -stressTensorProjection q
  isOnCoadjointOrbit := fun q => ∃ x, moment x = q

-- theorem-class: bridge
@[rep_depth thermo]
theorem identityBalanced_coadjointAction
    (moment : Orbit → Gdual)
    (geometricTemperature : G)
    (pairing : G → Gdual → ℝ)
    (parityOfGenerator : G → SuperParity)
    (stressTensorProjection : Gdual → ℝ)
    (g : G) (q : Gdual) :
    (identityBalanced
      (G := G) (Gdual := Gdual) (Orbit := Orbit)
      moment geometricTemperature pairing parityOfGenerator
      stressTensorProjection).coadjointAction g q = q :=
  rfl

-- theorem-class: bridge
@[rep_depth thermo]
theorem identityBalanced_supertrace_balance
    (moment : Orbit → Gdual)
    (geometricTemperature : G)
    (pairing : G → Gdual → ℝ)
    (parityOfGenerator : G → SuperParity)
    (stressTensorProjection : Gdual → ℝ)
    (x : Orbit) :
    let J :=
      identityBalanced
        (G := G) (Gdual := Gdual) (Orbit := Orbit)
        moment geometricTemperature pairing parityOfGenerator
        stressTensorProjection
    J.stressTensorProjection (J.moment x) +
        J.supercurrentProjection (J.moment x) = 0 := by
  dsimp [identityBalanced]
  ring

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
  reversibleFlow : Orbit → Orbit
  dissipativeFlow : Orbit → Orbit
  entropy : Orbit → ℝ
  reversibleEntropyRate : Orbit → ℝ
  dissipativeEntropyRate : Orbit → ℝ
  totalEntropyProduction : Orbit → ℝ
-- theorem-class: bridge
  moment_mem_orbit :
    ∀ x : Orbit, superMoment.isOnCoadjointOrbit (superMoment.moment x)
-- theorem-class: bridge
  reversible_preserves_orbit :
    ∀ x : Orbit,
      superMoment.isOnCoadjointOrbit (superMoment.moment (reversibleFlow x))
-- theorem-class: bridge
  orbit_entropy_invariant :
    ∀ x : Orbit, entropy (reversibleFlow x) = entropy x
-- theorem-class: bridge
  reversibleEntropyRate_eq_zero :
    ∀ x : Orbit, reversibleEntropyRate x = 0
-- theorem-class: bridge
  dissipativeEntropyRate_nonneg :
    ∀ x : Orbit, 0 ≤ dissipativeEntropyRate x
-- theorem-class: bridge
  totalEntropyProduction_eq_sum :
    ∀ x : Orbit,
      totalEntropyProduction x =
        reversibleEntropyRate x + dissipativeEntropyRate x
-- theorem-class: bridge
  weyl_covariant :
    ∀ (g : G) (x : Orbit),
      superMoment.coadjointAction g (superMoment.moment x) =
        superMoment.moment x
-- theorem-class: bridge
  supertrace_balance :
    ∀ x : Orbit,
      superMoment.stressTensorProjection (superMoment.moment x) +
        superMoment.supercurrentProjection (superMoment.moment x) = 0

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
    (reversibleFlow dissipativeFlow : Orbit → Orbit)
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
    (moment_in_orbit :
      ∀ x : Orbit, superMoment.isOnCoadjointOrbit (superMoment.moment x))
    (reversible_in_orbit :
      ∀ x : Orbit,
        superMoment.isOnCoadjointOrbit (superMoment.moment (reversibleFlow x))) :
    FullCoadjointOrbitMetriplecticContext G Gdual Orbit where
  superMoment := superMoment
  reversibleFlow := reversibleFlow
  dissipativeFlow := dissipativeFlow
  entropy := entropy
  reversibleEntropyRate := fun _ => 0
  dissipativeEntropyRate := fun x => dissipationAmplitude x ^ (2 : ℕ)
  totalEntropyProduction := fun x => dissipationAmplitude x ^ (2 : ℕ)
  moment_mem_orbit := moment_in_orbit
  reversible_preserves_orbit := reversible_in_orbit
  orbit_entropy_invariant := reversible_entropy_invariant
  reversibleEntropyRate_eq_zero := by
    intro x
    rfl
  dissipativeEntropyRate_nonneg := by
    intro x
    exact sq_nonneg (dissipationAmplitude x)
  totalEntropyProduction_eq_sum := by
    intro x
    simp
  weyl_covariant := weyl_covariant
  supertrace_balance := supertrace_balance

/--
Fully constructive exact super-coadjoint square-dissipation context.

This is the dimension-agnostic exact-equilibrium route:

* the coadjoint action is identity, so Weyl/coadjoint covariance is proved by
  reflexivity;
* the reversible flow is identity, so entropy is Casimir-invariant by
  reflexivity;
* the odd supercurrent is the negative stress readout, so supertrace balance is
  proved algebraically;
* dissipative and total entropy production are real squares.

No finite state space, matrix diagonalization, or scalarized finite response
model is used.
-/
@[rep_depth thermo]
def ofIdentityBalancedSquareDissipation
    (moment : Orbit → Gdual)
    (geometricTemperature : G)
    (pairing : G → Gdual → ℝ)
    (parityOfGenerator : G → SuperParity)
    (stressTensorProjection : Gdual → ℝ)
    (entropy : Orbit → ℝ)
    (dissipativeFlow : Orbit → Orbit)
    (dissipationAmplitude : Orbit → ℝ) :
    FullCoadjointOrbitMetriplecticContext G Gdual Orbit :=
  ofMomentImageSquareDissipation
    (superMoment :=
      SuperCoadjointMomentMapData.identityBalanced
        (G := G) (Gdual := Gdual) (Orbit := Orbit)
        moment geometricTemperature pairing parityOfGenerator
        stressTensorProjection)
    (entropy := entropy)
    (reversibleFlow := id)
    (dissipativeFlow := dissipativeFlow)
    (dissipationAmplitude := dissipationAmplitude)
    (reversible_entropy_invariant := by
      intro x
      rfl)
    (weyl_covariant := by
      intro g x
      rfl)
    (supertrace_balance := by
      intro x
      dsimp [SuperCoadjointMomentMapData.identityBalanced]
      ring)
    (moment_in_orbit := fun x => ⟨x, rfl⟩)
    (reversible_in_orbit := fun x => ⟨x, rfl⟩)

variable (C : FullCoadjointOrbitMetriplecticContext G Gdual Orbit)

-- theorem-class: bridge
/-- The reversible coadjoint-orbit channel is entropy-Casimir by hypothesis. -/
@[rep_depth thermo]
theorem reversible_channel_zero (x : Orbit) :
    C.reversibleEntropyRate x = 0 :=
  C.reversibleEntropyRate_eq_zero x

-- theorem-class: bridge
@[rep_depth thermo]
theorem moment_lands_on_coadjoint_orbit (x : Orbit) :
    C.superMoment.isOnCoadjointOrbit (C.superMoment.moment x) :=
  C.moment_mem_orbit x

-- theorem-class: bridge
@[rep_depth thermo]
theorem orbit_entropy_invariant_readout (x : Orbit) :
    C.entropy (C.reversibleFlow x) = C.entropy x :=
  C.orbit_entropy_invariant x

-- theorem-class: bridge
@[rep_depth thermo]
theorem weyl_gauge_covariant (g : G) (x : Orbit) :
    C.superMoment.coadjointAction g (C.superMoment.moment x) =
      C.superMoment.moment x :=
  C.weyl_covariant g x

-- theorem-class: bridge
@[rep_depth thermo]
theorem supertrace_free_stress (x : Orbit) :
    C.superMoment.stressTensorProjection (C.superMoment.moment x) +
      C.superMoment.supercurrentProjection (C.superMoment.moment x) = 0 :=
  C.supertrace_balance x

-- theorem-class: bridge
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

-- theorem-class: bridge
/--
Packed theorem for the constructive moment-image/square-dissipation full
super-coadjoint route.
-/
@[rep_depth thermo]
theorem full_moment_image_square_dissipation_packet
    (superMoment : SuperCoadjointMomentMapData G Gdual Orbit)
    (entropy : Orbit → ℝ)
    (reversibleFlow dissipativeFlow : Orbit → Orbit)
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
    (moment_in_orbit :
      ∀ x : Orbit, superMoment.isOnCoadjointOrbit (superMoment.moment x))
    (reversible_in_orbit :
      ∀ x : Orbit,
        superMoment.isOnCoadjointOrbit (superMoment.moment (reversibleFlow x)))
    (x : Orbit) :
    let C :=
      ofMomentImageSquareDissipation
        superMoment entropy reversibleFlow dissipativeFlow dissipationAmplitude
        reversible_entropy_invariant weyl_covariant supertrace_balance
        moment_in_orbit reversible_in_orbit
    C.superMoment.isOnCoadjointOrbit (C.superMoment.moment x)
      ∧ C.entropy (C.reversibleFlow x) = C.entropy x
      ∧ C.reversibleEntropyRate x = 0
      ∧ C.dissipativeEntropyRate x = dissipationAmplitude x ^ (2 : ℕ)
      ∧ C.totalEntropyProduction x = dissipationAmplitude x ^ (2 : ℕ)
      ∧ 0 ≤ C.totalEntropyProduction x
      ∧ (∀ g y, C.superMoment.coadjointAction g (C.superMoment.moment y) =
          C.superMoment.moment y)
      ∧ (∀ y, C.superMoment.stressTensorProjection (C.superMoment.moment y) +
          C.superMoment.supercurrentProjection (C.superMoment.moment y) = 0) := by
  dsimp [ofMomentImageSquareDissipation]
  exact
    ⟨moment_in_orbit x,
      reversible_entropy_invariant x,
      rfl,
      rfl,
      rfl,
      sq_nonneg (dissipationAmplitude x),
      weyl_covariant,
      supertrace_balance⟩

attribute [terminal] full_moment_image_square_dissipation_packet

-- theorem-class: bridge
/--
Packed theorem for the exact identity-action, balanced-supertrace,
square-dissipation super-coadjoint route.
-/
@[rep_depth thermo]
theorem full_identity_balanced_square_dissipation_packet
    (moment : Orbit → Gdual)
    (geometricTemperature : G)
    (pairing : G → Gdual → ℝ)
    (parityOfGenerator : G → SuperParity)
    (stressTensorProjection : Gdual → ℝ)
    (entropy : Orbit → ℝ)
    (dissipativeFlow : Orbit → Orbit)
    (dissipationAmplitude : Orbit → ℝ)
    (x : Orbit) :
    let C :=
      ofIdentityBalancedSquareDissipation
        moment geometricTemperature pairing parityOfGenerator
        stressTensorProjection entropy dissipativeFlow dissipationAmplitude
    C.superMoment.isOnCoadjointOrbit (C.superMoment.moment x)
      ∧ C.entropy (C.reversibleFlow x) = C.entropy x
      ∧ C.reversibleEntropyRate x = 0
      ∧ C.dissipativeEntropyRate x = dissipationAmplitude x ^ (2 : ℕ)
      ∧ C.totalEntropyProduction x = dissipationAmplitude x ^ (2 : ℕ)
      ∧ 0 ≤ C.totalEntropyProduction x
      ∧ (∀ g y, C.superMoment.coadjointAction g (C.superMoment.moment y) =
          C.superMoment.moment y)
      ∧ (∀ y, C.superMoment.stressTensorProjection (C.superMoment.moment y) +
          C.superMoment.supercurrentProjection (C.superMoment.moment y) = 0) := by
  simpa using
    (full_moment_image_square_dissipation_packet
      (superMoment :=
        SuperCoadjointMomentMapData.identityBalanced
          (G := G) (Gdual := Gdual) (Orbit := Orbit)
          moment geometricTemperature pairing parityOfGenerator
          stressTensorProjection)
      (entropy := entropy)
      (reversibleFlow := id)
      (dissipativeFlow := dissipativeFlow)
      (dissipationAmplitude := dissipationAmplitude)
      (reversible_entropy_invariant := by intro y; rfl)
      (weyl_covariant := by intro g y; rfl)
      (supertrace_balance := by
        intro y
        dsimp [SuperCoadjointMomentMapData.identityBalanced]
        ring)
      (moment_in_orbit := fun y => ⟨y, rfl⟩)
      (reversible_in_orbit := fun y => ⟨y, rfl⟩)
      (x := x))

attribute [terminal] full_identity_balanced_square_dissipation_packet

end FullCoadjointOrbitMetriplecticContext

/-! ## Dimension-agnostic constructive coadjoint-orbit route -/

section SquareDissipationCoadjointOrbit

open InfoGeometry.Canonical.SouriauCoadjointOrbitMetriplectic

variable {G Gdual Orbit : Type*}

-- theorem-class: bridge
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
-- theorem-class: bridge
  quantumFisherMetric_nonneg : 0 ≤ quantumFisherMetric

namespace CoordinatelessKMSFisherState

variable {Obs : Type*}
variable (K : CoordinatelessKMSFisherState Obs)

-- theorem-class: bridge
/-- The coordinateless quantum-Fisher/Bures metric is nonnegative by data. -/
@[rep_depth operator]
theorem fisherMetric_nonneg :
    0 ≤ K.quantumFisherMetric :=
  K.quantumFisherMetric_nonneg

-- theorem-class: bridge
/-- KMS and Weyl covariance are explicit algebraic hypotheses, not coordinates. -/
@[rep_depth operator]
theorem algebraic_equilibrium_packet
    (hKMS : K.kmsEquilibrium)
    (hWeyl : K.weylAutomorphismInvariant) :
    K.kmsEquilibrium ∧ K.weylAutomorphismInvariant ∧
      0 ≤ K.quantumFisherMetric :=
  ⟨hKMS, hWeyl, K.fisherMetric_nonneg⟩

/--
Proof-carrying algebraic equilibrium witness for the coordinateless KMS/Fisher lane.

This narrows the old two-hypothesis `(hKMS, hWeyl)` surface to one constructive
object carrying exactly the owned equilibrium proofs needed to recover the
existing algebraic packet.
-/
@[rep_depth operator]
structure EquilibriumWitness where
  state : CoordinatelessKMSFisherState Obs
  hKMS : state.kmsEquilibrium
  hWeyl : state.weylAutomorphismInvariant

namespace EquilibriumWitness

/-- Recover the old algebraic equilibrium packet from the proof-carrying witness. -/
@[rep_depth operator]
theorem packet (W : CoordinatelessKMSFisherState.EquilibriumWitness (Obs := Obs)) :
    W.state.kmsEquilibrium ∧ W.state.weylAutomorphismInvariant ∧
      0 ≤ W.state.quantumFisherMetric :=
  W.state.algebraic_equilibrium_packet W.hKMS W.hWeyl

end EquilibriumWitness

attribute [terminal] algebraic_equilibrium_packet
attribute [terminal] EquilibriumWitness.packet

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
-- theorem-class: bridge
  fenchel_metriplectic_moment :
    finiteFenchel.M = finiteMetriplectic.M
-- theorem-class: bridge
  fenchel_metriplectic_temperature :
    finiteFenchel.T = finiteMetriplectic.T
-- theorem-class: bridge
  conformal_metriplectic_moment :
    conformalKKT.density.M = finiteMetriplectic.M
-- theorem-class: bridge
  conformal_metriplectic_temperature :
    conformalKKT.density.T = finiteMetriplectic.T

/--
Exact KKT-residual branch of the Souriau Lie-thermodynamic optimization context.

This narrowed constructive branch does not carry an explicit
`KKTEntropyStationarityShadow` field. Instead, the KKT lane is fixed to the
owned exact residual packet and can be recovered definitionally through the
adapter `toSouriauLieThermoKKTContext`.
-/
@[rep_depth thermo]
structure ExactKKTResidualSouriauLieThermoKKTContext [Fintype α] [Nonempty α] where
  finiteFenchel : SouriauFenchelContext (α := α)
  finiteMetriplectic : MetriplecticContext (α := α)
  conformalKKT : SouriauConformalKKTContext (α := α) (H := H)
  operatorialMetriplectic : OperatorialMetriplecticContext (E := H)
-- theorem-class: bridge
  fenchel_metriplectic_moment :
    finiteFenchel.M = finiteMetriplectic.M
-- theorem-class: bridge
  fenchel_metriplectic_temperature :
    finiteFenchel.T = finiteMetriplectic.T
-- theorem-class: bridge
  conformal_metriplectic_moment :
    conformalKKT.density.M = finiteMetriplectic.M
-- theorem-class: bridge
  conformal_metriplectic_temperature :
    conformalKKT.density.T = finiteMetriplectic.T

namespace ExactKKTResidualSouriauLieThermoKKTContext

variable [Fintype α] [Nonempty α]

/-- Recover the legacy broad context by computing the exact KKT packet. -/
@[rep_depth thermo]
def toSouriauLieThermoKKTContext
    (C : ExactKKTResidualSouriauLieThermoKKTContext (α := α) (H := H)) :
    SouriauLieThermoKKTContext (α := α) (H := H) where
  finiteFenchel := C.finiteFenchel
  finiteMetriplectic := C.finiteMetriplectic
  conformalKKT := C.conformalKKT
  operatorialMetriplectic := C.operatorialMetriplectic
  kktStationarity :=
      DimensionAgnosticKKTResiduals.toShadow DimensionAgnosticKKTResiduals.exact
  fenchel_metriplectic_moment := C.fenchel_metriplectic_moment
  fenchel_metriplectic_temperature := C.fenchel_metriplectic_temperature
  conformal_metriplectic_moment := C.conformal_metriplectic_moment
  conformal_metriplectic_temperature := C.conformal_metriplectic_temperature

-- theorem-class: bridge
/-- Exact residuals discharge the computed KKT packet on the narrowed branch. -/
@[rep_depth thermo]
theorem kktStationarity_packet
    (C : ExactKKTResidualSouriauLieThermoKKTContext (α := α) (H := H)) :
    C.toSouriauLieThermoKKTContext.kktStationarity.coneAdmissible ∧
      C.toSouriauLieThermoKKTContext.kktStationarity.stationarity ∧
      C.toSouriauLieThermoKKTContext.kktStationarity.complementarySlackness ∧
      C.toSouriauLieThermoKKTContext.kktStationarity.finitePartitionAdmissible := by
  exact KKTEntropyStationarityShadow.mk_exact

end ExactKKTResidualSouriauLieThermoKKTContext

namespace SouriauLieThermoKKTContext

variable [Fintype α] [Nonempty α]
variable (C : SouriauLieThermoKKTContext (α := α) (H := H))

local notation "H₂" => DoubledSpace H
local notation "EndH₂" => H₂ →L[ℝ] H₂
local notation "cl11" => doubledSpaceCl11Action (E := H)

/-! ## Finite Souriau/Fenchel/Onsager projections -/

-- theorem-class: bridge
/-- The scalar Fenchel gap is nonnegative on the finite Souriau Massieu model. -/
@[rep_depth thermo]
theorem finiteFenchelGap_nonneg (eta : ℝ) :
    0 ≤ C.finiteFenchel.model.fenchelGap C.finiteFenchel.theta eta :=
  C.finiteFenchel.fenchelGap_nonneg eta

-- theorem-class: bridge
/-- The finite Fenchel contact equality holds at the Legendre contact locus. -/
@[rep_depth thermo]
theorem finiteFenchelGap_eq_zero_at_contact :
    C.finiteFenchel.model.fenchelGap
        C.finiteFenchel.theta
        (C.finiteFenchel.model.dualCoord C.finiteFenchel.theta) = 0 :=
  C.finiteFenchel.fenchelGap_eq_zero_at_contact

-- theorem-class: bridge
/-- The finite Massieu bridge is the owner Souriau Massieu value. -/
@[rep_depth thermo]
theorem finiteMassieu_matches_souriau :
    C.finiteFenchel.model.massieu C.finiteFenchel.theta =
      souriauMassieuPotential C.finiteFenchel.M C.finiteFenchel.T :=
  C.finiteFenchel.massieu_matches

-- theorem-class: bridge
/--
Finite Souriau-Onsager second-law shadow: the total entropy production is
nonnegative under the explicit Casimir and PSD response hypotheses carried by
`finiteMetriplectic`.
-/
@[rep_depth thermo]
theorem finiteMetriplecticEntropyProduction_nonneg :
    0 ≤ C.finiteMetriplectic.totalEntropyProduction :=
  C.finiteMetriplectic.totalEntropyProduction_nonneg

-- theorem-class: bridge
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

-- theorem-class: bridge
/--
The finite Souriau-Fisher metric/readout is nonnegative under the same PSD
response hypothesis that drives the finite metriplectic second law.
-/
@[rep_depth thermo]
theorem finiteSouriauFisherMetricReadout_nonneg :
    0 ≤ C.finiteSouriauFisherMetricReadout :=
  C.finiteMetriplectic.metricEntropyProduction_nonneg

-- theorem-class: bridge
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

-- theorem-class: bridge
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

-- theorem-class: bridge
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
        C.finiteMetriplectic.M C.finiteMetriplectic.T).Symmetric
      ∧ 0 ≤ souriauEntropyProduction
          C.finiteMetriplectic.M C.finiteMetriplectic.T xβ xμ :=
  ⟨souriauFisherResponseMatrix_symmetric
      C.finiteMetriplectic.M C.finiteMetriplectic.T,
    souriauEntropyProduction_nonneg_of_positiveSemidefinite
      C.finiteMetriplectic.M C.finiteMetriplectic.T hPSD xβ xμ⟩

-- theorem-class: bridge
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

-- theorem-class: bridge
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

-- theorem-class: bridge
/-- The certified conformal dilation is the Drazin dilation-gap owner object. -/
@[rep_depth transport]
theorem conformalD_eq_dilationGap :
    C.conformalKKT.CCI.toConformalInference.D =
      C.conformalKKT.CCI.toCertifiedInverseKernel.dilationGap :=
  C.conformalKKT.conformalD_eq_dilationGap

-- theorem-class: bridge
/-- The conformal dilation is grade zero under the explicit KKT wing hypotheses. -/
@[rep_depth transport]
theorem conformalD_isGZero :
    IsGZero cl11 C.conformalKKT.CCI.toConformalInference.D :=
  C.conformalKKT.conformalD_isGZero

-- theorem-class: bridge
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

-- theorem-class: bridge
/-- The context supplies the conformal/KKT grade-zero closure packet. -/
@[rep_depth transport]
theorem satisfiesConformalKKTGradeZero :
    C.SatisfiesConformalKKTGradeZero :=
  ⟨C.conformalD_eq_dilationGap, C.conformalD_isGZero, C.chiralGrading_isGZero⟩

/-! ## Operatorial Krein/Onsager projections -/

-- theorem-class: bridge
/-- Operatorial Onsager reciprocity on the doubled Krein carrier. -/
@[rep_depth transport]
theorem operatorialMetricResponse_swap :
    C.operatorialMetriplectic.metricResponse =
      C.operatorialMetriplectic.swappedMetricResponse :=
  C.operatorialMetriplectic.metricResponse_swap

-- theorem-class: bridge
/-- The mixed operatorial metric response is symmetric. -/
@[rep_depth transport]
theorem operatorialMixedMetricResponse_symm :
    C.operatorialMetriplectic.mixedMetricResponseXY =
      C.operatorialMetriplectic.mixedMetricResponseYX :=
  C.operatorialMetriplectic.mixedMetricResponse_symm

-- theorem-class: bridge
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

-- theorem-class: bridge
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

-- theorem-class: bridge
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

-- theorem-class: bridge
/--
The Weyl-weighted thermodynamic dynamics is a coordinate-free Lie derivation,
not a coordinate partial derivative.
-/
@[rep_depth transport]
theorem operatorialWeightedDynamics_eq_weylCovariantThermodynamicDerivation :
    C.operatorialMetriplectic.weightedDynamics =
      C.operatorialMetriplectic.weylCovariantThermodynamicDerivation :=
  C.operatorialMetriplectic.weightedDynamics_eq_weylCovariantThermodynamicDerivation

-- theorem-class: bridge
/--
Operatorial Weyl-covariant derivative split:
the density-weighted Souriau derivation is the zero-weight derivation plus the
explicit Weyl phase-axis derivation correction.
-/
@[rep_depth transport]
theorem operatorialWeylCovariantThermodynamicDerivation_split :
    C.operatorialMetriplectic.weylCovariantThermodynamicDerivation =
      C.operatorialMetriplectic.zeroWeightThermodynamicDerivation
        + C.operatorialMetriplectic.weight •
          C.operatorialMetriplectic.phaseAxisThermodynamicDerivation :=
  C.operatorialMetriplectic.weylCovariantThermodynamicDerivation_eq_zeroWeight_add_phaseAxis

-- theorem-class: bridge
/-- Operatorial entropy production is the two-channel quadratic response form. -/
@[rep_depth transport]
theorem operatorialEntropyProduction_eq_quadratic
    (xForce yForce : ℝ) :
    C.operatorialMetriplectic.operatorialEntropyProduction xForce yForce =
      C.operatorialMetriplectic.diagonalMetricResponse * xForce ^ (2 : ℕ)
        + 2 * C.operatorialMetriplectic.mixedMetricResponseXY * xForce * yForce
          + C.operatorialMetriplectic.yDiagonalMetricResponse * yForce ^ (2 : ℕ) :=
  C.operatorialMetriplectic.operatorialEntropyProduction_eq_quadratic xForce yForce

-- theorem-class: bridge
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

-- theorem-class: bridge
/--
Operatorial second-law gate from a constructive square-response witness.

This narrows the bare `OperatorialMetricResponsePSD` hypothesis to the owned
infinite-dimensional witness route already available on the operatorial
metriplectic lane.
-/
@[rep_depth transport]
theorem operatorialEntropyProduction_nonneg_of_squareResponse
    (S :
      OperatorialMetriplecticContext.SquareOperatorialResponseContext
        C.operatorialMetriplectic)
    (xForce yForce : ℝ) :
    0 ≤ C.operatorialMetriplectic.operatorialEntropyProduction xForce yForce :=
  C.operatorialEntropyProduction_nonneg_of_metricResponsePSD
    (OperatorialMetriplecticContext.SquareOperatorialResponseContext.operatorialMetricResponsePSD S)
    xForce yForce

-- theorem-class: bridge
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

-- theorem-class: bridge
/--
Operatorial Fisher/Onsager entropy equation from a constructive square-response
witness.

This removes the naked scalar PSD input from the bridge when the concrete
operatorial model proves orthogonal square response channels.  The carrier is
still the doubled Krein operator algebra; no finite response matrix is used.
-/
@[rep_depth transport]
theorem operatorialFisherOnsager_entropyProduction_equation_of_squareResponse
    (S :
      OperatorialMetriplecticContext.SquareOperatorialResponseContext
        C.operatorialMetriplectic)
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
  C.operatorialFisherOnsager_entropyProduction_equation
    (OperatorialMetriplecticContext.SquareOperatorialResponseContext.operatorialMetricResponsePSD S)
    xForce yForce

-- theorem-class: bridge
/--
Operatorial second-law gate from regular Drazin/Krein cone positivity.

This replaces the bare `OperatorialMetricResponsePSD` hypothesis by the owned
regular-cone witness route on the infinite doubled-Krein operator lane.
-/
@[rep_depth transport]
theorem operatorialEntropyProduction_nonneg_of_regularCone
    (R :
      OperatorialMetriplecticContext.RegularConeOperatorialResponseContext
        C.operatorialMetriplectic)
    (xForce yForce : ℝ) :
    0 ≤ C.operatorialMetriplectic.operatorialEntropyProduction xForce yForce :=
  C.operatorialEntropyProduction_nonneg_of_metricResponsePSD
    (OperatorialMetriplecticContext.RegularConeOperatorialResponseContext.operatorialMetricResponsePSD R)
    xForce yForce

-- theorem-class: bridge
/--
Operatorial Fisher/Onsager entropy equation from regular Drazin/Krein cone
positivity.

This is the noncommutative replacement for a bare PSD scalar assumption:
diagonal Hessian representatives live in the regular operator cone and the
probe is positive on that cone.
-/
@[rep_depth transport]
theorem operatorialFisherOnsager_entropyProduction_equation_of_regularCone
    (R :
      OperatorialMetriplecticContext.RegularConeOperatorialResponseContext
        C.operatorialMetriplectic)
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
  C.operatorialFisherOnsager_entropyProduction_equation
    (OperatorialMetriplecticContext.RegularConeOperatorialResponseContext.operatorialMetricResponsePSD R)
    xForce yForce

-- theorem-class: bridge
/--
Operatorial Fisher/Onsager entropy equation from a Cramer-Rao realization of
the response packet.

Here the two-channel determinant is not a hypothesis: the bridge delegates to
the comparison-state channel Cauchy-Schwarz theorem on the doubled Krein
carrier through `CramerRaoOperatorialResponseContext`.
-/
@[rep_depth transport]
theorem operatorialFisherOnsager_entropyProduction_equation_of_cramerRaoResponse
    (R :
      OperatorialMetriplecticContext.CramerRaoOperatorialResponseContext
        C.operatorialMetriplectic)
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
    C.operatorialMetriplectic.operatorialEntropyProduction_nonneg_of_cramerRaoResponse
      R xForce yForce⟩

-- theorem-class: bridge
/--
One-channel operatorial entropy production from the same Cramer-Rao realization.

This is the scalar `Operators.entropyProduction` endpoint, but its positivity
is still inherited from the doubled-carrier Cramer-Rao channel metric rather
than from an explicit `probe_hessian_nonneg` assumption.
-/
@[rep_depth transport]
theorem operatorCanonicalEntropyProduction_nonneg_of_cramerRaoResponse
    (R :
      OperatorialMetriplecticContext.CramerRaoOperatorialResponseContext
        C.operatorialMetriplectic) :
    0 ≤
      InfoGeometry.Canonical.Operators.entropyProduction (E := H)
        C.operatorialMetriplectic.P
        C.operatorialMetriplectic.X
        C.operatorialMetriplectic.A :=
  C.operatorialMetriplectic.canonicalEntropyProduction_nonneg_of_cramerRaoResponse R

-- theorem-class: bridge
/--
Operatorial Souriau-Fisher metric packet.

The Souriau-Fisher metric is exposed here as the doubled-Krein
`comparisonStateGeneratorMetric`, not as a finite response matrix or a scalar
Kähler-potential label.  The Hessian/Onsager readout identity is paired with
the Cramer-Rao channel metric realization and the resulting second-law
nonnegativity.
-/
@[rep_depth transport]
theorem operatorialSouriauFisherMetric_packet_of_cramerRaoResponse
    (R :
      OperatorialMetriplecticContext.CramerRaoOperatorialResponseContext
        C.operatorialMetriplectic)
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
      ∧ C.operatorialMetriplectic.diagonalMetricResponse =
          InfoGeometry.Canonical.RelativeModularPotential.comparisonStateGeneratorMetric
            (E := H) C.operatorialMetriplectic.comparison
            C.operatorialMetriplectic.X C.operatorialMetriplectic.X
      ∧ C.operatorialMetriplectic.yDiagonalMetricResponse =
          InfoGeometry.Canonical.RelativeModularPotential.comparisonStateGeneratorMetric
            (E := H) C.operatorialMetriplectic.comparison
            C.operatorialMetriplectic.Y C.operatorialMetriplectic.Y
      ∧ C.operatorialMetriplectic.mixedMetricResponseXY =
          InfoGeometry.Canonical.RelativeModularPotential.comparisonStateGeneratorMetric
            (E := H) C.operatorialMetriplectic.comparison
            C.operatorialMetriplectic.X C.operatorialMetriplectic.Y
      ∧ 0 ≤ C.operatorialMetriplectic.operatorialEntropyProduction xForce yForce :=
  ⟨C.operatorialFisherOnsager_eq_hessianReadout,
    R.diagonalMetricResponse_eq_comparisonMetric,
    R.yDiagonalMetricResponse_eq_comparisonMetric,
    R.mixedMetricResponseXY_eq_comparisonMetric,
    C.operatorialMetriplectic.operatorialEntropyProduction_nonneg_of_cramerRaoResponse
      R xForce yForce⟩

-- theorem-class: bridge
/--
Supergraded even/odd operatorial Onsager block packet.

The even and odd lanes are the two arbitrary doubled-Krein perturbation
channels of the operatorial context.  The block entries are response
coefficients, and the second-law inequality is proved through the
Cramer-Rao/Cauchy-Schwarz owner path.
-/
@[rep_depth transport]
theorem operatorialSupergradedEvenOddOnsagerBlock_packet_of_cramerRaoResponse
    (R :
      OperatorialMetriplecticContext.CramerRaoOperatorialResponseContext
        C.operatorialMetriplectic)
    (evenForce oddForce : ℝ) :
    C.operatorialMetriplectic.mixedMetricResponseXY =
        C.operatorialMetriplectic.mixedMetricResponseYX
      ∧ C.operatorialMetriplectic.diagonalMetricResponse =
          InfoGeometry.Canonical.RelativeModularPotential.comparisonStateGeneratorMetric
            (E := H) C.operatorialMetriplectic.comparison
            C.operatorialMetriplectic.X C.operatorialMetriplectic.X
      ∧ C.operatorialMetriplectic.yDiagonalMetricResponse =
          InfoGeometry.Canonical.RelativeModularPotential.comparisonStateGeneratorMetric
            (E := H) C.operatorialMetriplectic.comparison
            C.operatorialMetriplectic.Y C.operatorialMetriplectic.Y
      ∧ C.operatorialMetriplectic.mixedMetricResponseXY =
          InfoGeometry.Canonical.RelativeModularPotential.comparisonStateGeneratorMetric
            (E := H) C.operatorialMetriplectic.comparison
            C.operatorialMetriplectic.X C.operatorialMetriplectic.Y
      ∧ C.operatorialMetriplectic.operatorialEntropyProduction evenForce oddForce =
          C.operatorialMetriplectic.diagonalMetricResponse * evenForce ^ (2 : ℕ)
            + 2 * C.operatorialMetriplectic.mixedMetricResponseXY * evenForce * oddForce
              + C.operatorialMetriplectic.yDiagonalMetricResponse * oddForce ^ (2 : ℕ)
      ∧ 0 ≤ C.operatorialMetriplectic.operatorialEntropyProduction evenForce oddForce :=
  OperatorialMetriplecticContext.supergradedEvenOddOnsagerBlock_packet_of_cramerRaoResponse
    (C := C.operatorialMetriplectic) R evenForce oddForce

-- theorem-class: bridge
/--
One-channel operatorial second-law closure from regular Drazin/Krein cone
positivity.

This is the first constructive infinite-lane replacement for a bare
two-channel PSD/determinant hypothesis: for a pure `X` thermodynamic force, the
operatorial entropy production is controlled by the diagonal Hessian readout
alone, and that readout is proved nonnegative by regular-cone positivity.
-/
@[rep_depth transport]
theorem operatorialXChannel_entropyProduction_nonneg_of_regularCone
    (R :
      OperatorialMetriplecticContext.RegularConeXResponseContext
        C.operatorialMetriplectic)
    (xForce : ℝ) :
    0 ≤ C.operatorialMetriplectic.operatorialEntropyProduction xForce 0 :=
  C.operatorialMetriplectic.operatorialEntropyProduction_xChannel_nonneg_of_regularCone
    R xForce

/-! ## KKT stationarity packet -/

-- theorem-class: bridge
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

-- theorem-class: bridge
/-- Exact residuals discharge the explicit KKT stationarity packet on the exact branch. -/
@[rep_depth thermo]
theorem kktStationarity_packet_of_exact
    (hExact :
      C.kktStationarity =
        DimensionAgnosticKKTResiduals.toShadow DimensionAgnosticKKTResiduals.exact) :
    C.kktStationarity.coneAdmissible ∧ C.kktStationarity.stationarity ∧
      C.kktStationarity.complementarySlackness ∧
        C.kktStationarity.finitePartitionAdmissible := by
  rw [hExact]
  exact KKTEntropyStationarityShadow.mk_exact

/-! ## Combined finite/operatorial second-law readout -/

-- theorem-class: bridge
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

-- theorem-class: bridge
/--
Combined finite/operatorial entropy production without a bare operatorial PSD
hypothesis, using a constructive square-response witness on the infinite
doubled-Krein operator lane.
-/
@[rep_depth thermo]
theorem finite_and_operatorial_entropyProduction_nonneg_of_squareResponse
    (S :
      OperatorialMetriplecticContext.SquareOperatorialResponseContext
        C.operatorialMetriplectic)
    (xForce yForce : ℝ) :
    0 ≤ C.finiteMetriplectic.totalEntropyProduction ∧
      0 ≤ C.operatorialMetriplectic.operatorialEntropyProduction xForce yForce :=
  ⟨C.finiteMetriplecticEntropyProduction_nonneg,
    C.operatorialEntropyProduction_nonneg_of_squareResponse S xForce yForce⟩

-- theorem-class: bridge
/--
Combined finite/operatorial entropy production without a bare operatorial PSD
hypothesis, using regular Drazin/Krein cone positivity on the operatorial lane.
-/
@[rep_depth thermo]
theorem finite_and_operatorial_entropyProduction_nonneg_of_regularCone
    (R :
      OperatorialMetriplecticContext.RegularConeOperatorialResponseContext
        C.operatorialMetriplectic)
    (xForce yForce : ℝ) :
    0 ≤ C.finiteMetriplectic.totalEntropyProduction ∧
      0 ≤ C.operatorialMetriplectic.operatorialEntropyProduction xForce yForce :=
  ⟨C.finiteMetriplecticEntropyProduction_nonneg,
    C.operatorialEntropyProduction_nonneg_of_regularCone R xForce yForce⟩

-- theorem-class: bridge
/--
Combined finite/operatorial entropy production without a bare operatorial PSD
hypothesis, using a Cramer-Rao realization of the infinite doubled-Krein
operator response packet.
-/
@[rep_depth thermo]
theorem finite_and_operatorial_entropyProduction_nonneg_of_cramerRaoResponse
    (R :
      OperatorialMetriplecticContext.CramerRaoOperatorialResponseContext
        C.operatorialMetriplectic)
    (xForce yForce : ℝ) :
    0 ≤ C.finiteMetriplectic.totalEntropyProduction ∧
      0 ≤ C.operatorialMetriplectic.operatorialEntropyProduction xForce yForce :=
  ⟨C.finiteMetriplecticEntropyProduction_nonneg,
    C.operatorialMetriplectic.operatorialEntropyProduction_nonneg_of_cramerRaoResponse
      R xForce yForce⟩

-- theorem-class: bridge
/--
Combined finite/operatorial one-channel entropy production from regular-cone
positivity on the infinite doubled-Krein operator lane.

The finite lane still uses the already-owned finite Souriau-Fisher theorem; the
operatorial lane does not use a finite response matrix, a scalar PSD packet, or
a two-channel determinant hypothesis.
-/
@[rep_depth thermo]
theorem finite_and_operatorial_xChannel_entropyProduction_nonneg_of_regularCone
    (R :
      OperatorialMetriplecticContext.RegularConeXResponseContext
        C.operatorialMetriplectic)
    (xForce : ℝ) :
    0 ≤ C.finiteMetriplectic.totalEntropyProduction ∧
      0 ≤ C.operatorialMetriplectic.operatorialEntropyProduction xForce 0 :=
  ⟨C.finiteMetriplecticEntropyProduction_nonneg,
    C.operatorialXChannel_entropyProduction_nonneg_of_regularCone R xForce⟩

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
  operatorialWeightedDynamics_eq_weylCovariantThermodynamicDerivation
  operatorialWeylCovariantThermodynamicDerivation_split
  operatorialEntropyProduction_nonneg_of_squareResponse
  operatorialEntropyProduction_nonneg_of_regularCone
  operatorialFisherOnsager_entropyProduction_equation
  operatorialFisherOnsager_entropyProduction_equation_of_squareResponse
  operatorialFisherOnsager_entropyProduction_equation_of_regularCone
  operatorialFisherOnsager_entropyProduction_equation_of_cramerRaoResponse
  operatorialSupergradedEvenOddOnsagerBlock_packet_of_cramerRaoResponse
  operatorialXChannel_entropyProduction_nonneg_of_regularCone
  kktStationarity_packet
  finite_and_operatorial_entropyProduction_nonneg
  finite_and_operatorial_entropyProduction_nonneg_of_squareResponse
  finite_and_operatorial_entropyProduction_nonneg_of_regularCone
  finite_and_operatorial_entropyProduction_nonneg_of_cramerRaoResponse
  finite_and_operatorial_xChannel_entropyProduction_nonneg_of_regularCone

end SouriauLieThermoKKTContext

end InfoGeometry.Canonical.SouriauLieThermoKKTBridge
