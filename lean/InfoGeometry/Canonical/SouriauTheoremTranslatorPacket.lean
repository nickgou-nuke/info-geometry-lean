import InfoGeometry.Canonical.SouriauLieThermoKKTBridge
import InfoGeometry.Canonical.SouriauCoadjointOrbitMetriplecticTheorem
import InfoGeometry.Canonical.SouriauDensityWeightContext
import InfoGeometry.Canonical.SplitCl44TKKJordanLieBridge
import InfoGeometry.Canonical.SuperSouriauFermionGasBridge
import InfoGeometry.Canonical.OperatorFenchelRegularCone
import InfoGeometry.GrandCanonical.ResponseMatrix
import InfoGeometry.Convex.Legendre

/-!
# Souriau Theorem Translator Packet

Translator-facing surface for multilingual Souriau/Fisher/Onsager prose.

The intended pipeline is:

`prose → terminology normalization → claim segmentation → repo-native theorem`.

This file exposes the five theorem families used by that pipeline without
introducing placeholder `True` claims and without upgrading finite owner
theorems into unproved analytic/infinite-dimensional statements.
-/

namespace InfoGeometry.Canonical.SouriauTheoremTranslatorPacket

open InfoGeometry.Canonical.SouriauThermodynamics
open InfoGeometry.Canonical.SouriauFenchelOnsagerBridge
open InfoGeometry.Canonical.SouriauLieThermoKKTBridge
open InfoGeometry.Canonical.SouriauCoadjointOrbitMetriplectic
open InfoGeometry.Canonical.SouriauDensityWeight
open InfoGeometry.Canonical.SplitCl44TKKJordanLieBridge
open InfoGeometry.Canonical.SuperSouriauFermionGasBridge
open InfoGeometry.Canonical.SuperchargeCARCCRBridge
open InfoGeometry.Convex
open InfoGeometry.GrandCanonical
open InfoGeometry.Krein

universe u v w

variable {α : Type _}
variable {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

/-! ## Terminology normalization -/

/-- Normalized theorem-family roles extracted from Souriau thermodynamics prose. -/
inductive SouriauTheoremFamily where
  | potentialPartition
  | firstDerivativeMoments
  | hessianFisherCovariance
  | fenchelLegendreDual
  | onsagerEntropyProduction
  | representationWeightLift
  | conformalTKKJordanLie
  | superFermionGas
  | infiniteSuperCoadjointMetriplectic
deriving DecidableEq, Repr

/-- Canonical Lean-facing name for each extracted theorem family. -/
def canonicalTheoremFamilyName : SouriauTheoremFamily → String
  | .potentialPartition => "potential/partitionFunction"
  | .firstDerivativeMoments => "firstDerivative/moments"
  | .hessianFisherCovariance => "hessian/Fisher/covariance"
  | .fenchelLegendreDual => "FenchelLegendre/contact"
  | .onsagerEntropyProduction => "Onsager/entropyProduction"
  | .representationWeightLift => "representationWeight/densityLift"
  | .conformalTKKJordanLie => "conformalTKK/JordanLie"
  | .superFermionGas => "superSouriau/fermionGas"
  | .infiniteSuperCoadjointMetriplectic => "infiniteSuperCoadjoint/metriplectic"

/-! ## Stage-2 analytic enrichment interfaces -/

/--
Analytic enrichment gate for the inverse Fisher statement.

The finite translator layer owns Fenchel contact identities, but it does not
derive the analytic theorem `Hess(S) = Fisher⁻¹`.  A smooth/coadjoint-orbit
model can instantiate this interface once it supplies the required
differentiability, nondegeneracy, and inverse-Hessian proof.
-/
@[rep_depth thermo]
structure EntropyFisherInverseGate where
  entropyHessian : ℝ
  fisherInverse : ℝ
  entropy_hessian_eq_fisher_inverse : entropyHessian = fisherInverse

namespace EntropyFisherInverseGate

/-- The inverse Fisher/Hessian claim is available only from the explicit gate. -/
@[rep_depth thermo]
theorem claimD_entropy_hessian_eq_fisher_inverse
    (G : EntropyFisherInverseGate) :
    G.entropyHessian = G.fisherInverse :=
  G.entropy_hessian_eq_fisher_inverse

end EntropyFisherInverseGate

/--
Stage-2 scalar analytic enrichment for Claim D.

This is the one-dimensional Legendre theorem behind the prose line
`Hess(S) = Fisher⁻¹`: if the natural-to-dual coordinate map has derivative
`fisher θ`, and the inverse coordinate has derivative `a`, then away from
`fisher θ = 0` the inverse-coordinate derivative is the reciprocal Fisher
scalar.  The differentiability and nondegeneracy gates are explicit.
-/
@[rep_depth thermo]
theorem claimD_scalarLegendre_inverseHessian_eq_inv_fisher
    (L : LegendrePotential) (θ a : ℝ)
    (hEta : HasDerivAt (LegendrePotential.eta L) (L.fisher θ) θ)
    (hTheta :
      HasDerivAt (LegendrePotential.thetaOfEta L) a
        (LegendrePotential.eta L θ))
    (hFisher : L.fisher θ ≠ 0) :
    a = (L.fisher θ)⁻¹ :=
  L.thetaOfEta_deriv_eq_inv_fisher_of_hasDerivAt θ a hEta hTheta hFisher

section OperatorLegendreEnrichment

variable {E : Type}
variable [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

local notation "H₂" => InfoGeometry.Krein.DoubledSpace E
local notation "EndH" => H₂ →L[ℝ] H₂

/--
Stage-2 operatorial enrichment for Claim D on the doubled-Krein lane.

This is the constructive operator analog of the inverse-Hessian narrative:
given a continuous-linear equivalence witness for the Fisher side, the entropy
and Fisher Hessians form a two-sided inverse packet on the operator carrier.
-/
@[rep_depth thermo]
theorem claimD_operatorLegendre_inverseHessian_eq_inverseFisher_packet
    (D : InfoGeometry.Geometry.LegendreContinuousLinearEquivInverseData EndH) :
    D.toLegendreHessianInverseContext.moment =
        InfoGeometry.Geometry.dualCoord D.massieu D.beta
      ∧ D.entropyGradient D.toLegendreHessianInverseContext.moment = D.beta
      ∧ D.toLegendreHessianInverseContext.fisherHessian =
        InfoGeometry.Geometry.hessian D.massieu D.beta
      ∧ D.toLegendreHessianInverseContext.entropyHessian =
        fderiv ℝ D.entropyGradient D.toLegendreHessianInverseContext.moment
      ∧ D.toLegendreHessianInverseContext.entropyHessian.comp
          D.toLegendreHessianInverseContext.fisherHessian =
        ContinuousLinearMap.id ℝ EndH
      ∧ D.toLegendreHessianInverseContext.fisherHessian.comp
          D.toLegendreHessianInverseContext.entropyHessian =
        ContinuousLinearMap.id ℝ (InfoGeometry.Geometry.MomentCoord EndH) :=
  InfoGeometry.Canonical.OperatorFenchelRegularCone.operatorLegendreHessianInverse_packet_of_continuousLinearEquiv
    (E := E) D

end OperatorLegendreEnrichment

/--
Strict Onsager equilibrium gate.

The finite PSD theorem proves `σ ≥ 0`.  The stronger equality case
`σ = 0 ↔ force = 0` requires a stricter positivity/nondegeneracy hypothesis,
so it is represented here as explicit proof-carrying data.
-/
@[rep_depth thermo]
structure StrictOnsagerEquilibriumGate
    [Fintype α] [Nonempty α]
    (M : SouriauMomentMap α) (T : GeometricTemperature) where
  forceIsZero : ℝ → ℝ → Prop
  entropyProduction_eq_zero_iff_force_zero :
    ∀ xβ xμ : ℝ,
      souriauEntropyProduction M T xβ xμ = 0 ↔ forceIsZero xβ xμ

namespace StrictOnsagerEquilibriumGate

/-- Equality-case form of the second law, available only under the strict gate. -/
@[rep_depth thermo]
theorem claimE_entropyProduction_eq_zero_iff_force_zero
    [Fintype α] [Nonempty α]
    {M : SouriauMomentMap α} {T : GeometricTemperature}
    (G : StrictOnsagerEquilibriumGate M T) (xβ xμ : ℝ) :
    souriauEntropyProduction M T xβ xμ = 0 ↔ G.forceIsZero xβ xμ :=
  G.entropyProduction_eq_zero_iff_force_zero xβ xμ

end StrictOnsagerEquilibriumGate

/-! ## Claim A: partition function and Massieu potential -/

/--
Claim A: the finite Gibbs-Souriau Massieu potential is the logarithm of the
finite Gibbs-Souriau partition function.
-/
@[rep_depth thermo]
theorem claimA_massieu_eq_log_partition
    [Fintype α] [Nonempty α]
    (M : SouriauMomentMap α) (T : GeometricTemperature) :
    souriauMassieuPotential M T = Real.log (souriauPartition M T) :=
  souriauMassieuPotential_eq_log_partition M T

/-! ## Claim B: first derivatives and thermodynamic moments -/

/--
Claim B: first Massieu derivatives give the conjugate finite thermodynamic
readouts.

The sign convention is the owner grand-canonical convention:
`∂β Φ = -E[E - μN]` and `∂μ Φ = β E[N]`.
-/
@[rep_depth thermo]
theorem claimB_firstDerivatives_eq_moments
    [Fintype α] [Nonempty α]
    (M : SouriauMomentMap α) (T : GeometricTemperature) :
    deriv (fun β => souriauMassieuPotential M { T with beta := β }) T.beta =
        -souriauMeanShift M T
      ∧ deriv (fun μ => souriauMassieuPotential M { T with mu := μ }) T.mu =
        T.beta * souriauMeanNumber M T :=
  ⟨souriau_beta_conjugate_shifted_readout M T,
    souriau_mu_conjugate_number_readout M T⟩

/-! ## Claim C: Hessian, Fisher response, covariance, symmetry -/

/--
Claim C: the finite Souriau-Fisher response entries are the Massieu Hessian
readouts expressed as variance/covariance terms, and the mixed entries agree.

This is the finite covariance/Hessian surface.  Positivity is intentionally not
bundled here; it is Claim E and requires a PSD gate.
-/
@[rep_depth thermo]
theorem claimC_hessian_eq_fisher_eq_covariance
    [Fintype α] [Nonempty α]
    (M : SouriauMomentMap α) (T : GeometricTemperature) :
    (souriauFisherResponseMatrix M T).betaBeta =
        varianceShift (toGrandCanonicalTwoParam M) T.beta T.mu
      ∧ (souriauFisherResponseMatrix M T).muMu =
        T.beta ^ (2 : ℕ) *
          varianceNumber (toGrandCanonicalTwoParam M) T.beta T.mu
      ∧ (souriauFisherResponseMatrix M T).betaMu =
        meanNumber (toGrandCanonicalTwoParam M) T.beta T.mu -
          T.beta * covarianceShiftNumber (toGrandCanonicalTwoParam M) T.beta T.mu
      ∧ (souriauFisherResponseMatrix M T).muBeta =
        meanNumber (toGrandCanonicalTwoParam M) T.beta T.mu -
          T.beta * covarianceShiftNumber (toGrandCanonicalTwoParam M) T.beta T.mu
      ∧ (souriauFisherResponseMatrix M T).Symmetric :=
  ⟨souriauFisher_betaBeta_eq_varianceShift M T,
    souriauFisher_muMu_eq_beta_sq_varianceNumber M T,
    souriauFisher_betaMu_eq_meanNumber_sub_beta_mul_covariance M T,
    souriauFisher_muBeta_eq_meanNumber_sub_beta_mul_covariance M T,
    souriauFisherResponseMatrix_symmetric M T⟩

/-! ## Claim D: Fenchel-Legendre contact layer -/

/--
Claim D: the finite Souriau Massieu value satisfies the Fenchel-Legendre
contact balance; the generic Fenchel gap is nonnegative and vanishes at the
contact coordinate.

This is the repo-owned scalar contact surface.  It does not assert
`Hess(S) = Fisher⁻¹`; that inverse-Hessian statement is a stronger analytic
surface not owned by this finite theorem.
-/
@[rep_depth thermo]
theorem claimD_fenchelLegendre_contact_packet
    [Fintype α] [Nonempty α]
    (C : SouriauFenchelContext (α := α)) (eta : ℝ) :
    0 ≤ C.model.fenchelGap C.theta eta
      ∧ C.model.fenchelGap
          C.theta (C.model.dualCoord C.theta) = 0
      ∧ souriauMassieuPotential C.M C.T +
          C.model.φ (C.model.dualCoord C.theta) =
        C.theta * C.model.dualCoord C.theta :=
  ⟨C.fenchelGap_nonneg eta,
    C.fenchelGap_eq_zero_at_contact,
    C.souriauMassieu_contact_balance⟩

/-! ## Claim E: Onsager entropy production -/

/--
Claim E: the finite Onsager entropy production is nonnegative under the
explicit positive-semidefinite Souriau-Fisher response gate.
-/
@[rep_depth thermo]
theorem claimE_entropyProduction_nonneg_of_PSD
    [Fintype α] [Nonempty α]
    (M : SouriauMomentMap α) (T : GeometricTemperature)
    (hPSD : (souriauFisherResponseMatrix M T).PositiveSemidefinite)
    (xβ xμ : ℝ) :
    0 ≤ souriauEntropyProduction M T xβ xμ :=
  souriauEntropyProduction_nonneg_of_positiveSemidefinite M T hPSD xβ xμ

/--
Claim E with the proved finite diagonal Fisher positivity exposed.

Only the mixed determinant/non-spinodal gate remains explicit; the diagonal
PSD obligations are constructed from the variance identities.
-/
@[rep_depth thermo]
theorem claimE_entropyProduction_nonneg_of_det_nonneg
    [Fintype α] [Nonempty α]
    (M : SouriauMomentMap α) (T : GeometricTemperature)
    (hdet : 0 ≤ (souriauFisherResponseMatrix M T).det)
    (xβ xμ : ℝ) :
    0 ≤ souriauEntropyProduction M T xβ xμ :=
  souriauEntropyProduction_nonneg_of_det_nonneg M T hdet xβ xμ

/--
Claim E, strict equality case: under an explicit positive-definite response
gate, zero finite entropy production is equivalent to zero thermodynamic force.
-/
@[rep_depth thermo]
theorem claimE_entropyProduction_eq_zero_iff_force_zero_of_PD
    [Fintype α] [Nonempty α]
    (M : SouriauMomentMap α) (T : GeometricTemperature)
    (hPD : (souriauFisherResponseMatrix M T).PositiveDefinite)
    (xβ xμ : ℝ) :
    souriauEntropyProduction M T xβ xμ = 0 ↔ xβ = 0 ∧ xμ = 0 :=
  souriauEntropyProduction_eq_zero_iff_force_zero_of_positiveDefinite
    M T hPD xβ xμ

/-! ## Combined translator packet -/

/--
Combined theorem packet for the five normalized claims A-E.

The packet is finite and conservative:

* A-C and E use the finite Souriau/grand-canonical owner surface;
* D uses the scalar Fenchel contact owner surface;
* E requires an explicit PSD gate.
-/
@[rep_depth thermo]
theorem structuredSouriauTranslatorPacket
    [Fintype α] [Nonempty α]
    (C : SouriauFenchelContext (α := α))
    (hPSD : (souriauFisherResponseMatrix C.M C.T).PositiveSemidefinite)
    (eta xβ xμ : ℝ) :
    souriauMassieuPotential C.M C.T = Real.log (souriauPartition C.M C.T)
      ∧ deriv (fun β => souriauMassieuPotential C.M { C.T with beta := β }) C.T.beta =
        -souriauMeanShift C.M C.T
      ∧ deriv (fun μ => souriauMassieuPotential C.M { C.T with mu := μ }) C.T.mu =
        C.T.beta * souriauMeanNumber C.M C.T
      ∧ (souriauFisherResponseMatrix C.M C.T).betaBeta =
        varianceShift (toGrandCanonicalTwoParam C.M) C.T.beta C.T.mu
      ∧ (souriauFisherResponseMatrix C.M C.T).muMu =
        C.T.beta ^ (2 : ℕ) *
          varianceNumber (toGrandCanonicalTwoParam C.M) C.T.beta C.T.mu
      ∧ (souriauFisherResponseMatrix C.M C.T).Symmetric
      ∧ 0 ≤ C.model.fenchelGap C.theta eta
      ∧ C.model.fenchelGap C.theta (C.model.dualCoord C.theta) = 0
      ∧ souriauMassieuPotential C.M C.T +
          C.model.φ (C.model.dualCoord C.theta) =
        C.theta * C.model.dualCoord C.theta
      ∧ 0 ≤ souriauEntropyProduction C.M C.T xβ xμ := by
  exact ⟨claimA_massieu_eq_log_partition C.M C.T,
    (claimB_firstDerivatives_eq_moments C.M C.T).1,
    (claimB_firstDerivatives_eq_moments C.M C.T).2,
    (claimC_hessian_eq_fisher_eq_covariance C.M C.T).1,
    (claimC_hessian_eq_fisher_eq_covariance C.M C.T).2.1,
    (claimC_hessian_eq_fisher_eq_covariance C.M C.T).2.2.2.2,
    (claimD_fenchelLegendre_contact_packet C eta).1,
    (claimD_fenchelLegendre_contact_packet C eta).2.1,
    (claimD_fenchelLegendre_contact_packet C eta).2.2,
    claimE_entropyProduction_nonneg_of_PSD C.M C.T hPSD xβ xμ⟩

/--
Combined theorem packet with the finite positivity hypothesis narrowed to the
actual remaining determinant gate.
-/
@[rep_depth thermo]
theorem structuredSouriauTranslatorPacket_of_det_nonneg
    [Fintype α] [Nonempty α]
    (C : SouriauFenchelContext (α := α))
    (hdet : 0 ≤ (souriauFisherResponseMatrix C.M C.T).det)
    (eta xβ xμ : ℝ) :
    souriauMassieuPotential C.M C.T = Real.log (souriauPartition C.M C.T)
      ∧ deriv (fun β => souriauMassieuPotential C.M { C.T with beta := β }) C.T.beta =
        -souriauMeanShift C.M C.T
      ∧ deriv (fun μ => souriauMassieuPotential C.M { C.T with mu := μ }) C.T.mu =
        C.T.beta * souriauMeanNumber C.M C.T
      ∧ (souriauFisherResponseMatrix C.M C.T).betaBeta =
        varianceShift (toGrandCanonicalTwoParam C.M) C.T.beta C.T.mu
      ∧ (souriauFisherResponseMatrix C.M C.T).muMu =
        C.T.beta ^ (2 : ℕ) *
          varianceNumber (toGrandCanonicalTwoParam C.M) C.T.beta C.T.mu
      ∧ (souriauFisherResponseMatrix C.M C.T).Symmetric
      ∧ 0 ≤ C.model.fenchelGap C.theta eta
      ∧ C.model.fenchelGap C.theta (C.model.dualCoord C.theta) = 0
      ∧ souriauMassieuPotential C.M C.T +
          C.model.φ (C.model.dualCoord C.theta) =
        C.theta * C.model.dualCoord C.theta
      ∧ 0 ≤ souriauEntropyProduction C.M C.T xβ xμ := by
  exact ⟨claimA_massieu_eq_log_partition C.M C.T,
    (claimB_firstDerivatives_eq_moments C.M C.T).1,
    (claimB_firstDerivatives_eq_moments C.M C.T).2,
    (claimC_hessian_eq_fisher_eq_covariance C.M C.T).1,
    (claimC_hessian_eq_fisher_eq_covariance C.M C.T).2.1,
    (claimC_hessian_eq_fisher_eq_covariance C.M C.T).2.2.2.2,
    (claimD_fenchelLegendre_contact_packet C eta).1,
    (claimD_fenchelLegendre_contact_packet C eta).2.1,
    (claimD_fenchelLegendre_contact_packet C eta).2.2,
    claimE_entropyProduction_nonneg_of_det_nonneg C.M C.T hdet xβ xμ⟩

/-! ## KKT stationarity shadow -/

/--
Claim K: the Karush-Kuhn-Tucker reading is an explicit entropy-optimization
hypothesis packet.

This keeps the literature phrase "KKT conditions" separate from the repo's
chiral `KKTCore` corridor.  A concrete optimization model must supply cone
admissibility, stationarity, complementarity, and finite-partition
admissibility before downstream Souriau thermodynamic conclusions may use the
KKT language.
-/
@[rep_depth thermo]
theorem claimK_kktEntropyStationarity_packet
    (K : KKTEntropyStationarityShadow)
    (hCone : K.coneAdmissible)
    (hStationarity : K.stationarity)
    (hSlack : K.complementarySlackness)
    (hFinite : K.finitePartitionAdmissible) :
    K.coneAdmissible ∧ K.stationarity ∧
      K.complementarySlackness ∧ K.finitePartitionAdmissible :=
  K.packet hCone hStationarity hSlack hFinite

/-! ## Representation weights and conformal/TKK bridge claims -/

/--
Claim W: a finite Souriau representation weight has an operatorial
density-weight lift.

This is the repo-owned conservative form of the prose statement that
representation weights become thermodynamic/operatorial readouts.  Only the
finite number/charge component is lifted, and the target is the existing
doubled-carrier Souriau temperature plus dilation generator.
-/
@[rep_depth thermo]
theorem claimW_representationWeight_lifts_to_densityTransport
    (C : SouriauDensityWeightContext (α := α) (E := H)) :
    C.densityWeight = (souriauWeightAt C.M C.state).numberWeight
      ∧ C.liftedTransportGenerator =
        ThermodynamicGenerator.souriauTemperatureVector (E := H) C.P C.ψ
          + C.densityWeight • dilationOperator (E := H) :=
  ⟨C.densityWeight_eq_numberWeight,
    C.liftedTransportGenerator_eq_souriau_add_number_weighted_dilationOperator⟩

/--
Claim S: stress tensor and supercurrent are projections of one super-coadjoint
moment object.

This is an abstract readout theorem on the explicit
`SuperCoadjointMomentMapData` interface.  It does not construct a concrete
field-theoretic stress tensor; a model must still supply the projections.
-/
@[rep_depth thermo]
theorem claimS_superCoadjoint_stress_supercurrent_readouts
    {G Gdual Orbit : Type*}
    (J : SuperCoadjointMomentMapData G Gdual Orbit) (x : Orbit) :
    J.actionAt x = J.pairing J.geometricTemperature (J.moment x)
      ∧ J.stressTensorAt x = J.stressTensorProjection (J.moment x)
      ∧ J.supercurrentAt x = J.supercurrentProjection (J.moment x) :=
  ⟨J.actionAt_eq_pairing x, rfl, rfl⟩

/--
Claim F: supergraded ideal fermion-gas packet.

This is the conservative Lean surface for the supergeometry prose:

* stress and supercurrent are even/odd readouts of a super-moment map;
* the super Souriau action splits into even thermal and odd source parts;
* the grand-canonical Fock generator is the existing `H - μN` lane plus an
  explicit odd source coupling;
* fermionic/Pauli behavior is supplied by a genuine CAR pair;
* conformal/Weyl claims are carried only by an explicit supertrace-free stress
  context.

The theorem does not construct a concrete supermanifold, supermetric
variation, or `psu(2,2|4)` representation.  Those remain model
instantiations of the owner contexts.
-/
@[rep_depth thermo, capstone]
theorem claimF_superSouriauFermionGas_packet
    {State : Type u} {EvenMoment : Type v} {OddMoment : Type w}
    {Stress : Type u}
    (J :
      SuperSouriauFermionGasBridge.SuperMomentMapData
        State EvenMoment OddMoment)
    (P :
      SuperSouriauFermionGasBridge.SuperSouriauPairing
        State EvenMoment OddMoment)
    (x : State)
    (B : InfoGeometry.Canonical.BogoliubovFockSuper.BogoliubovMixingParams)
    (Hop Qodd : InfoGeometry.Canonical.BogoliubovFockSuper.FockEndomorphism H)
    (mu betaOdd : ℝ)
    (F :
      SuperSouriauFermionGasBridge.FermionicCAROperatorPair (E := H))
    (W :
      SuperSouriauFermionGasBridge.WeylSupertraceFreeStressContext Stress) :
    J.stressTensor x = J.stressTensorReadout (J.evenMoment x)
      ∧ J.supercurrent x = J.supercurrentReadout (J.oddMoment x)
      ∧ P.action x =
        P.beta.betaEven * P.evenEnergy x + P.beta.betaOdd * P.oddSource x
      ∧ SuperSouriauFermionGasBridge.superGrandCanonicalFockGenerator
          (E := H) B Hop mu betaOdd Qodd =
        SuperSouriauFermionGasBridge.evenGrandCanonicalFockGenerator
          (E := H) B Hop mu
          + SuperSouriauFermionGasBridge.oddFockSourceCoupling
            (E := H) betaOdd Qodd
      ∧ InfoGeometry.Canonical.BogoliubovFockSuper.fockSuperBracket
          (E := H)
          InfoGeometry.Canonical.BogoliubovFockSuper.SuperParity.odd
          InfoGeometry.Canonical.BogoliubovFockSuper.SuperParity.odd
          F.annihilation F.creation =
        SuperchargeCARCCRBridge.CARBracket
          (E := H) F.annihilation F.creation
      ∧ InfoGeometry.Canonical.BogoliubovFockSuper.fockAnticommutator
          (E := H) F.annihilation F.annihilation = 0
      ∧ InfoGeometry.Canonical.BogoliubovFockSuper.fockAnticommutator
          (E := H) F.creation F.creation = 0
      ∧ InfoGeometry.Canonical.BogoliubovFockSuper.fockAnticommutator
          (E := H) F.annihilation F.creation =
        ContinuousLinearMap.id ℝ (InfoGeometry.Krein.DoubledSpace H)
      ∧ W.superTrace W.stress = 0
      ∧ W.weylInvariant :=
  ⟨J.stressTensor_eq_even_readout x,
    J.supercurrent_eq_odd_readout x,
    P.action_eq_even_add_odd x,
    SuperSouriauFermionGasBridge.superGrandCanonicalFockGenerator_eq_even_add_odd
      (E := H) B Hop mu betaOdd Qodd,
    SuperSouriauFermionGasBridge.odd_odd_superBracket_eq_CARBracket
      (E := H) F.annihilation F.creation,
    F.annihilation_anticommutator_self_zero,
    F.creation_anticommutator_self_zero,
    F.annihilation_creation_anticommutator_id,
    W.superTrace_stress_eq_zero,
    W.is_weyl_invariant⟩

/--
Claim F, constructive identity-balanced stress variant.

This removes the explicit `WeylSupertraceFreeStressContext` argument from the
translator surface.  The Weyl/supertrace stress packet is constructed from the
identity-action super-coadjoint lane using the even moment and stress readout;
therefore the supertrace-free conclusion is proved by the owned
`ofIdentityBalanced` constructor rather than supplied as an independent field.
-/
@[rep_depth thermo, capstone]
theorem claimF_superSouriauFermionGas_packet_ofIdentityBalancedStress
    {State : Type u} {EvenMoment : Type v} {OddMoment : Type w}
    (J :
      SuperSouriauFermionGasBridge.SuperMomentMapData
        State EvenMoment OddMoment)
    (P :
      SuperSouriauFermionGasBridge.SuperSouriauPairing
        State EvenMoment OddMoment)
    (x : State)
    (B : InfoGeometry.Canonical.BogoliubovFockSuper.BogoliubovMixingParams)
    (Hop Qodd : InfoGeometry.Canonical.BogoliubovFockSuper.FockEndomorphism H)
    (mu betaOdd : ℝ)
    (F :
      SuperSouriauFermionGasBridge.FermionicCAROperatorPair (E := H)) :
    let W :=
      SuperSouriauFermionGasBridge.WeylSupertraceFreeStressContext.ofIdentityBalanced
        (G := Unit) (Gdual := EvenMoment) (Orbit := State)
        J.evenMoment
        ()
        (fun _ _ => 0)
        (fun _ => SuperParity.even)
        J.stressTensorReadout
        x
    J.stressTensor x = J.stressTensorReadout (J.evenMoment x)
      ∧ J.supercurrent x = J.supercurrentReadout (J.oddMoment x)
      ∧ P.action x =
        P.beta.betaEven * P.evenEnergy x + P.beta.betaOdd * P.oddSource x
      ∧ SuperSouriauFermionGasBridge.superGrandCanonicalFockGenerator
          (E := H) B Hop mu betaOdd Qodd =
        SuperSouriauFermionGasBridge.evenGrandCanonicalFockGenerator
          (E := H) B Hop mu
          + SuperSouriauFermionGasBridge.oddFockSourceCoupling
            (E := H) betaOdd Qodd
      ∧ InfoGeometry.Canonical.BogoliubovFockSuper.fockSuperBracket
          (E := H)
          InfoGeometry.Canonical.BogoliubovFockSuper.SuperParity.odd
          InfoGeometry.Canonical.BogoliubovFockSuper.SuperParity.odd
          F.annihilation F.creation =
        SuperchargeCARCCRBridge.CARBracket
          (E := H) F.annihilation F.creation
      ∧ InfoGeometry.Canonical.BogoliubovFockSuper.fockAnticommutator
          (E := H) F.annihilation F.annihilation = 0
      ∧ InfoGeometry.Canonical.BogoliubovFockSuper.fockAnticommutator
          (E := H) F.creation F.creation = 0
      ∧ InfoGeometry.Canonical.BogoliubovFockSuper.fockAnticommutator
          (E := H) F.annihilation F.creation =
        ContinuousLinearMap.id ℝ (InfoGeometry.Krein.DoubledSpace H)
      ∧ W.superTrace W.stress = 0
      ∧ W.weylInvariant := by
  let W :=
    SuperSouriauFermionGasBridge.WeylSupertraceFreeStressContext.ofIdentityBalanced
      (G := Unit) (Gdual := EvenMoment) (Orbit := State)
      J.evenMoment
      ()
      (fun _ _ => 0)
      (fun _ => SuperParity.even)
      J.stressTensorReadout
      x
  exact
    ⟨J.stressTensor_eq_even_readout x,
      J.supercurrent_eq_odd_readout x,
      P.action_eq_even_add_odd x,
      SuperSouriauFermionGasBridge.superGrandCanonicalFockGenerator_eq_even_add_odd
        (E := H) B Hop mu betaOdd Qodd,
      SuperSouriauFermionGasBridge.odd_odd_superBracket_eq_CARBracket
        (E := H) F.annihilation F.creation,
      F.annihilation_anticommutator_self_zero,
      F.creation_anticommutator_self_zero,
      F.annihilation_creation_anticommutator_id,
      W.superTrace_stress_eq_zero,
      W.is_weyl_invariant⟩

/--
Claim G: infinite/coadjoint super-metriplectic lift.

This is the infinite-dimensional target surface for the supergraded Souriau
fermion-gas prose.  It works over arbitrary orbit and Lie/co-Lie carriers and
therefore does not reduce the claim to a finite Fock model.  The theorem only
packages the proof-carrying context:

* one super-coadjoint moment object supplies stress and supercurrent readouts;
* entropy is orbit-invariant/Casimir on the reversible channel;
* dissipative/Onsager entropy production is nonnegative;
* total entropy production reduces to the dissipative channel;
* Weyl covariance and supertrace-free stress are proof fields of the context.

No concrete `psu(2,2|4)`, super-Poincare representation, supermanifold, or
field-theoretic stress variation is constructed here.
-/
@[rep_depth thermo]
theorem claimG_infiniteSuperCoadjointMetriplectic_packet
    {G Gdual Orbit : Type*}
    (C : FullCoadjointOrbitMetriplecticContext G Gdual Orbit)
    (x : Orbit) :
    C.isCoadjointOrbit
      ∧ C.orbitInvariantEntropy
      ∧ C.stressTensorAt x =
        C.superMoment.stressTensorProjection (C.superMoment.moment x)
      ∧ C.supercurrentAt x =
        C.superMoment.supercurrentProjection (C.superMoment.moment x)
      ∧ C.reversibleEntropyRate x = 0
      ∧ 0 ≤ C.dissipativeEntropyRate x
      ∧ C.totalEntropyProduction x = C.dissipativeEntropyRate x
      ∧ 0 ≤ C.totalEntropyProduction x
      ∧ C.weylGaugeCovariant
      ∧ C.supertraceFreeStress := by
  have htotal :
      C.totalEntropyProduction x = C.dissipativeEntropyRate x := by
    rw [C.totalEntropyProduction_eq_sum x, C.reversibleEntropyRate_eq_zero x]
    simp
  exact ⟨C.isCoadjointOrbit_proof,
    C.orbitInvariantEntropy_proof,
    rfl,
    rfl,
    C.reversibleEntropyRate_eq_zero x,
    C.dissipativeEntropyRate_nonneg x,
    htotal,
    C.totalEntropyProduction_nonneg x,
    C.weylGaugeCovariant_proof,
    C.supertraceFreeStress_proof⟩

/--
Claim T: the split `Cl(4,4)`/TKK/Jordan-Lie corridor is available only through
the explicit operatorial closure packet.

This theorem deliberately projects existing owner results.  It does not claim
full `Spin(4,4)` triality, split-octonion classification, or an unconditional
TKK construction from all Jordan systems.
-/
@[rep_depth transport]
theorem claimT_splitCl44_TKK_JordanLie_packet
    (P : SplitCl44TKKJordanLiePacket (α := α) (H := H)) :
    P.closure.SatisfiesKKT_TKK_Weyl_JordanLieClosure
      ∧ P.closure.gibbs.SatisfiesOperatorTKKMasterRelation
        P.closure.tkkParameter
      ∧ P.closure.gibbs.IsOperatorAdmissible
      ∧ P.closure.gibbs.conformalGeometricTemperature =
        P.closure.gibbs.translationPotential • P.closure.gibbs.PGenerator
          + P.closure.gibbs.cartanPotential • P.closure.gibbs.cartanGenerator
            + P.closure.gibbs.dilationPotential • P.closure.gibbs.DGenerator
              + P.closure.gibbs.specialConformalPotential •
                P.closure.gibbs.KGenerator
      ∧ InfoGeometry.Canonical.BogoliubovFockSuper.fockCommutator (E := H)
        P.closure.gibbs.conformalGeometricTemperature P.closure.weylTemperature =
          (2 : ℝ) • P.closure.lieProductTemperatureWeyl
      ∧ InfoGeometry.Canonical.BogoliubovFockSuper.fockAnticommutator (E := H)
        P.closure.gibbs.conformalGeometricTemperature P.closure.weylTemperature =
          (2 : ℝ) • P.closure.jordanProductTemperatureWeyl
      ∧ P.triality.informationalDiracSquare = LinearMap.id :=
  ⟨P.satisfiesKKT_TKK_Weyl_JordanLieClosure,
    P.tkkMasterRelation,
    P.operatorAdmissible,
    P.closure.gibbs.conformalTemperature_eq_components,
    P.fockCommutator_temperature_weyl_eq_two_smul_lieProduct,
    P.fockAnticommutator_temperature_weyl_eq_two_smul_jordanProduct,
    P.triality_informationalDiracSquare_eq_id⟩

/-! ## Symplectic-leaf/Casimir and transverse Onsager split -/

/--
Claim M: coadjoint-orbit metriplectic split.

This is the formal translator for the prose statement:

* motion along the symplectic/coadjoint leaf is Casimir and produces zero
  entropy;
* transverse metric/Onsager motion is nonnegative entropy production;
* total entropy production is exactly the metric channel after the Casimir
  reversible channel vanishes.

The theorem is projected from the full coadjoint-orbit metriplectic context.
It does not derive a symplectic foliation from a concrete manifold; that model
must instantiate `InfiniteCoadjointOrbitMetriplecticContext`.
-/
@[rep_depth thermo]
theorem claimM_coadjointLeaf_Casimir_transverseOnsager_packet
    {Orbit : Type u} {LieAlg : Type v} {LieCoalg : Type w}
    (C : InfiniteCoadjointOrbitMetriplecticContext Orbit LieAlg LieCoalg)
    (x : Orbit) :
    C.isOnCoadjointOrbit (C.moment x)
      ∧ C.isOnCoadjointOrbit (C.moment (C.reversibleVectorField x))
      ∧ C.isOnCoadjointOrbit (C.moment (C.metricVectorField x))
      ∧ C.reversibleEntropyRate x = 0
      ∧ 0 ≤ C.metricEntropyRate x
      ∧ C.totalEntropyRate x = C.metricEntropyRate x
      ∧ 0 ≤ C.totalEntropyRate x :=
  C.full_coadjoint_orbit_metriplectic_theorem x

/--
Literature-facing finite Souriau/KKT theorem packet.

This is the conservative Lean target for the prose synthesis:

* Massieu/log-partition and finite moment readouts;
* finite Fisher/covariance and Onsager PSD entropy production;
* Fenchel-Legendre contact and gap nonnegativity;
* Karush-Kuhn-Tucker stationarity kept as explicit hypotheses.

The theorem is finite.  Full smooth/coadjoint-orbit Hessian and metriplectic
statements are exposed separately by the infinite-dimensional enrichment
packets below.
-/
@[rep_depth thermo]
theorem structuredSouriauKKTTranslatorPacket
    [Fintype α] [Nonempty α]
    (C : SouriauFenchelContext (α := α))
    (K : KKTEntropyStationarityShadow)
    (hPSD : (souriauFisherResponseMatrix C.M C.T).PositiveSemidefinite)
    (hCone : K.coneAdmissible)
    (hStationarity : K.stationarity)
    (hSlack : K.complementarySlackness)
    (hFinite : K.finitePartitionAdmissible)
    (eta xβ xμ : ℝ) :
    (souriauMassieuPotential C.M C.T = Real.log (souriauPartition C.M C.T)
      ∧ deriv (fun β => souriauMassieuPotential C.M { C.T with beta := β }) C.T.beta =
        -souriauMeanShift C.M C.T
      ∧ deriv (fun μ => souriauMassieuPotential C.M { C.T with mu := μ }) C.T.mu =
        C.T.beta * souriauMeanNumber C.M C.T
      ∧ (souriauFisherResponseMatrix C.M C.T).betaBeta =
        varianceShift (toGrandCanonicalTwoParam C.M) C.T.beta C.T.mu
      ∧ (souriauFisherResponseMatrix C.M C.T).muMu =
        C.T.beta ^ (2 : ℕ) *
          varianceNumber (toGrandCanonicalTwoParam C.M) C.T.beta C.T.mu
      ∧ (souriauFisherResponseMatrix C.M C.T).Symmetric
      ∧ 0 ≤ C.model.fenchelGap C.theta eta
      ∧ C.model.fenchelGap C.theta (C.model.dualCoord C.theta) = 0
      ∧ souriauMassieuPotential C.M C.T +
          C.model.φ (C.model.dualCoord C.theta) =
        C.theta * C.model.dualCoord C.theta
      ∧ 0 ≤ souriauEntropyProduction C.M C.T xβ xμ)
      ∧ K.coneAdmissible ∧ K.stationarity ∧
        K.complementarySlackness ∧ K.finitePartitionAdmissible :=
  ⟨structuredSouriauTranslatorPacket C hPSD eta xβ xμ,
    claimK_kktEntropyStationarity_packet
      K hCone hStationarity hSlack hFinite⟩

/--
Stage-2 theorem packet for the two analytic claims that the finite translator
does not own by itself:

* entropy Hessian equals inverse Fisher metric;
* zero entropy production is equivalent to zero thermodynamic force.

Both conclusions are projected from explicit proof-carrying gates.
-/
@[rep_depth thermo]
theorem analyticEnrichmentTranslatorPacket
    [Fintype α] [Nonempty α]
    (C : SouriauFenchelContext (α := α))
    (Ginv : EntropyFisherInverseGate)
    (Gstrict : StrictOnsagerEquilibriumGate C.M C.T)
    (xβ xμ : ℝ) :
    Ginv.entropyHessian = Ginv.fisherInverse
      ∧ (souriauEntropyProduction C.M C.T xβ xμ = 0
        ↔ Gstrict.forceIsZero xβ xμ) :=
  ⟨Ginv.claimD_entropy_hessian_eq_fisher_inverse,
    Gstrict.claimE_entropyProduction_eq_zero_iff_force_zero xβ xμ⟩

/-! ## Infinite-dimensional coadjoint-orbit enrichment -/

/--
Infinite-dimensional Claim C/D enrichment: the full coadjoint-orbit
Hessian/Fisher/covariance and inverse-Fisher theorem packet.

This is not derived from the finite translator layer.  It is projected from the
proof-carrying infinite-dimensional context whose fields encode the analytic
Massieu, moment, covariance, Fenchel-Legendre, and inverse-Hessian obligations.
-/
@[rep_depth thermo]
theorem claimCD_fullCoadjointOrbit_hessian_packet
    {Orbit : Type u} {LieAlg : Type v} {LieCoalg : Type w}
    {Tangent DualTangent : Type*}
    (C :
      InfiniteCoadjointOrbitHessianContext
        Orbit LieAlg LieCoalg Tangent DualTangent)
    (β : LieAlg) (Q : LieCoalg) (X Y : Tangent) :
    C.massieuPotential β = Real.log (C.partitionFunction β)
      ∧ C.first_variation_eq_moment
      ∧ C.second_variation_eq_fisher
      ∧ C.fisherHessian β = C.momentCovariance β
      ∧ C.fisherHessian β X Y = C.fisherHessian β Y X
      ∧ 0 ≤ C.fisherHessian β X X
      ∧ C.fenchel_legendre_contact
      ∧ C.entropy_gradient_eq_beta
      ∧ C.entropyHessian Q = C.inverseFisherHessian Q :=
  C.full_infinite_dimensional_coadjoint_orbit_hessian_theorem β Q X Y

/--
Strict infinite-dimensional Claim C/D enrichment under the explicit
nondegenerate-tangent gate.
-/
@[rep_depth thermo]
theorem claimCD_fullCoadjointOrbit_strict_hessian_packet
    {Orbit : Type u} {LieAlg : Type v} {LieCoalg : Type w}
    {Tangent DualTangent : Type*}
    (C :
      InfiniteCoadjointOrbitHessianContext
        Orbit LieAlg LieCoalg Tangent DualTangent)
    (β : LieAlg) (Q : LieCoalg) (X Y : Tangent)
    (hX : C.nonzeroTangent X) :
    C.massieuPotential β = Real.log (C.partitionFunction β)
      ∧ C.first_variation_eq_moment
      ∧ C.second_variation_eq_fisher
      ∧ C.fisherHessian β = C.momentCovariance β
      ∧ C.fisherHessian β X Y = C.fisherHessian β Y X
      ∧ 0 ≤ C.fisherHessian β X X
      ∧ 0 < C.fisherHessian β X X
      ∧ C.fenchel_legendre_contact
      ∧ C.entropy_gradient_eq_beta
      ∧ C.entropyHessian Q = C.inverseFisherHessian Q :=
  C.full_infinite_dimensional_coadjoint_orbit_strict_hessian_theorem
    β Q X Y hX

/--
Infinite-dimensional Claim C/D/E enrichment: full coadjoint-orbit Hessian
packet plus metriplectic second law.
-/
@[rep_depth thermo]
theorem claimCDE_fullCoadjointOrbit_hessian_metriplectic_packet
    {Orbit : Type u} {LieAlg : Type v} {LieCoalg : Type w}
    {Tangent DualTangent : Type*}
    (C :
      InfiniteCoadjointOrbitHessianMetriplecticContext
        Orbit LieAlg LieCoalg Tangent DualTangent)
    (β : LieAlg) (Q : LieCoalg) (X Y : Tangent) (x : Orbit) :
    C.hessian.massieuPotential β =
        Real.log (C.hessian.partitionFunction β)
      ∧ C.hessian.first_variation_eq_moment
      ∧ C.hessian.second_variation_eq_fisher
      ∧ C.hessian.fisherHessian β = C.hessian.momentCovariance β
      ∧ C.hessian.fisherHessian β X Y =
        C.hessian.fisherHessian β Y X
      ∧ 0 ≤ C.hessian.fisherHessian β X X
      ∧ C.hessian.fenchel_legendre_contact
      ∧ C.hessian.entropy_gradient_eq_beta
      ∧ C.hessian.entropyHessian Q =
        C.hessian.inverseFisherHessian Q
      ∧ 0 ≤ C.metriplectic.totalEntropyRate x :=
  C.full_infinite_dimensional_coadjoint_orbit_hessian_metriplectic_theorem
    β Q X Y x

/--
Strict infinite-dimensional Claim C/D/E enrichment: full coadjoint-orbit
Hessian packet with strict Fisher positivity plus metriplectic second law.
-/
@[rep_depth thermo]
theorem claimCDE_fullCoadjointOrbit_strict_hessian_metriplectic_packet
    {Orbit : Type u} {LieAlg : Type v} {LieCoalg : Type w}
    {Tangent DualTangent : Type*}
    (C :
      InfiniteCoadjointOrbitHessianMetriplecticContext
        Orbit LieAlg LieCoalg Tangent DualTangent)
    (β : LieAlg) (Q : LieCoalg) (X Y : Tangent) (x : Orbit)
    (hX : C.hessian.nonzeroTangent X) :
    C.hessian.massieuPotential β =
        Real.log (C.hessian.partitionFunction β)
      ∧ C.hessian.first_variation_eq_moment
      ∧ C.hessian.second_variation_eq_fisher
      ∧ C.hessian.fisherHessian β = C.hessian.momentCovariance β
      ∧ C.hessian.fisherHessian β X Y =
        C.hessian.fisherHessian β Y X
      ∧ 0 ≤ C.hessian.fisherHessian β X X
      ∧ 0 < C.hessian.fisherHessian β X X
      ∧ C.hessian.fenchel_legendre_contact
      ∧ C.hessian.entropy_gradient_eq_beta
      ∧ C.hessian.entropyHessian Q =
        C.hessian.inverseFisherHessian Q
      ∧ 0 ≤ C.metriplectic.totalEntropyRate x :=
  C.full_infinite_dimensional_coadjoint_orbit_strict_hessian_metriplectic_theorem
    β Q X Y x hX

end InfoGeometry.Canonical.SouriauTheoremTranslatorPacket
