import InfoGeometry.Canonical.BulgarianThermodynamicGeometryPacket

/-!
# Souriau Translator Audit

Audit contract for the multilingual Souriau theorem translator.

This module proves that the Bulgarian theorem-family normalization is aligned
with the compiled Souriau theorem packet.  It does not introduce new physics;
it is a deterministic routing layer from upstream prose categories to
repo-native theorem surfaces.
-/

namespace InfoGeometry.Canonical.SouriauTranslatorAudit

open InfoGeometry.Canonical.SouriauTheoremTranslatorPacket
open InfoGeometry.Canonical.BulgarianThermodynamicGeometryPacket
open InfoGeometry.Canonical.SouriauLieThermoKKTBridge
open InfoGeometry.Canonical.SouriauCoadjointOrbitMetriplectic
open InfoGeometry.Canonical.SouriauThermodynamics
open InfoGeometry.Canonical.SouriauFenchelOnsagerBridge
open InfoGeometry.Convex
open InfoGeometry.GrandCanonical

universe u v w

variable {α : Type _}
variable {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

/-! ## Family-name routing -/

/-- Bulgarian Hessian/Fisher/covariance maps to Souriau claim C. -/
@[rep_depth thermo]
theorem bulgarian_hessian_fisher_covariance_maps_to_claimC :
    canonicalFamilyName BulgarianThermoFamily.hessianFisherCovariance =
      "Hessian/Fisher/covariance"
      ∧ canonicalTheoremFamilyName SouriauTheoremFamily.hessianFisherCovariance =
        "hessian/Fisher/covariance" := by
  decide

/-- Bulgarian Fenchel-Legendre/inverse-metric prose maps to Souriau claim D. -/
@[rep_depth thermo]
theorem bulgarian_fenchel_legendre_maps_to_claimD :
    canonicalFamilyName BulgarianThermoFamily.fenchelLegendreDuality =
      "FenchelLegendre/inverseMetric"
      ∧ canonicalTheoremFamilyName SouriauTheoremFamily.fenchelLegendreDual =
        "FenchelLegendre/contact" := by
  decide

/-- Bulgarian Onsager/metriplectic prose maps to the Souriau Onsager family. -/
@[rep_depth thermo]
theorem bulgarian_onsager_metriplectic_maps_to_claimE :
    canonicalFamilyName BulgarianThermoFamily.onsagerMetriplecticDissipation =
      "Onsager/metriplectic/dissipation"
      ∧ canonicalTheoremFamilyName SouriauTheoremFamily.onsagerEntropyProduction =
        "Onsager/entropyProduction" := by
  decide

/--
The Bulgarian packet's explicit alignment list is exactly the three Souriau
families it currently routes to.
-/
@[rep_depth thermo]
theorem alignedWithSouriauTranslator_eq_expected :
    alignedWithSouriauTranslator =
      [ "hessian/Fisher/covariance"
      , "FenchelLegendre/contact"
      , "Onsager/entropyProduction" ] := by
  rfl

/-! ## Contract aliases to compiled theorem surfaces -/

/--
Audit alias for Claim A: partition/log-Massieu routing.
-/
@[rep_depth thermo]
theorem audit_claimA_massieu_eq_log_partition
    [Fintype α] [Nonempty α]
    (M : SouriauMomentMap α) (T : GeometricTemperature) :
    souriauMassieuPotential M T = Real.log (souriauPartition M T) :=
  claimA_massieu_eq_log_partition M T

/--
Audit alias for Claim B: first derivatives are conjugate moment readouts.
-/
@[rep_depth thermo]
theorem audit_claimB_firstDerivatives_eq_moments
    [Fintype α] [Nonempty α]
    (M : SouriauMomentMap α) (T : GeometricTemperature) :
    deriv (fun β => souriauMassieuPotential M { T with beta := β }) T.beta =
        -souriauMeanShift M T
      ∧ deriv (fun μ => souriauMassieuPotential M { T with mu := μ }) T.mu =
        T.beta * souriauMeanNumber M T :=
  claimB_firstDerivatives_eq_moments M T

/--
Audit alias for Claim C: Hessian/Fisher/covariance and symmetry packet.
-/
@[rep_depth thermo]
theorem audit_claimC_hessian_eq_fisher_eq_covariance
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
  claimC_hessian_eq_fisher_eq_covariance M T

/--
Audit alias for Claim D: finite Fenchel-Legendre contact packet.
-/
@[rep_depth thermo]
theorem audit_claimD_fenchelLegendre_contact_packet
    [Fintype α] [Nonempty α]
    (C : SouriauFenchelContext (α := α)) (eta : ℝ) :
    0 ≤ C.model.fenchelGap C.theta eta
      ∧ C.model.fenchelGap C.theta (C.model.dualCoord C.theta) = 0
      ∧ souriauMassieuPotential C.M C.T +
          C.model.φ (C.model.dualCoord C.theta) =
        C.theta * C.model.dualCoord C.theta :=
  claimD_fenchelLegendre_contact_packet C eta

/--
Audit alias for Claim E: finite Onsager second law under an explicit PSD gate.
-/
@[rep_depth thermo]
theorem audit_claimE_entropyProduction_nonneg_of_PSD
    [Fintype α] [Nonempty α]
    (M : SouriauMomentMap α) (T : GeometricTemperature)
    (hPSD : (souriauFisherResponseMatrix M T).PositiveSemidefinite)
    (xβ xμ : ℝ) :
    0 ≤ souriauEntropyProduction M T xβ xμ :=
  claimE_entropyProduction_nonneg_of_PSD M T hPSD xβ xμ

/--
Audit alias for Claim E with the finite PSD hypothesis reduced to the actual
remaining determinant gate.  Variance positivity supplies the diagonal entries.
-/
@[rep_depth thermo]
theorem audit_claimE_entropyProduction_nonneg_of_det_nonneg
    [Fintype α] [Nonempty α]
    (M : SouriauMomentMap α) (T : GeometricTemperature)
    (hdet : 0 ≤ (souriauFisherResponseMatrix M T).det)
    (xβ xμ : ℝ) :
    0 ≤ souriauEntropyProduction M T xβ xμ :=
  claimE_entropyProduction_nonneg_of_det_nonneg M T hdet xβ xμ

/--
Audit alias for the strict equality case in the finite Onsager second law.

This is the compiled version of the prose phrase "equality holds only at
equilibrium"; the positive-definite response gate is explicit.
-/
@[rep_depth thermo]
theorem audit_claimE_entropyProduction_eq_zero_iff_force_zero_of_PD
    [Fintype α] [Nonempty α]
    (M : SouriauMomentMap α) (T : GeometricTemperature)
    (hPD : (souriauFisherResponseMatrix M T).PositiveDefinite)
    (xβ xμ : ℝ) :
    souriauEntropyProduction M T xβ xμ = 0 ↔ xβ = 0 ∧ xμ = 0 :=
  claimE_entropyProduction_eq_zero_iff_force_zero_of_PD M T hPD xβ xμ

/--
Audit alias for the finite inverse-Fisher theorem actually owned by the repo.

This is the compiled replacement for the prose phrase "entropy Hessian is the
inverse Fisher metric" at the current finite level: the Souriau-Fisher response
matrix has a certified two-sided inverse on the non-spinodal locus `det ≠ 0`.
The smooth analytic Hessian identity remains represented by
`EntropyFisherInverseGate`.
-/
@[rep_depth thermo]
theorem audit_finite_inverseFisherMetric_of_det_ne_zero
    [Fintype α] [Nonempty α]
    (C : SouriauLieThermoKKTContext (α := α) (H := H))
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
  C.finite_inverseFisherMetric_of_det_ne_zero hdet

/--
Audit alias for the scalar analytic inverse-Hessian/Fisher enrichment.

This is the proof-carrying 1D Legendre version of the prose claim
`Hess(S) = Fisher⁻¹`.  It remains gated by the derivative witnesses and by the
non-spinodal condition `fisher θ ≠ 0`.
-/
@[rep_depth thermo]
theorem audit_claimD_scalarLegendre_inverseHessian_eq_inv_fisher
    (L : LegendrePotential) (θ a : ℝ)
    (hEta : HasDerivAt (LegendrePotential.eta L) (L.fisher θ) θ)
    (hTheta :
      HasDerivAt (LegendrePotential.thetaOfEta L) a
        (LegendrePotential.eta L θ))
    (hFisher : L.fisher θ ≠ 0) :
    a = (L.fisher θ)⁻¹ :=
  claimD_scalarLegendre_inverseHessian_eq_inv_fisher
    L θ a hEta hTheta hFisher

/--
Audit alias for the stage-2 analytic enrichment gates.
-/
@[rep_depth thermo]
theorem audit_analyticEnrichmentTranslatorPacket
    [Fintype α] [Nonempty α]
    (C : SouriauFenchelContext (α := α))
    (Ginv : EntropyFisherInverseGate)
    (Gstrict : StrictOnsagerEquilibriumGate C.M C.T)
    (xβ xμ : ℝ) :
    Ginv.entropyHessian = Ginv.fisherInverse
      ∧ (souriauEntropyProduction C.M C.T xβ xμ = 0
        ↔ Gstrict.forceIsZero xβ xμ) :=
  analyticEnrichmentTranslatorPacket C Ginv Gstrict xβ xμ

/-! ## Infinite-dimensional coadjoint-orbit audit aliases -/

/--
Audit alias for the full infinite-dimensional coadjoint-orbit
Hessian/Fisher/covariance and inverse-Fisher theorem packet.
-/
@[rep_depth thermo]
theorem audit_claimCD_fullCoadjointOrbit_hessian_packet
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
  claimCD_fullCoadjointOrbit_hessian_packet C β Q X Y

/--
Audit alias for the strict infinite-dimensional coadjoint-orbit Hessian packet.
The strict positivity conclusion is available only under the explicit
`nonzeroTangent` gate.
-/
@[rep_depth thermo]
theorem audit_claimCD_fullCoadjointOrbit_strict_hessian_packet
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
  claimCD_fullCoadjointOrbit_strict_hessian_packet C β Q X Y hX

/--
Audit alias for the full infinite-dimensional coadjoint-orbit Hessian packet
combined with the metriplectic second law.
-/
@[rep_depth thermo]
theorem audit_claimCDE_fullCoadjointOrbit_hessian_metriplectic_packet
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
  claimCDE_fullCoadjointOrbit_hessian_metriplectic_packet C β Q X Y x

/--
Audit alias for the strict infinite-dimensional coadjoint-orbit
Hessian/metriplectic theorem packet.
-/
@[rep_depth thermo]
theorem audit_claimCDE_fullCoadjointOrbit_strict_hessian_metriplectic_packet
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
  claimCDE_fullCoadjointOrbit_strict_hessian_metriplectic_packet
    C β Q X Y x hX

end InfoGeometry.Canonical.SouriauTranslatorAudit
