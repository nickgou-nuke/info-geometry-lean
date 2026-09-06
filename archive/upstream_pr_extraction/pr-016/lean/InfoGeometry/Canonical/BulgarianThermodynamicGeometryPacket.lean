import InfoGeometry.Canonical.SouriauTheoremTranslatorPacket

set_option linter.dupNamespace false

/-!
# Bulgarian Thermodynamic Geometry Packet

Conservative multilingual translator-facing packet for the Bulgarian thermodynamic
geometry exposition about:

* Hessians and Fisher covariance,
* Fenchel-Legendre duality,
* Onsager operators,
* entropy production,
* metriplectic conservative/dissipative splitting.

This file is not a closure claim for the full analytic story.  It is a repo
artifact that turns the upstream Bulgarian exposition into Lean-facing theorem
families, symbol normalization, assumption layers, and conservative scaffold
interfaces.
-/

namespace InfoGeometry.Canonical.BulgarianThermodynamicGeometryPacket

open InfoGeometry.Canonical.SouriauTheoremTranslatorPacket

/-! ## Terminology normalization -/

/-- The normalized theorem families extracted from the Bulgarian source packet. -/
inductive BulgarianThermoFamily where
  | hessianFisherCovariance
  | fenchelLegendreDuality
  | onsagerMetriplecticDissipation
  | entropyProductionSecondLaw
  | poissonMetricSplit
  deriving DecidableEq, Repr

/-- Canonical Lean-facing family names for the Bulgarian theorem packet. -/
def canonicalFamilyName : BulgarianThermoFamily → String
  | .hessianFisherCovariance => "Hessian/Fisher/covariance"
  | .fenchelLegendreDuality => "FenchelLegendre/inverseMetric"
  | .onsagerMetriplecticDissipation => "Onsager/metriplectic/dissipation"
  | .entropyProductionSecondLaw => "entropyProduction/secondLaw"
  | .poissonMetricSplit => "PoissonLeaf/metricTransverse"

/-- Normalized symbols extracted from the Bulgarian packet. -/
inductive BulgarianThermoSymbol where
  | partitionFunction
  | massieuPotential
  | geometricTemperature
  | momentMap
  | thermodynamicMoment
  | fisherMetric
  | covarianceMetric
  | souriauEntropy
  | thermodynamicForce
  | onsagerOperator
  | entropyProduction
  | metriplecticFlow
  | poissonLeafFlow
  | metricTransverseFlow
  deriving DecidableEq, Repr

/-- Canonical Lean identifiers suggested for multilingual translation. -/
def canonicalSymbolName : BulgarianThermoSymbol → String
  | .partitionFunction => "partitionFunction"
  | .massieuPotential => "massieuPotential"
  | .geometricTemperature => "beta"
  | .momentMap => "momentMap"
  | .thermodynamicMoment => "thermodynamicMoment"
  | .fisherMetric => "fisherMetric"
  | .covarianceMetric => "covarianceMetric"
  | .souriauEntropy => "souriauEntropy"
  | .thermodynamicForce => "thermodynamicForce"
  | .onsagerOperator => "onsagerOperator"
  | .entropyProduction => "entropyProduction"
  | .metriplecticFlow => "metriplecticFlow"
  | .poissonLeafFlow => "poissonLeafFlow"
  | .metricTransverseFlow => "metricTransverseFlow"

/-! ## Assumption layers -/

/-- Interface-level assumptions for conservative first-pass formalization. -/
class BulgarianTierA (β Q X : Type _) where
  massieuPotential : β → ℝ
  thermodynamicMoment : β → Q
  fisherMetric : β → β → ℝ
  souriauEntropy : Q → ℝ
  thermodynamicForce : Q → X
  onsagerOperator : X → X → ℝ

/-- Finite-dimensional smoothness assumptions for Hessian/gradient surfaces. -/
class BulgarianTierB (β Q : Type _) where
  firstDerivativeExists : Prop
  secondDerivativeExists : Prop
  hessianSymmetric : Prop
  inverseMetricExists : Prop

/-- Analytic/statistical assumptions delayed behind an explicit gate. -/
class BulgarianTierC (β M : Type _) where
  partitionIntegralExists : Prop
  differentiationUnderIntegral : Prop
  covarianceIdentity : Prop
  nondegenerateCovariance : Prop

/-! ## Family A: Hessian / Fisher / covariance -/

structure BulgarianFamilyAInterface (β Q Obs : Type _) where
  potential : β → ℝ
  moment : β → Q
  fisherMetric : β → β → ℝ
  covarianceMetric : Obs → Obs → ℝ
  firstDerivativeEncodesMoments : Prop
  fisherEqMassieuHessian : Prop
  covarianceRealizesFisher : Prop
  fisherSymmetric : Prop
  fisherNonnegative : Prop
  fisherSymmetric_holds : fisherSymmetric
  fisherNonnegative_holds : fisherNonnegative

def familyA_fisher_symmetric
    {β Q Obs : Type _} (A : BulgarianFamilyAInterface β Q Obs) : Prop :=
  A.fisherSymmetric

def familyA_fisher_nonnegative
    {β Q Obs : Type _} (A : BulgarianFamilyAInterface β Q Obs) : Prop :=
  A.fisherNonnegative

/-! ## Family B: Fenchel-Legendre / inverse metric -/

structure BulgarianFamilyBInterface (β Q : Type _) where
  massieuPotential : β → ℝ
  souriauEntropy : Q → ℝ
  betaOfQ : Q → β
  entropyGradientRecoversBeta : Prop
  entropyHessianRealizesInverseFisher : Prop
  entropyGradientRecoversBeta_holds : entropyGradientRecoversBeta
  entropyHessianRealizesInverseFisher_holds : entropyHessianRealizesInverseFisher

def familyB_entropy_gradient_eq_beta
    {β Q : Type _} (B : BulgarianFamilyBInterface β Q) : Prop :=
  B.entropyGradientRecoversBeta

def familyB_entropy_hessian_eq_inverseFisher
    {β Q : Type _} (B : BulgarianFamilyBInterface β Q) : Prop :=
  B.entropyHessianRealizesInverseFisher

/-! ## Family C: Onsager / metriplectic dissipation -/

structure BulgarianFamilyCInterface (Q X : Type _) where
  thermodynamicForce : Q → X
  thermodynamicCurrent : Q → X
  onsagerOperator : X → X → ℝ
  currentEqOnsagerForce : Prop
  onsagerSymmetric : Prop
  onsagerPositiveSemidefinite : Prop
  onsagerSymmetric_holds : onsagerSymmetric
  onsagerPositiveSemidefinite_holds : onsagerPositiveSemidefinite

def familyC_onsager_symmetric
    {Q X : Type _} (C : BulgarianFamilyCInterface Q X) : Prop :=
  C.onsagerSymmetric

def familyC_onsager_positiveSemidefinite
    {Q X : Type _} (C : BulgarianFamilyCInterface Q X) : Prop :=
  C.onsagerPositiveSemidefinite

/-! ## Family D: entropy production / second law -/

structure BulgarianFamilyDInterface (X : Type _) where
  entropyProduction : X → ℝ
  quadraticFormRealization : Prop
  nonnegative : Prop
  vanishesAtEquilibrium : Prop
  nonnegative_holds : nonnegative
  vanishesAtEquilibrium_holds : vanishesAtEquilibrium

def familyD_entropyProduction_nonnegative
    {X : Type _} (D : BulgarianFamilyDInterface X) : Prop :=
  D.nonnegative

def familyD_entropyProduction_zero_at_equilibrium
    {X : Type _} (D : BulgarianFamilyDInterface X) : Prop :=
  D.vanishesAtEquilibrium

/-! ## Family E: Poisson-leaf vs transverse metric flow -/

structure BulgarianFamilyEInterface (S : Type _) where
  poissonPreservesEntropy : Prop
  metricIncreasesEntropy : Prop
  conservativeDissipativeSeparation : Prop
  poissonPreservesEntropy_holds : poissonPreservesEntropy
  metricIncreasesEntropy_holds : metricIncreasesEntropy

def familyE_poisson_entropy_constant
    {S : Type _} (E : BulgarianFamilyEInterface S) : Prop :=
  E.poissonPreservesEntropy

def familyE_metric_entropy_monotone
    {S : Type _} (E : BulgarianFamilyEInterface S) : Prop :=
  E.metricIncreasesEntropy

/-! ## Packet assembly -/

structure BulgarianThermoPacket
    (β Q Obs X S M : Type _) where
  familyA : BulgarianFamilyAInterface β Q Obs
  familyB : BulgarianFamilyBInterface β Q
  familyC : BulgarianFamilyCInterface Q X
  familyD : BulgarianFamilyDInterface X
  familyE : BulgarianFamilyEInterface S
  tierA : BulgarianTierA β Q X
  tierB : BulgarianTierB β Q
  tierC : BulgarianTierC β M

def packet_has_five_families
    {β Q Obs X S M : Type _}
    (P : BulgarianThermoPacket β Q Obs X S M) : Prop :=
    P.familyA.fisherSymmetric
      ∧ P.familyB.entropyGradientRecoversBeta
      ∧ P.familyC.onsagerSymmetric
      ∧ P.familyD.nonnegative
      ∧ P.familyE.poissonPreservesEntropy

/--
Compatibility note: the Bulgarian packet refines the same five-family translator
pipeline already exposed by `SouriauTheoremTranslatorPacket`, but keeps the
multilingual source packet explicit.
-/
def alignedWithSouriauTranslator : List String :=
  [ canonicalTheoremFamilyName SouriauTheoremFamily.hessianFisherCovariance
  , canonicalTheoremFamilyName SouriauTheoremFamily.fenchelLegendreDual
  , canonicalTheoremFamilyName SouriauTheoremFamily.onsagerEntropyProduction
  ]

end InfoGeometry.Canonical.BulgarianThermodynamicGeometryPacket
