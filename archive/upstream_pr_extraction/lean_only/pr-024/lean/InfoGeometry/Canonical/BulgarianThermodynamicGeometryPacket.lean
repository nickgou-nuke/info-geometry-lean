import InfoGeometry.Canonical.SouriauTheoremTranslatorPacket

set_option linter.dupNamespace false

namespace InfoGeometry.Canonical.BulgarianThermodynamicGeometryPacket

variable (β Q Obs X S M : Type _)

/-! ## Tier A: explicit sockets, not fake theorems -/

/-- Partition-function socket with the positivity law needed by thermodynamics. -/
structure PositivePartitionFunction where
  Z : β → ℝ
  positive : ∀ b : β, 0 < Z b

/-- Symplectic-form socket reduced to the antisymmetry law available over a bare carrier. -/
structure SymplecticStructure where
  omega : S → S → ℝ
  antisymmetric : ∀ x y : S, omega x y = -omega y x

/-- Positive-temperature socket. -/
structure PositiveTemperature where
  temperature : β → ℝ
  positive : ∀ b : β, 0 < temperature b

def has_smooth_partition_function : Prop :=
  ∃ Z : PositivePartitionFunction β, ∀ b : β, 0 < Z.Z b

def has_symplectic_structure : Prop :=
  ∃ Ω : SymplecticStructure S, ∀ x y : S, Ω.omega x y = -Ω.omega y x

def has_positive_temperature : Prop :=
  ∃ T : PositiveTemperature β, ∀ b : β, 0 < T.temperature b

/-! ## Tier B -/

/-- Legendre transform socket as an explicit inverse pair between beta and charge coordinates. -/
structure LegendreTransformData where
  toCharge : β → Q
  toBeta : Q → β
  left_inv : ∀ b : β, toBeta (toCharge b) = b
  right_inv : ∀ q : Q, toCharge (toBeta q) = q

/-- Strict-convexity socket over a bare parameter carrier, represented by a positive gap. -/
structure StrictConvexityData where
  gap : β → β → ℝ
  gap_pos : ∀ x y : β, x ≠ y → 0 < gap x y

/-- Injective inverse-temperature coordinate map. -/
structure InverseTemperatureInjection where
  inverseTemperature : Q → β
  injective : Function.Injective inverseTemperature

def legendreTransformExists : Prop :=
  ∃ L : LegendreTransformData β Q,
    (∀ b : β, L.toBeta (L.toCharge b) = b)
      ∧ (∀ q : Q, L.toCharge (L.toBeta q) = q)

def convexityStrict : Prop :=
  ∃ C : StrictConvexityData β, ∀ x y : β, x ≠ y → 0 < C.gap x y

def inverseTemperatureMapInjective : Prop :=
  ∃ I : InverseTemperatureInjection β Q, Function.Injective I.inverseTemperature

/-! ## Tier C -/

/-- Partition integral readout: an integral value equal to the partition function at each point. -/
structure PartitionIntegralData where
  Z : β → ℝ
  integral : β → ℝ
  integral_eq_partition : ∀ b : β, integral b = Z b

/-- Differentiation-under-integral socket with a declared derivative readout. -/
structure DifferentiationUnderIntegralData where
  integral : β → ℝ
  derivative : β → ℝ
  differentiatedIntegrand : β → ℝ
  derivative_eq_integrand : ∀ b : β, derivative b = differentiatedIntegrand b

/-- Covariance identity socket: covariance is represented by a bilinear-looking readout. -/
structure CovarianceIdentityData where
  covariance : Obs → Obs → ℝ
  readout : Obs → Obs → ℝ
  covariance_eq_readout : ∀ x y : Obs, covariance x y = readout x y

/-- Nondegenerate covariance socket using diagonal positivity for nonzero observations. -/
structure NondegenerateCovarianceData where
  zeroObs : Obs
  covariance : Obs → Obs → ℝ
  nondegenerate : ∀ x : Obs, x ≠ zeroObs → 0 < covariance x x

def partitionIntegralExists : Prop :=
  ∃ P : PartitionIntegralData β, ∀ b : β, P.integral b = P.Z b

def differentiationUnderIntegral : Prop :=
  ∃ D : DifferentiationUnderIntegralData β,
    ∀ b : β, D.derivative b = D.differentiatedIntegrand b

def covarianceIdentity : Prop :=
  ∃ C : CovarianceIdentityData Obs, ∀ x y : Obs, C.covariance x y = C.readout x y

def nondegenerateCovariance : Prop :=
  ∃ C : NondegenerateCovarianceData Obs,
    ∀ x : Obs, x ≠ C.zeroObs → 0 < C.covariance x x

/-! ## Family A: Hessian / Fisher / covariance -/
variable (potential : β → ℝ)
variable (moment : β → Q)
variable (fisherMetric : β → β → ℝ)
variable (covarianceMetric : Obs → Obs → ℝ)

def firstDerivativeEncodesMoments : Prop :=
  ∃ derivative : β → Q, ∀ b : β, derivative b = moment b

def fisherEqMassieuHessian : Prop :=
  ∃ hessian : β → β → ℝ, ∀ x y : β, fisherMetric x y = hessian x y

def covarianceRealizesFisher : Prop :=
  ∃ encode : β → Obs, ∀ x y : β,
    fisherMetric x y = covarianceMetric (encode x) (encode y)

theorem fisherSymmetric
    (hfisherSymmetric : ∀ x y : β, fisherMetric x y = fisherMetric y x)
    (x y : β) : fisherMetric x y = fisherMetric y x :=
  hfisherSymmetric x y

theorem fisherNonnegative
    (hfisherNonnegative : ∀ x : β, 0 ≤ fisherMetric x x)
    (x : β) : 0 ≤ fisherMetric x x :=
  hfisherNonnegative x

/-! ## Family B: Fenchel-Legendre / inverse metric -/
variable (massieuPotential : β → ℝ)
variable (souriauEntropy : Q → ℝ)
variable (betaOfQ : Q → β)

def entropyGradientRecoversBeta : Prop :=
  ∃ entropyGradient : Q → β, ∀ q : Q, entropyGradient q = betaOfQ q

def entropyHessianRealizesInverseFisher : Prop :=
  ∃ entropyHessian : Q → Q → ℝ,
    ∀ q r : Q, entropyHessian q r = fisherMetric (betaOfQ q) (betaOfQ r)

/-! ## Family C: Onsager / metriplectic dissipation -/
variable (thermodynamicForce : Q → X)
variable (thermodynamicCurrent : Q → X)
variable (onsagerOperator : X → X → ℝ)

def currentEqOnsagerForce : Prop :=
  ∀ q : Q, thermodynamicCurrent q = thermodynamicForce q

theorem onsagerSymmetric
    (honsagerSymmetric : ∀ x y : X, onsagerOperator x y = onsagerOperator y x)
    (x y : X) : onsagerOperator x y = onsagerOperator y x :=
  honsagerSymmetric x y

theorem onsagerPositiveSemidefinite
    (honsagerPositiveSemidefinite : ∀ x : X, 0 ≤ onsagerOperator x x)
    (x : X) : 0 ≤ onsagerOperator x x :=
  honsagerPositiveSemidefinite x

/-! ## Family D: entropy production / second law -/
variable (entropyProduction : X → ℝ)

def quadraticFormRealization : Prop :=
  ∃ quadratic : X → ℝ, ∀ x : X, entropyProduction x = quadratic x

theorem nonnegative_entropy
    (hnonnegative_entropy : ∀ x : X, 0 ≤ entropyProduction x)
    (x : X) : 0 ≤ entropyProduction x :=
  hnonnegative_entropy x

def vanishesAtEquilibrium : Prop :=
  ∃ equilibrium : X, entropyProduction equilibrium = 0

/-! ## Family E: Poisson-leaf vs transverse metric flow -/

def poissonPreservesEntropy : Prop :=
  ∃ poissonFlow : X → X, ∀ x : X, entropyProduction (poissonFlow x) = entropyProduction x

def metricIncreasesEntropy : Prop :=
  ∃ metricFlow : X → X, ∀ x : X, entropyProduction x ≤ entropyProduction (metricFlow x)

def conservativeDissipativeSeparation : Prop :=
  ∃ conservative dissipative : X → X,
    (∀ x : X, entropyProduction (conservative x) = entropyProduction x)
      ∧ (∀ x : X, entropyProduction x ≤ entropyProduction (dissipative x))

/-! ## Packet assembly -/

open InfoGeometry.Canonical
open InfoGeometry.Canonical.SouriauTheoremTranslatorPacket

def alignedWithSouriauTranslator : List String :=
  [ canonicalTheoremFamilyName SouriauTheoremFamily.hessianFisherCovariance
  , canonicalTheoremFamilyName SouriauTheoremFamily.fenchelLegendreDual
  , canonicalTheoremFamilyName SouriauTheoremFamily.onsagerEntropyProduction
  ]

end InfoGeometry.Canonical.BulgarianThermodynamicGeometryPacket
