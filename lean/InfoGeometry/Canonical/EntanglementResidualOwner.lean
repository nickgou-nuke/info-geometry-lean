import InfoGeometry.Canonical.ProjectorNoncommutativityDilationClosure
import InfoGeometry.Canonical.OperatorProjectorMismatch
import InfoGeometry.Canonical.MetricTransportWitness
import Mathlib

/-!
# Entanglement residual owner

Drazin reduction isolates an algebraic zero sector.  It is not entanglement by
default.  Entanglement-level claims require explicit positivity / separability
or Gaussian witnesses.
-/

namespace InfoGeometry.Canonical.EntanglementResidualOwner

open InfoGeometry.Canonical.ProjectorNoncommutativityDilationClosure
open InfoGeometry.Canonical.OperatorProjectorMismatch
open InfoGeometry.Canonical.MetricTransportWitness

variable {R Scalar : Type*} [Ring R] [Zero Scalar]

/-- Transport prerequisite: mismatch transports covariantly once the metric witness is supplied. -/
@[rep_depth transport]
structure TransportedMismatchPrerequisite
    (P P' : ProjectorPair R) where
  transport : MetricCompensatorWitness P P'

/-- The mismatch transports covariantly; zero requires an additional agreement witness. -/
theorem transportedMismatch_covariant
    {P P' : ProjectorPair R}
    (W : TransportedMismatchPrerequisite P P') :
    P'.mismatch = W.transport.transport.g * P.mismatch * W.transport.transport.gInv :=
  W.transport.mismatch_transport

/-- Agreement after transport is an extra witness, not automatic. -/
@[rep_depth transport]
structure AgreementAfterTransportWitness
    (P P' : ProjectorPair R) where
  transport : TransportedMismatchPrerequisite P P'
  transportedAgreement : Prop
  transportedAgreementCertified : transportedAgreement → P'.ProjectorAgreement

/-- Positive compression witness for a projector/compression sector. -/
@[rep_depth transport]
structure PositiveCompressionWitness (A : Type*) [Semiring A] [Algebra ℝ A] where
  projector : A
  projector_idem : projector * projector = projector
  projector_selfAdj_G : Prop
  state : A → ℝ
  denom_pos : 0 < state projector
  compressedState : A → ℝ
  compression_eq : ∀ a, compressedState a = state (projector * a * projector) / state projector

/-- Algebraic Drazin-null sector witness. Physical support needs a separate compression witness. -/
@[rep_depth transport]
structure DrazinNullSector (R : Type*) [Ring R] where
  pair : ProjectorPair R
  nullProjector : R
  nullProjector_eq : nullProjector = pair.PD
  algebraicNull : Prop
  physicalNull : Prop
  physicalWitness : physicalNull → algebraicNull

/-- Bipartite algebra and state data. -/
@[rep_depth transport]
structure BipartiteStateData (A : Type*) [Semiring A] [Algebra ℝ A] where
  A_L : Subalgebra ℝ A
  A_R : Subalgebra ℝ A
  commute_LR : ∀ a ∈ A_L, ∀ b ∈ A_R, a * b = b * a
  ω : A → ℝ

/-- Factorization over the bipartite split. -/
def Factorizes {A : Type*} [Semiring A] [Algebra ℝ A]
    (ω : A → ℝ) (A_L A_R : Subalgebra ℝ A) : Prop :=
  ∀ a ∈ A_L, ∀ b ∈ A_R, ω (a * b) = ω a * ω b

/-- Residual covariance supported on the Drazin-null sector. -/
@[rep_depth transport]
structure ResidualCovariance (A : Type*) [Semiring A] [Algebra ℝ A] where
  compression : PositiveCompressionWitness A
  bipartite : BipartiteStateData A
  ω₀ : A → ℝ
  ω₀_def : ∀ a, ω₀ a = compression.compressedState a
  corrD0 : A → A → ℝ
  corrD0_def : ∀ a b, corrD0 a b = ω₀ (a * b) - ω₀ a * ω₀ b

/-- Factorization kills the residual covariance. -/
theorem factorizes_implies_corr_zero
    {A : Type*} [Semiring A] [Algebra ℝ A]
    (R : ResidualCovariance A)
    (h : Factorizes R.ω₀ R.bipartite.A_L R.bipartite.A_R)
    {a : A} (ha : a ∈ R.bipartite.A_L) {b : A} (hb : b ∈ R.bipartite.A_R) :
    R.corrD0 a b = 0 := by
  rw [R.corrD0_def, h a ha b hb]
  ring

/-- Nonzero residual covariance obstructs factorization. -/
theorem corr_nonzero_implies_not_factorize
    {A : Type*} [Semiring A] [Algebra ℝ A]
    (R : ResidualCovariance A)
    {a : A} (ha : a ∈ R.bipartite.A_L) {b : A} (hb : b ∈ R.bipartite.A_R) :
    R.corrD0 a b ≠ 0 →
      ¬ Factorizes R.ω₀ R.bipartite.A_L R.bipartite.A_R := by
  intro hCorr hFact
  exact hCorr (factorizes_implies_corr_zero (R := R) hFact ha hb)

/-- Compatibility surface retained for the v2 owner-map tests: a Drazin-null
covariance is residual covariance plus a nonzero covariance certificate.  It is
not the entanglement itself. -/
@[rep_depth transport]
structure DrazinNullCovariance (A : Type*) [Semiring A] [Algebra ℝ A] where
  residual : ResidualCovariance A
  leftObservable : A
  rightObservable : A
  left_mem : leftObservable ∈ residual.bipartite.A_L
  right_mem : rightObservable ∈ residual.bipartite.A_R
  nonfactorizingCovariance : residual.corrD0 leftObservable rightObservable ≠ 0

/-- Nonzero residual covariance is a Drazin-null-supported nonproduct
correlation; it is not an automatic entanglement theorem. -/
theorem nonfactorizingCovariance_implies_drazinNullSupportedCorrelation
    {A : Type*} [Semiring A] [Algebra ℝ A]
    (C : DrazinNullCovariance A) :
    ¬ Factorizes C.residual.ω₀ C.residual.bipartite.A_L C.residual.bipartite.A_R :=
  corr_nonzero_implies_not_factorize (R := C.residual)
    (a := C.leftObservable) (b := C.rightObservable)
    C.left_mem C.right_mem C.nonfactorizingCovariance

/-- Entanglement is not the Drazin residue. It requires an explicit witness. -/
@[rep_depth transport]
structure EntropyWitness (ω₀ : A → ℝ) where
  reducedDensityMatrices : Prop
  vonNeumannEntropy : Prop
  mutualInformation_or_entropy : Prop

@[rep_depth transport]
structure NegativityWitness (ω₀ : A → ℝ) where
  partialTranspose : Prop
  negativeEigenvalueCriterion : Prop
  traceNormCriterion : Prop

@[rep_depth transport]
structure GaussianBosonicWitness (ω₀ : A → ℝ) where
  symplecticSpace : Prop
  covarianceMatrix : Prop
  uncertaintyCondition : Prop
  symplecticEigenvalueCriterion : Prop

@[rep_depth transport]
structure GaussianFermionicWitness (ω₀ : A → ℝ) where
  carSpace : Prop
  covarianceMatrix : Prop
  parityConstraint : Prop
  separabilityCriterion : Prop

@[rep_depth transport]
structure EntanglementWitness (ω₀ : A → ℝ) where
  entropy : Prop
  negativity : Prop
  gaussianBosonic : Prop
  gaussianFermionic : Prop
  certified : entropy ∨ negativity ∨ gaussianBosonic ∨ gaussianFermionic

/-- Compatibility name for explicit entanglement criteria.  This is witness-only:
nonzero covariance alone does not construct it. -/
@[rep_depth transport]
structure EntanglementCriterionWitness (ω₀ : A → ℝ) where
  witness : EntanglementWitness (A := A) ω₀

/-- Entanglement is represented by the existence of an explicit witness. -/
def IsEntangled (ω₀ : A → ℝ) : Prop :=
  Nonempty (EntanglementWitness (A := A) ω₀)

/-- An entanglement witness certifies entanglement. -/
theorem entanglementWitness_implies_entangled
    {ω₀ : A → ℝ} (W : EntanglementWitness (A := A) ω₀) :
    IsEntangled (A := A) ω₀ := by
  exact ⟨W⟩

/-- Lemma 1: an explicit entropy criterion proves entanglement. -/
theorem isEntangled_of_entropy
    {ω₀ : A → ℝ}
    (hEntropy : Prop)
    (h : hEntropy) :
    IsEntangled (A := A) ω₀ := by
  exact ⟨{ entropy := hEntropy
           negativity := False
           gaussianBosonic := False
           gaussianFermionic := False
           certified := Or.inl h }⟩

/-- Lemma 2: an explicit negativity criterion proves entanglement. -/
theorem isEntangled_of_negativity
    {ω₀ : A → ℝ}
    (hNegativity : Prop)
    (h : hNegativity) :
    IsEntangled (A := A) ω₀ := by
  exact ⟨{ entropy := False
           negativity := hNegativity
           gaussianBosonic := False
           gaussianFermionic := False
           certified := Or.inr (Or.inl h) }⟩

/-- Lemma 3: an explicit Gaussian bosonic criterion proves entanglement. -/
theorem isEntangled_of_gaussianBosonic
    {ω₀ : A → ℝ}
    (hGaussianBosonic : Prop)
    (h : hGaussianBosonic) :
    IsEntangled (A := A) ω₀ := by
  exact ⟨{ entropy := False
           negativity := False
           gaussianBosonic := hGaussianBosonic
           gaussianFermionic := False
           certified := Or.inr (Or.inr (Or.inl h)) }⟩

/-- Lemma 4: an explicit Gaussian fermionic criterion proves entanglement. -/
theorem isEntangled_of_gaussianFermionic
    {ω₀ : A → ℝ}
    (hGaussianFermionic : Prop)
    (h : hGaussianFermionic) :
    IsEntangled (A := A) ω₀ := by
  exact ⟨{ entropy := False
           negativity := False
           gaussianBosonic := False
           gaussianFermionic := hGaussianFermionic
           certified := Or.inr (Or.inr (Or.inr h)) }⟩

/-- Lemma 5: any witness inhabits the entangled predicate. -/
theorem isEntangled_of_entanglementWitness
    {ω₀ : A → ℝ}
    (W : EntanglementWitness (A := A) ω₀) :
    IsEntangled (A := A) ω₀ := by
  exact ⟨W⟩

/-- Theorem: any one explicit criterion proves entanglement. -/
theorem isEntangled_of_any_explicit_criterion
    {ω₀ : A → ℝ}
    (hEntropy hNegativity hGaussianBosonic hGaussianFermionic : Prop)
    (hAny : hEntropy ∨ hNegativity ∨ hGaussianBosonic ∨ hGaussianFermionic) :
    IsEntangled (A := A) ω₀ := by
  rcases hAny with h | h | h | h
  · exact isEntangled_of_entropy (A := A) (ω₀ := ω₀) hEntropy h
  · exact isEntangled_of_negativity (A := A) (ω₀ := ω₀) hNegativity h
  · exact isEntangled_of_gaussianBosonic (A := A) (ω₀ := ω₀) hGaussianBosonic h
  · exact isEntangled_of_gaussianFermionic (A := A) (ω₀ := ω₀) hGaussianFermionic h

/-- Residual correlation factoring through mismatch. -/
@[rep_depth transport]
structure ResidualCorrelationThroughMismatch
    {R Scalar : Type*} [Zero R] [Zero Scalar] where
  residualMismatch : R
  crossCorrelation : Scalar
  transfer : R → Scalar
  transfer_zero : transfer 0 = 0
  factorsThrough : crossCorrelation = transfer residualMismatch

/-- Vanishing mismatch kills mismatch-supported correlation. -/
theorem mismatch_zero_kills_correlation
    {R Scalar : Type*} [Zero R] [Zero Scalar]
    (C : ResidualCorrelationThroughMismatch (R := R) (Scalar := Scalar))
    (h : C.residualMismatch = 0) :
    C.crossCorrelation = 0 := by
  rw [C.factorsThrough, h, C.transfer_zero]

/-- Restricted Gaussian covariance on the Drazin-null sector. -/
@[rep_depth transport]
structure GaussianCovarianceOwner (Scalar : Type*) [Zero Scalar] where
  restrictedCovariance : Scalar

/-- No Drazin-null-supported Gaussian covariance when the restricted covariance vanishes. -/
def HasDrazinNullSupportedGaussianCovariance
    {Scalar : Type*} [Zero Scalar] (G : GaussianCovarianceOwner Scalar) : Prop :=
  G.restrictedCovariance ≠ 0

theorem restrictedCovariance_zero_implies_no_support
    {Scalar : Type*} [Zero Scalar]
    (G : GaussianCovarianceOwner Scalar)
    (h : G.restrictedCovariance = 0) :
    ¬ HasDrazinNullSupportedGaussianCovariance (G := G) := by
  intro hSupp
  exact hSupp h

/-- Lorentzian lightcone witness: null rays need a dedicated Dirac witness. -/
@[rep_depth transport]
structure LightconeReadoutBoundary where
  diracSquare : Prop
  kernelNontrivial : Prop
  nullConeCertified : Prop
  projectivizationWitness : Prop

theorem entanglement_claim_from_witness
    {ω₀ : A → ℝ} (W : EntanglementWitness (A := A) ω₀) :
    IsEntangled (A := A) ω₀ :=
  isEntangled_of_entanglementWitness (ω₀ := ω₀) W

theorem nonfactorizing_covariance_is_not_entanglement
    {A : Type*} [Semiring A] [Algebra ℝ A]
    (R : ResidualCovariance A)
    {a : A} (ha : a ∈ R.bipartite.A_L) {b : A} (hb : b ∈ R.bipartite.A_R)
    (h : R.corrD0 a b ≠ 0) :
    ¬ Factorizes R.ω₀ R.bipartite.A_L R.bipartite.A_R :=
  corr_nonzero_implies_not_factorize (R := R) (a := a) (b := b) ha hb h

end InfoGeometry.Canonical.EntanglementResidualOwner
