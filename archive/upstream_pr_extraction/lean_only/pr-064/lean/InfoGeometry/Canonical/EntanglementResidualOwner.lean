import InfoGeometry.Canonical.ProjectorNoncommutativityDilationClosure
import InfoGeometry.Canonical.OperatorProjectorMismatch
import InfoGeometry.Canonical.MetricTransport
import InfoGeometry.Holography.RyuTakayanagiEmergence
import InfoGeometry.Canonical.WeylFiveGradePhysicalReadoutBridge
import Mathlib.Tactic
import Mathlib.LinearAlgebra.Projectivization.Basic
import Mathlib.LinearAlgebra.QuadraticForm.Basic

/-!
# Entanglement residual owner

Drazin reduction isolates an algebraic zero sector.  It is not entanglement by
default.  Entanglement-level claims require explicit positivity / separability
or Gaussian witnesses.
-/

namespace InfoGeometry.Canonical.EntanglementResidualOwner

open InfoGeometry.Canonical.ProjectorNoncommutativityDilationClosure
open InfoGeometry.Canonical.OperatorProjectorMismatch
open InfoGeometry.Canonical.MetricTransport

variable {R Scalar : Type*} [Ring R] [Zero Scalar]

/-- Transport prerequisite: mismatch transports covariantly once metric transport is supplied. -/
@[rep_depth transport]
structure TransportedMismatchPrerequisite
    (P P' : ProjectorPair R) where
  transport : SimilarityTransport P P'

/-- The mismatch transports covariantly; zero requires an additional agreement property. -/
theorem transportedMismatch_covariant
    {P P' : ProjectorPair R}
    (W : TransportedMismatchPrerequisite P P') :
    P'.mismatch = W.transport.g * P.mismatch * W.transport.gInv :=
  mismatch_covariant_of_similarityTransport W.transport

/-- Agreement after transport is extra data, not automatic. -/
@[rep_depth transport]
structure AgreementAfterTransport
    (P P' : ProjectorPair R) where
  transport : TransportedMismatchPrerequisite P P'
  transportedAgreement : P'.ProjectorAgreement

/-- Transported agreement is enough to certify projector agreement. -/
theorem transportedAgreement_implies_projectorAgreement
    {P P' : ProjectorPair R}
    (W : AgreementAfterTransport P P') :
    P'.ProjectorAgreement :=
  W.transportedAgreement

/-- Agreement after transport can be read back as equality of the transported projectors. -/
theorem transportedAgreement_implies_projectorEquality
    {P P' : ProjectorPair R}
    (W : AgreementAfterTransport P P') :
    P'.PD = P'.PMP :=
  (ProjectorPair.projectorAgreement_iff_eq (P := P')).1 W.transportedAgreement

/-- Normalized compression of a state by an idempotent projector. -/
noncomputable def normalizedCompression
    {A : Type*} [Semiring A] [Star A] [Algebra ℝ A]
    (projector : A) (state : A → ℝ) (a : A) : ℝ :=
  state (projector * a * projector) / state projector

/-- Algebraic Drazin-null sector property. Physical support needs a separate compression property. -/
@[rep_depth transport]
structure DrazinNullSector (R : Type*) [Ring R] where
  pair : ProjectorPair R
  /-- The null projector annihilates every observable after compression. -/
  algebraicNull : ∀ a : R, pair.PD * a * pair.PD = 0
  /-- The physical null sector is represented by left annihilation. -/
  physicalNull : ∀ a : R, pair.PD * a = 0
  /-- Left annihilation implies the compressed algebraic null law. -/
  physicalWitness : ∀ a : R, (pair.PD * a = 0) →
    (pair.PD * a * pair.PD = 0)

namespace DrazinNullSector

/-- The null projector is the canonical projector supplied by the pair. -/
abbrev nullProjector {R : Type*} [Ring R]
    (W : DrazinNullSector R) : R :=
  W.pair.PD

@[simp] theorem nullProjector_eq
    {R : Type*} [Ring R] (W : DrazinNullSector R) :
    W.nullProjector = W.pair.PD :=
  rfl

end DrazinNullSector

theorem DrazinNullSector.nullProjector_idempotent
    {R : Type*} [Ring R] (W : DrazinNullSector R) :
    W.nullProjector * W.nullProjector = W.nullProjector := by
  rw [W.nullProjector_eq]
  exact W.pair.PD_idempotent

/- Left annihilation implies compressed annihilation by associativity and
 zero multiplication. -/
theorem DrazinNullSector.physicalNull_implies_compressedNull
    {R : Type*} [Ring R] (W : DrazinNullSector R) (a : R)
    (h : W.nullProjector * a = 0) :
    W.nullProjector * a * W.nullProjector = 0 := by
  rw [h, zero_mul]

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
structure ResidualCovariance (A : Type*) [Semiring A] [Star A] [Algebra ℝ A] where
  projector : A
  projector_idem : projector * projector = projector
  projector_selfAdj_G : IsSelfAdjoint projector
  state : A → ℝ
  denom_pos : 0 < state projector
  bipartite : BipartiteStateData A
  ω₀ : A → ℝ
  ω₀_def : ∀ a, ω₀ a = normalizedCompression projector state a
  corrD0 : A → A → ℝ
  corrD0_def : ∀ a b, corrD0 a b = ω₀ (a * b) - ω₀ a * ω₀ b

/- The residual covariance is symmetric on commuting observables. -/
theorem corrD0_commute
    {A : Type*} [Semiring A] [Star A] [Algebra ℝ A]
    (R : ResidualCovariance A) {a b : A} (hab : a * b = b * a) :
    R.corrD0 a b = R.corrD0 b a := by
  rw [R.corrD0_def, R.corrD0_def, hab]
  ring

/- The covariance readout is explicitly the centered normalized projector
 compression of the state. -/
theorem corrD0_eq_normalized_compression
    {A : Type*} [Semiring A] [Star A] [Algebra ℝ A]
    (R : ResidualCovariance A) (a b : A) :
    R.corrD0 a b =
      R.state (R.projector * (a * b) * R.projector) /
          R.state R.projector -
        (R.state (R.projector * a * R.projector) /
            R.state R.projector) *
          (R.state (R.projector * b * R.projector) /
            R.state R.projector) := by
  rw [R.corrD0_def, R.ω₀_def, R.ω₀_def, R.ω₀_def]
  simp only [normalizedCompression]

/-- Factorization kills the residual covariance. -/
theorem factorizes_implies_corr_zero
    {A : Type*} [Semiring A] [Star A] [Algebra ℝ A]
    (R : ResidualCovariance A)
    (h : Factorizes R.ω₀ R.bipartite.A_L R.bipartite.A_R)
    {a : A} (ha : a ∈ R.bipartite.A_L) {b : A} (hb : b ∈ R.bipartite.A_R) :
    R.corrD0 a b = 0 := by
  rw [R.corrD0_def, h a ha b hb]
  ring

/-- Nonzero residual covariance obstructs factorization. -/
theorem corr_nonzero_implies_not_factorize
    {A : Type*} [Semiring A] [Star A] [Algebra ℝ A]
    (R : ResidualCovariance A)
    {a : A} (ha : a ∈ R.bipartite.A_L) {b : A} (hb : b ∈ R.bipartite.A_R) :
    R.corrD0 a b ≠ 0 →
      ¬ Factorizes R.ω₀ R.bipartite.A_L R.bipartite.A_R := by
  intro hCorr hFact
  exact hCorr (factorizes_implies_corr_zero (R := R) hFact ha hb)

/-- Nonzero residual covariance is a Drazin-null-supported nonproduct
correlation; it is not an automatic entanglement theorem. -/
@[rep_depth transport]
theorem nonfactorizingCovariance_implies_drazinNullSupportedCorrelation
    {A : Type*} [Semiring A] [Star A] [Algebra ℝ A]
    (R : ResidualCovariance A) (a b : A)
    (ha : a ∈ R.bipartite.A_L) (hb : b ∈ R.bipartite.A_R)
    (h : R.corrD0 a b ≠ 0) :
    ¬ Factorizes R.ω₀ R.bipartite.A_L R.bipartite.A_R :=
  corr_nonzero_implies_not_factorize (R := R) ha hb h

/-- Entropy property: the existing two-state RT owner theorem gives a concrete
entropy readout. -/
noncomputable def entropyReadout_of_twoStateRT : ℝ :=
  InfoGeometry.Holography.RyuTakayanagiEmergence.vonNeumannEntropy (1 / 2 : ℝ)

/- The RT owner theorem pins the concrete readout to `log 2`. -/
theorem entropyReadout_of_twoStateRT_eq_ln2 :
    entropyReadout_of_twoStateRT = Real.log 2 := by
  dsimp [entropyReadout_of_twoStateRT]
  simpa using InfoGeometry.Holography.RyuTakayanagiEmergence.maxEntropy_twoState

/-- Negativity property: a residual covariance packet plus a property nonzero
covariance readout. -/
@[rep_depth transport]

theorem negativity_blocks_factorization
    {A : Type*} [Semiring A] [Star A] [Algebra ℝ A]
    (R : ResidualCovariance A) (a b : A)
    (ha : a ∈ R.bipartite.A_L) (hb : b ∈ R.bipartite.A_R)
    (_h : R.corrD0 a b ≠ 0) :
    ¬ Factorizes R.ω₀ R.bipartite.A_L R.bipartite.A_R :=
  nonfactorizingCovariance_implies_drazinNullSupportedCorrelation
    (A := A) R a b ha hb _h

/- The positive-compression property exposes the idempotent projector law. -/
theorem residualCovariance_projector_idem
    {A : Type*} [Semiring A] [Star A] [Algebra ℝ A]
    (W : ResidualCovariance A) :
    W.projector * W.projector = W.projector :=
  W.projector_idem

/-- The positive-compression property exposes the self-adjoint projector side-condition. -/
def residualCovariance_projector_selfAdj_G
    {A : Type*} [Semiring A] [Star A] [Algebra ℝ A]
    (W : ResidualCovariance A) : IsSelfAdjoint W.projector :=
  W.projector_selfAdj_G

/-- The compression formula on the projector itself unfolds to the compressed
state at the idempotent projector. -/
theorem residualCovariance_compression_on_projector
    {A : Type*} [Semiring A] [Star A] [Algebra ℝ A]
    (W : ResidualCovariance A) :
    normalizedCompression W.projector W.state W.projector =
      W.state (W.projector * W.projector) / W.state W.projector := by
  have hnum :
      W.projector * W.projector * W.projector =
        W.projector * W.projector :=
    congrArg (fun x => x * W.projector) W.projector_idem
  dsimp [normalizedCompression]
  rw [hnum]

/-- The normalized compression fixes its supporting projector. -/
theorem residualCovariance_compression_on_projector_eq_one
    {A : Type*} [Semiring A] [Star A] [Algebra ℝ A]
    (W : ResidualCovariance A) :
    normalizedCompression W.projector W.state W.projector = 1 := by
  rw [residualCovariance_compression_on_projector W]
  rw [W.projector_idem]
  exact div_self (ne_of_gt W.denom_pos)

/-- The Drazin-null sector exposes its physical-null property. -/
def drazinNullSector_physicalNull
    (W : DrazinNullSector R) (a : R) : W.nullProjector * a = 0 :=
  W.physicalNull a

/-- The Drazin-null sector exposes the implication from physical nullity to algebraic nullity. -/
theorem drazinNullSector_physicalWitness
    (W : DrazinNullSector R) :
    ∀ a : R, (W.nullProjector * a = 0) →
      (W.nullProjector * a * W.nullProjector = 0) :=
  W.physicalWitness

/-- Entanglement is the direct disjunction of the finite criteria owned here. -/
def IsEntangled (A : Type*) [Semiring A] [Star A] [Algebra ℝ A] : Prop :=
  (∃ entropyReadout : ℝ, entropyReadout = Real.log 2) ∨
  (∃ (residual : ResidualCovariance A) (leftObservable rightObservable : A),
    leftObservable ∈ residual.bipartite.A_L ∧
    rightObservable ∈ residual.bipartite.A_R ∧
    residual.corrD0 leftObservable rightObservable ≠ 0) ∨
  (∃ E : Type, ∃ hE : NormedAddCommGroup E, ∃ hI : InnerProductSpace ℝ E,
      ∃ hC : CompleteSpace E,
        Nonempty (@WeylFiveGradePhysicalReadoutBridge.WeylFockPhysicalReadoutCarrier
          E hE hI hC)) ∨
  (∃ E : Type, ∃ hE : NormedAddCommGroup E, ∃ hI : InnerProductSpace ℝ E,
      ∃ hC : CompleteSpace E,
        Nonempty (@InfoGeometry.Canonical.ScaledCARPair E hE hI hC))

/-- Lemma 1: an explicit entropy property proves entanglement. -/
theorem isEntangled_of_entropy
    {A : Type*} [Semiring A] [Star A] [Algebra ℝ A]
    (entropyReadout : ℝ) (hEntropy : entropyReadout = Real.log 2) :
    IsEntangled A := by
  exact Or.inl ⟨entropyReadout, hEntropy⟩

/-- The two-state RT entropy property directly certifies entanglement. -/
theorem isEntangled_of_twoStateRT
    {A : Type*} [Semiring A] [Star A] [Algebra ℝ A] :
    IsEntangled (A := A) := by
  exact isEntangled_of_entropy (A := A) entropyReadout_of_twoStateRT
    entropyReadout_of_twoStateRT_eq_ln2

/-- Lemma 2: an explicit negativity property proves entanglement. -/
theorem isEntangled_of_negativity
    {A : Type*} [Semiring A] [Star A] [Algebra ℝ A]
    (R : ResidualCovariance A) (a b : A)
    (ha : a ∈ R.bipartite.A_L) (hb : b ∈ R.bipartite.A_R)
    (h : R.corrD0 a b ≠ 0) :
    IsEntangled A := by
  exact Or.inr (Or.inl ⟨R, a, b, ha, hb, h⟩)

/-- Lemma 3: an explicit Gaussian bosonic property proves entanglement. -/
theorem isEntangled_of_gaussianBosonic
    {A : Type*} [Semiring A] [Star A] [Algebra ℝ A]
    {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    (W : WeylFiveGradePhysicalReadoutBridge.WeylFockPhysicalReadoutCarrier (E := E)) :
    IsEntangled A := by
  exact Or.inr (Or.inr (Or.inl ⟨E, inferInstance, inferInstance, inferInstance, ⟨W⟩⟩))

/-- The bosonic Gaussian property exposes a normalized CAR pair. -/
theorem gaussianBosonic_car_is_normalized
    {A : Type*} [Semiring A] [Star A] [Algebra ℝ A]
    {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    (W : WeylFiveGradePhysicalReadoutBridge.WeylFockPhysicalReadoutCarrier (E := E)) :
    InfoGeometry.Canonical.BogoliubovFockSuper.IsCARPair
      (E := E) W.car.normalizedAnnihilation W.car.normalizedCreation :=
  W.car_is_normalized

/-- The bosonic Gaussian property also exposes the normalized CCR pair. -/
theorem gaussianBosonic_ccr_is_normalized
    {A : Type*} [Semiring A] [Star A] [Algebra ℝ A]
    {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    (W : WeylFiveGradePhysicalReadoutBridge.WeylFockPhysicalReadoutCarrier (E := E)) :
    InfoGeometry.Canonical.IsCCRPair
      (E := E) W.ccr.normalizedAnnihilation W.ccr.normalizedCreation :=
  W.ccr_is_normalized

/-- Lemma 4: an explicit Gaussian fermionic property proves entanglement. -/
theorem isEntangled_of_gaussianFermionic
    {A : Type*} [Semiring A] [Star A] [Algebra ℝ A]
    {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    (W : InfoGeometry.Canonical.ScaledCARPair E) :
    IsEntangled A := by
  exact Or.inr (Or.inr (Or.inr ⟨E, inferInstance, inferInstance, inferInstance, ⟨W⟩⟩))

/-- The fermionic Gaussian property exposes a normalized CAR pair. -/
theorem gaussianFermionic_car_is_normalized
    {A : Type*} [Semiring A] [Star A] [Algebra ℝ A]
    {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    (W : InfoGeometry.Canonical.ScaledCARPair E) :
    InfoGeometry.Canonical.BogoliubovFockSuper.IsCARPair
      (E := E) W.normalizedAnnihilation W.normalizedCreation :=
  W.normalized_isCARPair

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

/-- Lorentzian lightcone property: null rays need a dedicated Dirac property. -/
@[rep_depth transport]
structure LightconeReadoutBoundary
    (V : Type*) [AddCommGroup V] [Module ℝ V]
    (Q : QuadraticForm ℝ V) where
  dirac : V →ₗ[ℝ] V
  diracSquare : dirac.comp dirac = 0
  kernelVector : V
  kernelNontrivial : dirac kernelVector = 0 ∧ kernelVector ≠ 0
  nullConeCertified : Q kernelVector = 0
  projectiveRay : Projectivization ℝ V
  projectivizationWitness :
    projectiveRay = Projectivization.mk ℝ kernelVector kernelNontrivial.2

/-- A lightcone boundary property exposes its Dirac-square side condition. -/
theorem lightconeReadoutBoundary_diracSquare
    {V : Type*} [AddCommGroup V] [Module ℝ V]
    {Q : QuadraticForm ℝ V} (W : LightconeReadoutBoundary V Q) :
    W.dirac.comp W.dirac = 0 :=
  W.diracSquare

/-- A lightcone boundary property exposes kernel nontriviality. -/
theorem lightconeReadoutBoundary_kernelNontrivial
    {V : Type*} [AddCommGroup V] [Module ℝ V]
    {Q : QuadraticForm ℝ V} (W : LightconeReadoutBoundary V Q) :
    W.dirac W.kernelVector = 0 ∧ W.kernelVector ≠ 0 :=
  W.kernelNontrivial

/-- A lightcone boundary property exposes null-cone certification. -/
theorem lightconeReadoutBoundary_nullConeCertified
    {V : Type*} [AddCommGroup V] [Module ℝ V]
    {Q : QuadraticForm ℝ V} (W : LightconeReadoutBoundary V Q) :
    Q W.kernelVector = 0 :=
  W.nullConeCertified

/-- A lightcone boundary property exposes the projectivization property. -/
theorem lightconeReadoutBoundary_projectivization
    {V : Type*} [AddCommGroup V] [Module ℝ V]
    {Q : QuadraticForm ℝ V} (W : LightconeReadoutBoundary V Q) :
    W.projectiveRay = Projectivization.mk ℝ W.kernelVector W.kernelNontrivial.2 :=
  W.projectivizationWitness

theorem nonfactorizing_covariance_is_not_entanglement
    {A : Type*} [Semiring A] [Star A] [Algebra ℝ A]
    (R : ResidualCovariance A)
    {a : A} (ha : a ∈ R.bipartite.A_L) {b : A} (hb : b ∈ R.bipartite.A_R)
    (h : R.corrD0 a b ≠ 0) :
    ¬ Factorizes R.ω₀ R.bipartite.A_L R.bipartite.A_R :=
  corr_nonzero_implies_not_factorize (R := R) (a := a) (b := b) ha hb h

end InfoGeometry.Canonical.EntanglementResidualOwner
