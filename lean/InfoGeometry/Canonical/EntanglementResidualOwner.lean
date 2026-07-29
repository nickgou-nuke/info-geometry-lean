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

/-- The mismatch transports covariantly; zero requires an additional agreement witness. -/
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

/-- Positive compression witness for a projector/compression sector. -/
@[rep_depth transport]
structure PositiveCompressionWitness (A : Type*) [Semiring A] [Star A] [Algebra ℝ A] where
  projector : A
  projector_idem : projector * projector = projector
  projector_selfAdj_G : IsSelfAdjoint projector
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
  /-- The null projector annihilates every observable after compression. -/
  algebraicNull : ∀ a : R, nullProjector * a * nullProjector = 0
  /-- The physical null sector is represented by left annihilation. -/
  physicalNull : ∀ a : R, nullProjector * a = 0
  /-- Left annihilation implies the compressed algebraic null law. -/
  physicalWitness : ∀ a : R, (nullProjector * a = 0) →
    (nullProjector * a * nullProjector = 0)

theorem DrazinNullSector.nullProjector_idempotent
    {R : Type*} [Ring R] (W : DrazinNullSector R) :
    W.nullProjector * W.nullProjector = W.nullProjector := by
  rw [W.nullProjector_eq]
  exact W.pair.PD_idempotent

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
  compression : PositiveCompressionWitness A
  bipartite : BipartiteStateData A
  ω₀ : A → ℝ
  ω₀_def : ∀ a, ω₀ a = compression.compressedState a
  corrD0 : A → A → ℝ
  corrD0_def : ∀ a b, corrD0 a b = ω₀ (a * b) - ω₀ a * ω₀ b

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

/-- Compatibility surface retained for the v2 owner-map tests: a Drazin-null
covariance is residual covariance plus a nonzero covariance certificate.  It is
not the entanglement itself. -/
@[rep_depth transport]
structure DrazinNullCovariance (A : Type*) [Semiring A] [Star A] [Algebra ℝ A] where
  residual : ResidualCovariance A
  leftObservable : A
  rightObservable : A
  left_mem : leftObservable ∈ residual.bipartite.A_L
  right_mem : rightObservable ∈ residual.bipartite.A_R
  nonfactorizingCovariance : residual.corrD0 leftObservable rightObservable ≠ 0

/-- Nonzero residual covariance is a Drazin-null-supported nonproduct
correlation; it is not an automatic entanglement theorem. -/
theorem nonfactorizingCovariance_implies_drazinNullSupportedCorrelation
    {A : Type*} [Semiring A] [Star A] [Algebra ℝ A]
    (C : DrazinNullCovariance A) :
    ¬ Factorizes C.residual.ω₀ C.residual.bipartite.A_L C.residual.bipartite.A_R :=
  corr_nonzero_implies_not_factorize (R := C.residual)
    (a := C.leftObservable) (b := C.rightObservable)
    C.left_mem C.right_mem C.nonfactorizingCovariance

/-- Entropy witness: the existing two-state RT owner theorem gives a concrete
entropy readout. -/
@[rep_depth transport]
structure EntropyWitness where
  entropyReadout : ℝ
  entropy_eq_ln2 : entropyReadout = Real.log 2

/-- A concrete entropy witness from the owner RT theorem. -/
noncomputable def entropyWitness_of_twoStateRT : EntropyWitness := by
  refine ⟨InfoGeometry.Holography.RyuTakayanagiEmergence.vonNeumannEntropy (1 / 2 : ℝ), ?_⟩
  simpa using InfoGeometry.Holography.RyuTakayanagiEmergence.maxEntropy_twoState

/-- The entropy witness readout is pinned to `log 2`. -/
theorem entropyWitness_readout_eq_ln2 (W : EntropyWitness) :
    W.entropyReadout = Real.log 2 :=
  W.entropy_eq_ln2

/-- The two-state RT witness carries the `log 2` readout explicitly. -/
theorem entropyWitness_of_twoStateRT_readout_eq_ln2 :
    (entropyWitness_of_twoStateRT).entropyReadout = Real.log 2 :=
  (entropyWitness_of_twoStateRT).entropy_eq_ln2

/-- Negativity witness: a residual covariance packet plus a certified nonzero
covariance readout. -/
@[rep_depth transport]
structure NegativityWitness (A : Type*) [Semiring A] [Star A] [Algebra ℝ A] where
  residual : DrazinNullCovariance A
  covarianceNonzero :
    residual.residual.corrD0 residual.leftObservable residual.rightObservable ≠ 0

/-- A concrete negativity witness comes directly from any supplied Drazin-null
supported covariance packet. -/
def negativityWitness_of_drazinNullCovariance
    {A : Type*} [Semiring A] [Star A] [Algebra ℝ A]
    (C : DrazinNullCovariance A) :
    NegativityWitness A := by
  refine ⟨C, ?_⟩
  exact C.nonfactorizingCovariance

/-- A negativity witness exposes an explicit nonzero covariance readout. -/
theorem negativityWitness_covarianceNonzero
    {A : Type*} [Semiring A] [Star A] [Algebra ℝ A]
    (W : NegativityWitness A) :
    W.residual.residual.corrD0 W.residual.leftObservable W.residual.rightObservable ≠ 0 :=
  W.covarianceNonzero

/-- A negativity witness directly blocks factorization. -/
theorem negativityWitness_blocks_factorization
    {A : Type*} [Semiring A] [Star A] [Algebra ℝ A]
    (W : NegativityWitness A) :
    ¬ Factorizes W.residual.residual.ω₀ W.residual.residual.bipartite.A_L
        W.residual.residual.bipartite.A_R :=
  nonfactorizingCovariance_implies_drazinNullSupportedCorrelation
    (A := A) W.residual

/-- The positive-compression witness exposes the idempotent projector law. -/
theorem positiveCompressionWitness_projector_idem
    {A : Type*} [Semiring A] [Star A] [Algebra ℝ A]
    (W : PositiveCompressionWitness A) :
    W.projector * W.projector = W.projector :=
  W.projector_idem

/-- The positive-compression witness exposes the self-adjoint projector side-condition. -/
def positiveCompressionWitness_projector_selfAdj_G
    {A : Type*} [Semiring A] [Star A] [Algebra ℝ A]
    (W : PositiveCompressionWitness A) : IsSelfAdjoint W.projector :=
  W.projector_selfAdj_G

/-- The compression formula on the projector itself unfolds to the compressed
state at the idempotent projector. -/
theorem positiveCompressionWitness_compression_on_projector
    {A : Type*} [Semiring A] [Star A] [Algebra ℝ A]
    (W : PositiveCompressionWitness A) :
    W.compressedState W.projector =
      W.state (W.projector * W.projector) / W.state W.projector := by
  rw [W.compression_eq]
  have hnum :
      W.projector * W.projector * W.projector =
        W.projector * W.projector :=
    congrArg (fun x => x * W.projector) W.projector_idem
  rw [hnum]

/-- The Drazin-null sector exposes its physical-null certificate. -/
def drazinNullSector_physicalNull
    (W : DrazinNullSector R) (a : R) : W.nullProjector * a = 0 :=
  W.physicalNull a

/-- The Drazin-null sector exposes the implication from physical nullity to algebraic nullity. -/
theorem drazinNullSector_physicalWitness
    (W : DrazinNullSector R) :
    ∀ a : R, (W.nullProjector * a = 0) →
      (W.nullProjector * a * W.nullProjector = 0) :=
  W.physicalWitness

/-! The concrete normalized CAR/CCR readout is already the owner carrier. -/
@[rep_depth transport]
abbrev GaussianBosonicWitness
    (E : Type) [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E] :=
  WeylFiveGradePhysicalReadoutBridge.WeylFockPhysicalReadoutCarrier (E := E)

namespace GaussianBosonicWitness

abbrev readout
    {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    (W : GaussianBosonicWitness E) :
    WeylFiveGradePhysicalReadoutBridge.WeylFockPhysicalReadoutCarrier (E := E) :=
  W

end GaussianBosonicWitness

/-! The concrete normalized CAR readout is already the owner carrier. -/
@[rep_depth transport]
abbrev GaussianFermionicWitness
    (E : Type) [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E] :=
  WeylFiveGradePhysicalReadoutBridge.WeylCARPhysicalReadoutCarrier (E := E)

namespace GaussianFermionicWitness

abbrev readout
    {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    (W : GaussianFermionicWitness E) :
    WeylFiveGradePhysicalReadoutBridge.WeylCARPhysicalReadoutCarrier (E := E) :=
  W

end GaussianFermionicWitness

/-- Entanglement witness assembled from one of the concrete witness lanes. -/
@[rep_depth transport]
inductive EntanglementWitness (A : Type*) [Semiring A] [Star A] [Algebra ℝ A] where
  | entropy : EntropyWitness → EntanglementWitness A
  | negativity : NegativityWitness A → EntanglementWitness A
  | gaussianBosonic
      {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E] :
      GaussianBosonicWitness E → EntanglementWitness A
  | gaussianFermionic
      {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E] :
      GaussianFermionicWitness E → EntanglementWitness A

/-!
An explicit entanglement criterion is already represented by the inductive
`EntanglementWitness` owner. Keep the compatibility name as a type alias
instead of introducing a one-field wrapper.
-/
abbrev EntanglementCriterionWitness (A : Type*) [Semiring A] [Star A] [Algebra ℝ A] :=
  EntanglementWitness A

/-- Entanglement is represented by the existence of an explicit witness. -/
def IsEntangled (A : Type*) [Semiring A] [Star A] [Algebra ℝ A] : Prop :=
  Nonempty (EntanglementWitness A)

/-- An entanglement witness certifies entanglement. -/
theorem entanglementWitness_implies_entangled
    {A : Type*} [Semiring A] [Star A] [Algebra ℝ A]
    (W : EntanglementWitness A) :
    IsEntangled A := by
  exact ⟨W⟩

/-- Lemma 1: an explicit entropy witness proves entanglement. -/
theorem isEntangled_of_entropy
    {A : Type*} [Semiring A] [Star A] [Algebra ℝ A]
    (W : EntropyWitness) :
    IsEntangled A := by
  exact ⟨EntanglementWitness.entropy W⟩

/-- The two-state RT entropy witness directly certifies entanglement. -/
theorem isEntangled_of_twoStateRT
    {A : Type*} [Semiring A] [Star A] [Algebra ℝ A] :
    IsEntangled (A := A) := by
  exact isEntangled_of_entropy (A := A) entropyWitness_of_twoStateRT

/-- Lemma 2: an explicit negativity witness proves entanglement. -/
theorem isEntangled_of_negativity
    {A : Type*} [Semiring A] [Star A] [Algebra ℝ A]
    (W : NegativityWitness A) :
    IsEntangled A := by
  exact ⟨EntanglementWitness.negativity W⟩

/-- Lemma 3: an explicit Gaussian bosonic witness proves entanglement. -/
theorem isEntangled_of_gaussianBosonic
    {A : Type*} [Semiring A] [Star A] [Algebra ℝ A]
    {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    (W : GaussianBosonicWitness E) :
    IsEntangled A := by
  exact ⟨EntanglementWitness.gaussianBosonic W⟩

/-- The bosonic Gaussian witness exposes a normalized CAR pair. -/
theorem gaussianBosonicWitness_car_is_normalized
    {A : Type*} [Semiring A] [Star A] [Algebra ℝ A]
    {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    (W : GaussianBosonicWitness E) :
    InfoGeometry.Canonical.BogoliubovFockSuper.IsCARPair
      (E := E) W.readout.car.normalizedAnnihilation W.readout.car.normalizedCreation :=
  W.readout.car_is_normalized

/-- The bosonic Gaussian witness also exposes the normalized CCR pair. -/
theorem gaussianBosonicWitness_ccr_is_normalized
    {A : Type*} [Semiring A] [Star A] [Algebra ℝ A]
    {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    (W : GaussianBosonicWitness E) :
    InfoGeometry.Canonical.IsCCRPair
      (E := E) W.readout.ccr.normalizedAnnihilation W.readout.ccr.normalizedCreation :=
  W.readout.ccr_is_normalized

/-- Lemma 4: an explicit Gaussian fermionic witness proves entanglement. -/
theorem isEntangled_of_gaussianFermionic
    {A : Type*} [Semiring A] [Star A] [Algebra ℝ A]
    {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    (W : GaussianFermionicWitness E) :
    IsEntangled A := by
  exact ⟨EntanglementWitness.gaussianFermionic W⟩

/-- The fermionic Gaussian witness exposes a normalized CAR pair. -/
theorem gaussianFermionicWitness_car_is_normalized
    {A : Type*} [Semiring A] [Star A] [Algebra ℝ A]
    {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    (W : GaussianFermionicWitness E) :
    InfoGeometry.Canonical.BogoliubovFockSuper.IsCARPair
      (E := E) W.readout.car.normalizedAnnihilation W.readout.car.normalizedCreation :=
  W.readout.car_is_normalized

/-- Lemma 5: any witness inhabits the entangled predicate. -/
theorem isEntangled_of_entanglementWitness
    {A : Type*} [Semiring A] [Star A] [Algebra ℝ A]
    (W : EntanglementWitness A) :
    IsEntangled A := by
  exact ⟨W⟩

/-- Theorem: any one explicit criterion proves entanglement. -/
theorem isEntangled_of_any_explicit_criterion
    {A : Type*} [Semiring A] [Star A] [Algebra ℝ A]
    (W : EntanglementCriterionWitness A) :
    IsEntangled A :=
  entanglementWitness_implies_entangled W

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

theorem entanglement_claim_from_witness
    {A : Type*} [Semiring A] [Star A] [Algebra ℝ A]
    (W : EntanglementWitness (A := A)) :
    IsEntangled (A := A) :=
  entanglementWitness_implies_entangled (A := A) W

/-- A lightcone boundary witness exposes its Dirac-square side condition. -/
def lightconeReadoutBoundary_diracSquare
    {V : Type*} [AddCommGroup V] [Module ℝ V]
    {Q : QuadraticForm ℝ V} (W : LightconeReadoutBoundary V Q) :
    W.dirac.comp W.dirac = 0 :=
  W.diracSquare

/-- A lightcone boundary witness exposes kernel nontriviality. -/
def lightconeReadoutBoundary_kernelNontrivial
    {V : Type*} [AddCommGroup V] [Module ℝ V]
    {Q : QuadraticForm ℝ V} (W : LightconeReadoutBoundary V Q) :
    W.dirac W.kernelVector = 0 ∧ W.kernelVector ≠ 0 :=
  W.kernelNontrivial

/-- A lightcone boundary witness exposes null-cone certification. -/
def lightconeReadoutBoundary_nullConeCertified
    {V : Type*} [AddCommGroup V] [Module ℝ V]
    {Q : QuadraticForm ℝ V} (W : LightconeReadoutBoundary V Q) :
    Q W.kernelVector = 0 :=
  W.nullConeCertified

/-- A lightcone boundary witness exposes the projectivization witness. -/
def lightconeReadoutBoundary_projectivizationWitness
    {V : Type*} [AddCommGroup V] [Module ℝ V]
    {Q : QuadraticForm ℝ V} (W : LightconeReadoutBoundary V Q) :
    W.projectiveRay = Projectivization.mk ℝ W.kernelVector W.kernelNontrivial.2 :=
  W.projectivizationWitness

/-- The full lightcone boundary packet can be read back as a conjunction of
its four supplied boundary conditions. -/
def lightconeReadoutBoundary_packet
    {V : Type*} [AddCommGroup V] [Module ℝ V]
  {Q : QuadraticForm ℝ V} (W : LightconeReadoutBoundary V Q) : Prop :=
  (W.dirac.comp W.dirac = 0) ∧
    (W.dirac W.kernelVector = 0 ∧ W.kernelVector ≠ 0) ∧
    (Q W.kernelVector = 0) ∧
    (W.projectiveRay = Projectivization.mk ℝ W.kernelVector W.kernelNontrivial.2)

theorem nonfactorizing_covariance_is_not_entanglement
    {A : Type*} [Semiring A] [Star A] [Algebra ℝ A]
    (R : ResidualCovariance A)
    {a : A} (ha : a ∈ R.bipartite.A_L) {b : A} (hb : b ∈ R.bipartite.A_R)
    (h : R.corrD0 a b ≠ 0) :
    ¬ Factorizes R.ω₀ R.bipartite.A_L R.bipartite.A_R :=
  corr_nonzero_implies_not_factorize (R := R) (a := a) (b := b) ha hb h

end InfoGeometry.Canonical.EntanglementResidualOwner
