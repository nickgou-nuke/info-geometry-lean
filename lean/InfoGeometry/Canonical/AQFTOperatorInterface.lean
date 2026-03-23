import InfoGeometry.Canonical.QFTTDFTLaunchpad
import InfoGeometry.Canonical.IBCore
import Mathlib.Analysis.CStarAlgebra.Basic
import Mathlib.Analysis.CStarAlgebra.ContinuousLinearMap
import Mathlib.Analysis.InnerProductSpace.Adjoint

/-!
# InfoGeometry.Canonical.AQFTOperatorInterface

AQFT operator-algebra preparation layer:

- abstract C*-ready / complete-C*-ready signatures
- concrete finite-model interpretation/compression maps over existing `AlgebraEnd` infrastructure
- packaging theorems pairing readiness certificates with already-proved concrete AQFT statements
-/

namespace InfoGeometry.Canonical.AQFTOperatorInterface

open InfoGeometry.Krein
open InfoGeometry.Canonical.KMSSinkhornBridge
open InfoGeometry.Canonical.IB
open InfoGeometry.Canonical.MoE
open InfoGeometry.Canonical.QFTTDFTLaunchpad
open InfoGeometry.Canonical.BogoliubovFockSuper
open InfoGeometry.Canonical.RicciMongeAmpere

section AbstractSignatures

variable (Obs : Type*)
variable [NonUnitalNormedRing Obs] [StarRing Obs]

/-- Abstract C*-ready AQFT operator-algebra signature. -/
abbrev IsCStarReady : Prop := CStarRing Obs

/--
Abstract complete-C*-ready AQFT signature used in this library:
this is only `CStarRing` plus completeness, not a von Neumann notion.
-/
abbrev IsCompleteCStarReady : Prop :=
  IsCStarReady Obs ∧ CompleteSpace Obs

end AbstractSignatures

section Realizations

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]
variable {Obs : Type*} [NonUnitalNormedRing Obs] [StarRing Obs]

/--
Explicit interpretation map from the concrete finite doubled-space operator model
into an abstract operator target.
No algebraic or star-preserving properties are imposed here.
-/
structure AQFTOperatorInterpretation
    (F : Type*) [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F] where
  interpret : AlgebraEnd F → Obs

/-- Theorem `cstarReady_of_instance`. -/
theorem cstarReady_of_instance
    [CStarRing Obs] :
    IsCStarReady (Obs := Obs) := by
  infer_instance

/-- Theorem `completeCStarReady_of_instance`. -/
theorem completeCStarReady_of_instance
    [CStarRing Obs] [CompleteSpace Obs] :
    IsCompleteCStarReady (Obs := Obs) := by
  exact ⟨cstarReady_of_instance (Obs := Obs), inferInstance⟩

end Realizations

section ConcreteHilbertModels

/-! ### Real Hilbert model (instantiates the AQFT interface directly) -/

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/-- Real Hilbert bounded-operator algebra (adjoint/star model). -/
abbrev RealHilbertObs
    (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E] :=
  E →L[ℝ] E

/-- First-leg embedding `x ↦ (x,0)` into doubled space. -/
def firstLegEmbedding : E →L[ℝ] InfoGeometry.Krein.DoubledSpace E where
  toLinearMap :=
    { toFun := fun x => InfoGeometry.Krein.to_doubled x (0 : E)
      map_add' := by
        intro x y
        apply (WithLp.ofLp_injective 2)
        simp [InfoGeometry.Krein.to_doubled]
      map_smul' := by
        intro a x
        apply (WithLp.ofLp_injective 2)
        simp [InfoGeometry.Krein.to_doubled, smul_zero] }
  cont := by
    simpa [InfoGeometry.Krein.to_doubled] using
      (WithLp.prod_continuous_toLp (p := 2) (α := E) (β := E)).comp
        (continuous_id.prodMk (continuous_const (y := (0 : E))))

/-- First-leg projection `(x,y) ↦ x` from doubled space. -/
def firstLegProjection : InfoGeometry.Krein.DoubledSpace E →L[ℝ] E where
  toLinearMap :=
    { toFun := fun v => WithLp.fst v
      map_add' := by
        intro v w
        simp [WithLp.add_fst]
      map_smul' := by
        intro a v
        simp [WithLp.smul_fst] }
  cont := by
    simpa using
      WithLp.continuous_fst (p := 2) (α := E) (β := E)

/-- Compression of doubled operators onto the first Hilbert leg. -/
def firstLegCompression (A : AlgebraEnd E) : RealHilbertObs E :=
  (firstLegProjection (E := E)).comp (A.comp (firstLegEmbedding (E := E)))

/-- Concrete interpretation into real Hilbert bounded operators via first-leg compression. -/
def realHilbertCompressionInterpretation :
    AQFTOperatorInterpretation E (Obs := RealHilbertObs E) where
  interpret := firstLegCompression (E := E)

/-- Theorem `realHilbertOp_cstarReady`. -/
theorem realHilbertOp_cstarReady :
    IsCStarReady (Obs := RealHilbertObs E) := by
  infer_instance

/-- Theorem `realHilbertOp_completeCStarReady`. -/
theorem realHilbertOp_completeCStarReady :
    IsCompleteCStarReady (Obs := RealHilbertObs E) := by
  exact ⟨realHilbertOp_cstarReady (E := E), inferInstance⟩

/--
Package the concrete real-Hilbert compression interpretation with the complete
C*-readiness of its target.
-/
theorem realHilbertCompressionInterpretation_packaged_with_completeCStarReady :
    Nonempty (AQFTOperatorInterpretation E (Obs := RealHilbertObs E))
      ∧ IsCompleteCStarReady (Obs := RealHilbertObs E) := by
  exact ⟨⟨realHilbertCompressionInterpretation (E := E)⟩,
    realHilbertOp_completeCStarReady (E := E)⟩

/-! ### Complex Hilbert model (adjoint/star bounded operators) -/

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- Complex doubled operator source type (complex-linear counterpart). -/
abbrev ComplexHilbertOp
    (H : Type*) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] :=
  InfoGeometry.Krein.DoubledSpace H →L[ℂ] InfoGeometry.Krein.DoubledSpace H

/-- Complex Hilbert bounded-operator algebra (adjoint/star model). -/
abbrev ComplexHilbertObs
    (H : Type*) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] :=
  H →L[ℂ] H

/-- Complex first-leg embedding `x ↦ (x,0)` into doubled space. -/
def complexFirstLegEmbedding : H →L[ℂ] InfoGeometry.Krein.DoubledSpace H where
  toLinearMap :=
    { toFun := fun x => InfoGeometry.Krein.to_doubled x (0 : H)
      map_add' := by
        intro x y
        apply (WithLp.ofLp_injective 2)
        simp [InfoGeometry.Krein.to_doubled]
      map_smul' := by
        intro a x
        apply (WithLp.ofLp_injective 2)
        simp [InfoGeometry.Krein.to_doubled, smul_zero] }
  cont := by
    simpa [InfoGeometry.Krein.to_doubled] using
      (WithLp.prod_continuous_toLp (p := 2) (α := H) (β := H)).comp
        (continuous_id.prodMk (continuous_const (y := (0 : H))))

/-- Complex first-leg projection `(x,y) ↦ x` from doubled space. -/
def complexFirstLegProjection : InfoGeometry.Krein.DoubledSpace H →L[ℂ] H where
  toLinearMap :=
    { toFun := fun v => WithLp.fst v
      map_add' := by
        intro v w
        simp [WithLp.add_fst]
      map_smul' := by
        intro a v
        simp [WithLp.smul_fst] }
  cont := by
    simpa using
      WithLp.continuous_fst (p := 2) (α := H) (β := H)

/-- Complex compression of doubled operators onto the first Hilbert leg. -/
def complexFirstLegCompression (A : ComplexHilbertOp H) : ComplexHilbertObs H :=
  (complexFirstLegProjection (H := H)).comp (A.comp (complexFirstLegEmbedding (H := H)))

/-- Complex-operator interpretation wrapper (complex-source counterpart). -/
structure ComplexAQFTOperatorInterpretation
    (Obs : Type*) [NonUnitalNormedRing Obs] [StarRing Obs] where
  interpret : ComplexHilbertOp H → Obs

/-- Complex interpretation into Hilbert bounded operators via first-leg compression. -/
def complexHilbertCompressionInterpretation :
    ComplexAQFTOperatorInterpretation (H := H) (Obs := ComplexHilbertObs H) where
  interpret := complexFirstLegCompression (H := H)

/-- Theorem `complexHilbertOp_cstarReady`. -/
theorem complexHilbertOp_cstarReady :
    IsCStarReady (Obs := ComplexHilbertObs H) := by
  infer_instance

/-- Theorem `complexHilbertOp_completeCStarReady`. -/
theorem complexHilbertOp_completeCStarReady :
    IsCompleteCStarReady (Obs := ComplexHilbertObs H) := by
  exact ⟨complexHilbertOp_cstarReady (H := H), inferInstance⟩

/--
Package the concrete complex-Hilbert compression interpretation with the
complete C*-readiness of its target.
-/
theorem complexHilbertCompressionInterpretation_packaged_with_completeCStarReady :
    Nonempty (ComplexAQFTOperatorInterpretation (H := H) (Obs := ComplexHilbertObs H))
      ∧ IsCompleteCStarReady (Obs := ComplexHilbertObs H) := by
  exact ⟨⟨complexHilbertCompressionInterpretation (H := H)⟩,
    complexHilbertOp_completeCStarReady (H := H)⟩

end ConcreteHilbertModels

section KMSInterface

variable (n : Nat)
variable {F : Type} [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]
variable {Obs : Type*} [NonUnitalNormedRing Obs] [StarRing Obs] [CStarRing Obs]

/--
Packaging theorem:
pair C*-readiness of the target with the already-proved concrete Sinkhorn-to-KMS
closure theorem.
-/
theorem sinkhorn_kmsClosure_packaged_with_cstarReady
    (T : SinkhornTrajectory n)
    (K : AlgebraEnd F)
    (ω : Nat → AlgebraEnd F →L[ℝ] ℝ)
    (β : ℝ)
    (hClosure : SinkhornKMSClosure n T K ω β) :
    IsCStarReady (Obs := Obs) ∧ SinkhornKMSClosure n T K ω β := by
  refine ⟨cstarReady_of_instance (Obs := Obs), ?_⟩
  exact hClosure

end KMSInterface

section FockInterface

variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
variable {Obs : Type*} [NonUnitalNormedRing Obs] [StarRing Obs] [CStarRing Obs] [CompleteSpace Obs]

/--
Packaging theorem:
pair complete-C*-readiness of the target with the already-proved concrete
vacuum-transported grand-canonical Euler collapse.
-/
theorem grandCanonicalFockEulerStep_packaged_with_completeCStarReady
    (η : ℝ)
    (B : BogoliubovMixingParams)
    (H : FockEndomorphism E)
    (R : RicciTensor E)
    (Kgeo : InfoGeometry.Canonical.KaehlerGeometry.KaehlerInformationGeometry E)
    (x : E)
    (scalar Λ : ℝ)
    (V : SplitVielbein Kgeo x)
    (Γ : SpinConnection Kgeo x V)
    (ψ : InfoGeometry.Krein.DoubledSpace E)
    (hVacSplit : VacuumEinsteinOnTransportedSplit R Kgeo x scalar Λ V Γ) :
    IsCompleteCStarReady (Obs := Obs)
      ∧ grandCanonicalFockEulerStep (E := E) η B H
          (einsteinInducedChemicalPotential (R := R) (K := Kgeo) (x := x)
            (scalar := scalar) (Λ := Λ) (V := V) (Γ := Γ)) ψ
            = ψ + η • H ψ := by
  refine ⟨completeCStarReady_of_instance (Obs := Obs), ?_⟩
  exact grandCanonicalFockEulerStep_eq_hamiltonianStep_of_vacuumTransported
    (E := E) (η := η) (B := B) (H := H)
    (R := R) (Kgeo := Kgeo) (x := x) (scalar := scalar) (Λ := Λ)
    (V := V) (Γ := Γ) (ψ := ψ) hVacSplit

/--
Packaging theorem:
pair complete-C*-readiness of the target with the already-proved Bogoliubov
projector superalgebra and the vacuum-transported grand-canonical Euler
collapse.
-/
theorem grandCanonicalFockEulerStep_and_bogoliubov_projector_superalgebra_packaged_with_completeCStarReady
    (η : ℝ)
    (B : BogoliubovMixingParams)
    (H : FockEndomorphism E)
    (R : RicciTensor E)
    (Kgeo : InfoGeometry.Canonical.KaehlerGeometry.KaehlerInformationGeometry E)
    (x : E)
    (scalar Λ : ℝ)
    (V : SplitVielbein Kgeo x)
    (Γ : SpinConnection Kgeo x V)
    (ψ : InfoGeometry.Krein.DoubledSpace E)
    (hVacSplit : VacuumEinsteinOnTransportedSplit R Kgeo x scalar Λ V Γ) :
    IsCompleteCStarReady (Obs := Obs)
      ∧ fockAnticommutator (E := E)
          (bogoliubovAnnihilation (E := E) B)
          (bogoliubovCreation (E := E) B)
          = (B.u * (B.v * 2) : ℝ) • ContinuousLinearMap.id ℝ (DoubledSpace E)
      ∧ fockCommutator (E := E)
          (bogoliubovAnnihilation (E := E) B)
          (bogoliubovCreation (E := E) B) = 0
      ∧ grandCanonicalFockEulerStep (E := E) η B H
          (einsteinInducedChemicalPotential (R := R) (K := Kgeo) (x := x)
            (scalar := scalar) (Λ := Λ) (V := V) (Γ := Γ)) ψ
            = ψ + η • H ψ := by
  refine ⟨completeCStarReady_of_instance (Obs := Obs), ?_, ?_, ?_⟩
  · exact (bogoliubov_projector_superalgebra (E := E) B).1
  · exact (bogoliubov_projector_superalgebra (E := E) B).2
  · exact grandCanonicalFockEulerStep_eq_hamiltonianStep_of_vacuumTransported
      (E := E) (η := η) (B := B) (H := H)
      (R := R) (Kgeo := Kgeo) (x := x) (scalar := scalar) (Λ := Λ)
      (V := V) (Γ := Γ) (ψ := ψ) hVacSplit

end FockInterface

section UnifiedInterface

variable (n : Nat)
variable {F : Type} [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]
variable {ObsKMS : Type*} [NonUnitalNormedRing ObsKMS] [StarRing ObsKMS] [CStarRing ObsKMS]
variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
variable {ObsFock : Type*} [NonUnitalNormedRing ObsFock] [StarRing ObsFock]
  [CStarRing ObsFock] [CompleteSpace ObsFock]

/--
Unified readiness package:
pair C*- / complete-C*-readiness certificates with the already-proved concrete
AQFT closure statements.
-/
theorem aqft_readiness_package
    (T : SinkhornTrajectory n)
    (K : AlgebraEnd F)
    (ω : Nat → AlgebraEnd F →L[ℝ] ℝ)
    (β : ℝ)
    (η : ℝ)
    (B : BogoliubovMixingParams)
    (H : FockEndomorphism E)
    (R : RicciTensor E)
    (Kgeo : InfoGeometry.Canonical.KaehlerGeometry.KaehlerInformationGeometry E)
    (x : E)
    (scalar Λ : ℝ)
    (V : SplitVielbein Kgeo x)
    (Γ : SpinConnection Kgeo x V)
    (ψ : InfoGeometry.Krein.DoubledSpace E)
    (hClosure : SinkhornKMSClosure n T K ω β)
    (hVacSplit : VacuumEinsteinOnTransportedSplit R Kgeo x scalar Λ V Γ) :
    IsCStarReady (Obs := ObsKMS)
      ∧ IsCompleteCStarReady (Obs := ObsFock)
      ∧ SinkhornKMSClosure n T K ω β
      ∧ grandCanonicalFockEulerStep (E := E) η B H
          (einsteinInducedChemicalPotential (R := R) (K := Kgeo) (x := x)
            (scalar := scalar) (Λ := Λ) (V := V) (Γ := Γ)) ψ
            = ψ + η • H ψ := by
  have hK :=
    sinkhorn_kmsClosure_packaged_with_cstarReady
      (n := n) (F := F) (Obs := ObsKMS)
      (T := T) (K := K) (ω := ω) (β := β) hClosure
  have hF :=
    grandCanonicalFockEulerStep_packaged_with_completeCStarReady
      (E := E) (Obs := ObsFock)
      (η := η) (B := B) (H := H)
      (R := R) (Kgeo := Kgeo) (x := x) (scalar := scalar) (Λ := Λ)
      (V := V) (Γ := Γ) (ψ := ψ) hVacSplit
  exact ⟨hK.1, hF.1, hK.2, hF.2⟩

/--
Canonical AQFT readiness endpoint carrying the doubled-projector super-pair
alongside the concrete AQFT closure statements.
-/
theorem aqft_readiness_package_with_projectorSuperPair_base
    (T : SinkhornTrajectory n)
    (K : AlgebraEnd F)
    (ω : Nat → AlgebraEnd F →L[ℝ] ℝ)
    (β : ℝ)
    (η : ℝ)
    (B : BogoliubovMixingParams)
    (H : FockEndomorphism E)
    (R : RicciTensor E)
    (Kgeo : InfoGeometry.Canonical.KaehlerGeometry.KaehlerInformationGeometry E)
    (x : E)
    (scalar Λ : ℝ)
    (V : SplitVielbein Kgeo x)
    (Γ : SpinConnection Kgeo x V)
    (ψ : InfoGeometry.Krein.DoubledSpace E)
    (hClosure : SinkhornKMSClosure n T K ω β)
    (hVacSplit : VacuumEinsteinOnTransportedSplit R Kgeo x scalar Λ V Γ) :
    IsCStarReady (Obs := ObsKMS)
      ∧ IsCompleteCStarReady (Obs := ObsFock)
      ∧ SinkhornKMSClosure n T K ω β
      ∧ IsProjectorSuperPair
          (InfoGeometry.Quantum.annihilationOp (E := E))
          (InfoGeometry.Quantum.creationOp (E := E))
      ∧ grandCanonicalFockEulerStep (E := E) η B H
          (einsteinInducedChemicalPotential (R := R) (K := Kgeo) (x := x)
            (scalar := scalar) (Λ := Λ) (V := V) (Γ := Γ)) ψ
            = ψ + η • H ψ := by
  refine ⟨?_, ?_, ?_, projectorSuperPair_base (E := E), ?_⟩
  · exact cstarReady_of_instance (Obs := ObsKMS)
  · exact completeCStarReady_of_instance (Obs := ObsFock)
  · exact hClosure
  · exact grandCanonicalFockEulerStep_eq_hamiltonianStep_of_vacuumTransported
      (E := E) (η := η) (B := B) (H := H)
      (R := R) (Kgeo := Kgeo) (x := x) (scalar := scalar) (Λ := Λ)
      (V := V) (Γ := Γ) (ψ := ψ) hVacSplit

end UnifiedInterface

section UnifiedLaunchpadInterface

variable (n : Nat)
variable {F : Type} [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]
variable {ObsKMS : Type*}
  [NonUnitalNormedRing ObsKMS] [StarRing ObsKMS] [CStarRing ObsKMS]
variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
variable {ObsFock : Type*} [NonUnitalNormedRing ObsFock] [StarRing ObsFock]
  [CStarRing ObsFock] [CompleteSpace ObsFock]
variable {Θ : Type*} [NormedAddCommGroup Θ] [NormedSpace ℝ Θ]

/--
Unified AQFT/TDFT launchpad packaged together with operator-target readiness.
-/
theorem aqft_tdft_constructive_launchpad_packaged_with_aqft_readiness
    (T : SinkhornTrajectory n)
    (K : AlgebraEnd F)
    (ω : Nat → AlgebraEnd F →L[ℝ] ℝ)
    (β : ℝ)
    (η : ℝ)
    (B : BogoliubovMixingParams)
    (H : FockEndomorphism E)
    (R : RicciTensor E)
    (Kgeo : InfoGeometry.Canonical.KaehlerGeometry.KaehlerInformationGeometry E)
    (x : E)
    (scalar Λ : ℝ)
    (V : SplitVielbein Kgeo x)
    (Γ : SpinConnection Kgeo x V)
    (ψ0 : InfoGeometry.Krein.DoubledSpace E)
    (ψ : Θ → ℝ)
    (ψStar : (Θ →L[ℝ] ℝ) → ℝ)
    (flow : InfoGeometry.Canonical.RGFlow.InformationFlow E)
    (scale0 : ℝ)
    (hClosure : SinkhornKMSClosure n T K ω β)
    (hVacSplit : VacuumEinsteinOnTransportedSplit R Kgeo x scalar Λ V Γ)
    (hHK : HohenbergKohnDualState ψ ψStar)
    (hStationary : InfoGeometry.Canonical.RGFlow.IsStationaryAtScale flow scale0) :
    IsCStarReady (Obs := ObsKMS)
      ∧ IsCompleteCStarReady (Obs := ObsFock)
      ∧ SinkhornKMSClosure n T K ω β
      ∧ grandCanonicalFockEulerStep (E := E) η B H
          (einsteinInducedChemicalPotential (R := R) (K := Kgeo) (x := x)
            (scalar := scalar) (Λ := Λ) (V := V) (Γ := Γ)) ψ0
            = ψ0 + η • H ψ0
      ∧ HohenbergKohnDualState ψ ψStar
      ∧ RungeGrossStationaryDualState flow scale0 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact cstarReady_of_instance (Obs := ObsKMS)
  · exact completeCStarReady_of_instance (Obs := ObsFock)
  · exact hClosure
  · exact grandCanonicalFockEulerStep_eq_hamiltonianStep_of_vacuumTransported
      (E := E) (η := η) (B := B) (H := H)
      (R := R) (Kgeo := Kgeo) (x := x) (scalar := scalar) (Λ := Λ)
      (V := V) (Γ := Γ) (ψ := ψ0) hVacSplit
  · exact hHK
  · exact rungeGrossStationaryDualState_of_stationaryAtScale
      (flow := flow) (scale0 := scale0) hStationary

/--
Unified AQFT/TDFT launchpad with Bogoliubov projector-superalgebra packaged
together with operator-target readiness.
-/
theorem aqft_tdft_constructive_launchpad_with_bogoliubov_projector_superalgebra_packaged_with_aqft_readiness
    (T : SinkhornTrajectory n)
    (K : AlgebraEnd F)
    (ω : Nat → AlgebraEnd F →L[ℝ] ℝ)
    (β : ℝ)
    (η : ℝ)
    (B : BogoliubovMixingParams)
    (H : FockEndomorphism E)
    (R : RicciTensor E)
    (Kgeo : InfoGeometry.Canonical.KaehlerGeometry.KaehlerInformationGeometry E)
    (x : E)
    (scalar Λ : ℝ)
    (V : SplitVielbein Kgeo x)
    (Γ : SpinConnection Kgeo x V)
    (ψ0 : InfoGeometry.Krein.DoubledSpace E)
    (ψ : Θ → ℝ)
    (ψStar : (Θ →L[ℝ] ℝ) → ℝ)
    (flow : InfoGeometry.Canonical.RGFlow.InformationFlow E)
    (scale0 : ℝ)
    (hClosure : SinkhornKMSClosure n T K ω β)
    (hVacSplit : VacuumEinsteinOnTransportedSplit R Kgeo x scalar Λ V Γ)
    (hHK : HohenbergKohnDualState ψ ψStar)
    (hStationary : InfoGeometry.Canonical.RGFlow.IsStationaryAtScale flow scale0) :
    IsCStarReady (Obs := ObsKMS)
      ∧ IsCompleteCStarReady (Obs := ObsFock)
      ∧ SinkhornKMSClosure n T K ω β
      ∧ fockAnticommutator (E := E)
          (bogoliubovAnnihilation (E := E) B)
          (bogoliubovCreation (E := E) B)
          = (B.u * (B.v * 2) : ℝ) • ContinuousLinearMap.id ℝ (DoubledSpace E)
      ∧ fockCommutator (E := E)
          (bogoliubovAnnihilation (E := E) B)
          (bogoliubovCreation (E := E) B) = 0
      ∧ grandCanonicalFockEulerStep (E := E) η B H
          (einsteinInducedChemicalPotential (R := R) (K := Kgeo) (x := x)
            (scalar := scalar) (Λ := Λ) (V := V) (Γ := Γ)) ψ0
            = ψ0 + η • H ψ0
      ∧ HohenbergKohnDualState ψ ψStar
      ∧ RungeGrossStationaryDualState flow scale0 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact cstarReady_of_instance (Obs := ObsKMS)
  · exact completeCStarReady_of_instance (Obs := ObsFock)
  · exact hClosure
  · exact (bogoliubov_projector_superalgebra (E := E) B).1
  · exact (bogoliubov_projector_superalgebra (E := E) B).2
  · exact grandCanonicalFockEulerStep_eq_hamiltonianStep_of_vacuumTransported
      (E := E) (η := η) (B := B) (H := H)
      (R := R) (Kgeo := Kgeo) (x := x) (scalar := scalar) (Λ := Λ)
      (V := V) (Γ := Γ) (ψ := ψ0) hVacSplit
  · exact hHK
  · exact rungeGrossStationaryDualState_of_stationaryAtScale
      (flow := flow) (scale0 := scale0) hStationary

/--
Unified AQFT/TDFT launchpad packaged together with operator readiness and the
canonical doubled-projector super-pair.
-/
theorem aqft_tdft_constructive_launchpad_packaged_with_aqft_readiness_and_projectorSuperPair_base
    (T : SinkhornTrajectory n)
    (K : AlgebraEnd F)
    (ω : Nat → AlgebraEnd F →L[ℝ] ℝ)
    (β : ℝ)
    (η : ℝ)
    (B : BogoliubovMixingParams)
    (H : FockEndomorphism E)
    (R : RicciTensor E)
    (Kgeo : InfoGeometry.Canonical.KaehlerGeometry.KaehlerInformationGeometry E)
    (x : E)
    (scalar Λ : ℝ)
    (V : SplitVielbein Kgeo x)
    (Γ : SpinConnection Kgeo x V)
    (ψ0 : InfoGeometry.Krein.DoubledSpace E)
    (ψ : Θ → ℝ)
    (ψStar : (Θ →L[ℝ] ℝ) → ℝ)
    (flow : InfoGeometry.Canonical.RGFlow.InformationFlow E)
    (scale0 : ℝ)
    (hClosure : SinkhornKMSClosure n T K ω β)
    (hVacSplit : VacuumEinsteinOnTransportedSplit R Kgeo x scalar Λ V Γ)
    (hHK : HohenbergKohnDualState ψ ψStar)
    (hStationary : InfoGeometry.Canonical.RGFlow.IsStationaryAtScale flow scale0) :
    IsCStarReady (Obs := ObsKMS)
      ∧ IsCompleteCStarReady (Obs := ObsFock)
      ∧ SinkhornKMSClosure n T K ω β
      ∧ IsProjectorSuperPair
          (InfoGeometry.Quantum.annihilationOp (E := E))
          (InfoGeometry.Quantum.creationOp (E := E))
      ∧ grandCanonicalFockEulerStep (E := E) η B H
          (einsteinInducedChemicalPotential (R := R) (K := Kgeo) (x := x)
            (scalar := scalar) (Λ := Λ) (V := V) (Γ := Γ)) ψ0
            = ψ0 + η • H ψ0
      ∧ HohenbergKohnDualState ψ ψStar
      ∧ RungeGrossStationaryDualState flow scale0 := by
  refine ⟨?_, ?_, ?_, projectorSuperPair_base (E := E), ?_, ?_, ?_⟩
  · exact cstarReady_of_instance (Obs := ObsKMS)
  · exact completeCStarReady_of_instance (Obs := ObsFock)
  · exact hClosure
  · exact grandCanonicalFockEulerStep_eq_hamiltonianStep_of_vacuumTransported
      (E := E) (η := η) (B := B) (H := H)
      (R := R) (Kgeo := Kgeo) (x := x) (scalar := scalar) (Λ := Λ)
      (V := V) (Γ := Γ) (ψ := ψ0) hVacSplit
  · exact hHK
  · exact rungeGrossStationaryDualState_of_stationaryAtScale
      (flow := flow) (scale0 := scale0) hStationary

end UnifiedLaunchpadInterface

section ConcreteInterfaceInstances

variable (n : Nat)
variable {F : Type} [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]
variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/--
Direct real-Hilbert instantiation of the unified readiness package.
-/
theorem aqft_readiness_package_realHilbert
    (T : SinkhornTrajectory n)
    (K : AlgebraEnd F)
    (ω : Nat → AlgebraEnd F →L[ℝ] ℝ)
    (β : ℝ)
    (η : ℝ)
    (B : BogoliubovMixingParams)
    (Hf : FockEndomorphism E)
    (R : RicciTensor E)
    (Kgeo : InfoGeometry.Canonical.KaehlerGeometry.KaehlerInformationGeometry E)
    (x : E)
    (scalar Λ : ℝ)
    (V : SplitVielbein Kgeo x)
    (Γ : SpinConnection Kgeo x V)
    (ψ : InfoGeometry.Krein.DoubledSpace E)
    (hClosure : SinkhornKMSClosure n T K ω β)
    (hVacSplit : VacuumEinsteinOnTransportedSplit R Kgeo x scalar Λ V Γ) :
    IsCStarReady (Obs := RealHilbertObs F)
      ∧ IsCompleteCStarReady (Obs := RealHilbertObs E)
      ∧ SinkhornKMSClosure n T K ω β
      ∧ grandCanonicalFockEulerStep (E := E) η B Hf
          (einsteinInducedChemicalPotential (R := R) (K := Kgeo) (x := x)
            (scalar := scalar) (Λ := Λ) (V := V) (Γ := Γ)) ψ
            = ψ + η • Hf ψ := by
  exact aqft_readiness_package
    (n := n)
    (F := F) (ObsKMS := RealHilbertObs F)
    (E := E) (ObsFock := RealHilbertObs E)
    (T := T) (K := K) (ω := ω) (β := β)
    (η := η) (B := B) (H := Hf)
    (R := R) (Kgeo := Kgeo) (x := x)
    (scalar := scalar) (Λ := Λ) (V := V) (Γ := Γ) (ψ := ψ)
    hClosure hVacSplit

/--
Direct real-Hilbert instantiation that keeps the concrete compression
interpretation visible while carrying the AQFT readiness package and the
canonical doubled-projector super-pair.
-/
theorem realHilbertCompressionInterpretation_packaged_with_aqft_readiness_and_projectorSuperPair_base
    (T : SinkhornTrajectory n)
    (K : AlgebraEnd F)
    (ω : Nat → AlgebraEnd F →L[ℝ] ℝ)
    (β : ℝ)
    (η : ℝ)
    (B : BogoliubovMixingParams)
    (Hf : FockEndomorphism E)
    (R : RicciTensor E)
    (Kgeo : InfoGeometry.Canonical.KaehlerGeometry.KaehlerInformationGeometry E)
    (x : E)
    (scalar Λ : ℝ)
    (V : SplitVielbein Kgeo x)
    (Γ : SpinConnection Kgeo x V)
    (ψ : InfoGeometry.Krein.DoubledSpace E)
    (hClosure : SinkhornKMSClosure n T K ω β)
    (hVacSplit : VacuumEinsteinOnTransportedSplit R Kgeo x scalar Λ V Γ) :
    Nonempty (AQFTOperatorInterpretation E (Obs := RealHilbertObs E))
      ∧ IsCStarReady (Obs := RealHilbertObs F)
      ∧ IsCompleteCStarReady (Obs := RealHilbertObs E)
      ∧ SinkhornKMSClosure n T K ω β
      ∧ IsProjectorSuperPair
          (InfoGeometry.Quantum.annihilationOp (E := E))
          (InfoGeometry.Quantum.creationOp (E := E))
      ∧ grandCanonicalFockEulerStep (E := E) η B Hf
          (einsteinInducedChemicalPotential (R := R) (K := Kgeo) (x := x)
            (scalar := scalar) (Λ := Λ) (V := V) (Γ := Γ)) ψ
            = ψ + η • Hf ψ := by
  refine ⟨⟨realHilbertCompressionInterpretation (E := E)⟩, ?_, ?_, ?_, ?_, ?_⟩
  · exact cstarReady_of_instance (Obs := RealHilbertObs F)
  · exact realHilbertOp_completeCStarReady (E := E)
  · exact hClosure
  · exact projectorSuperPair_base (E := E)
  · exact grandCanonicalFockEulerStep_eq_hamiltonianStep_of_vacuumTransported
      (E := E) (η := η) (B := B) (H := Hf)
      (R := R) (Kgeo := Kgeo) (x := x) (scalar := scalar) (Λ := Λ)
      (V := V) (Γ := Γ) (ψ := ψ) hVacSplit


/--
Direct constructive AQFT readiness package from IB dynamics plus the thermal
joint-kernel/commutator route to weighted Sinkhorn KMS closure.
-/
theorem realHilbertCompressionInterpretation_packaged_with_aqft_readiness_and_projectorSuperPair_base_of_ibDynamics_weighted_from_jointKernel_commutator
    (T : SinkhornTrajectory n)
    (K : AlgebraEnd F)
    (β : ℝ)
    {Xib Yib Tib : Type}
    [Fintype Xib] [Fintype Yib] [Fintype Tib]
    [MeasurableSpace Xib] [MeasurableSingletonClass Xib]
    [MeasurableSpace Yib] [MeasurableSingletonClass Yib]
    [MeasurableSpace Tib] [MeasurableSingletonClass Tib]
    (prob : IBProblem (X := Xib) (Y := Yib))
    (pTrajectory : Nat → Xib → FinProb Tib)
    (hStep : ∀ k : Nat, pTrajectory (k + 1) = ibBlahutArimotoStep prob (pTrajectory k))
    (x0 : Xib) (t0 : Tib)
    (Ω : InfoGeometry.Krein.DoubledSpace F)
    (hΩ : Ω ≠ 0)
    (hJointKernel : JointKernelOnOmega (F := F) K β Ω)
    (hCommOrthogonal : CommutatorOrthogonalOnOmega (F := F) Ω)
    (η : ℝ)
    (B : BogoliubovMixingParams)
    (Hf : FockEndomorphism E)
    (R : RicciTensor E)
    (Kgeo : InfoGeometry.Canonical.KaehlerGeometry.KaehlerInformationGeometry E)
    (x : E)
    (scalar Λ : ℝ)
    (V : SplitVielbein Kgeo x)
    (Γ : SpinConnection Kgeo x V)
    (ψ : InfoGeometry.Krein.DoubledSpace E)
    (hVacSplit : VacuumEinsteinOnTransportedSplit R Kgeo x scalar Λ V Γ) :
    Nonempty (AQFTOperatorInterpretation E (Obs := RealHilbertObs E))
      ∧ IsCStarReady (Obs := RealHilbertObs F)
      ∧ IsCompleteCStarReady (Obs := RealHilbertObs E)
      ∧ SinkhornKMSClosure n T K
          (ibInducedObservableWeighted
            (F := F) (Xib := Xib) (Yib := Yib) (Tib := Tib)
            pTrajectory x0 t0 (omegaSeed (F := F) Ω)) β
      ∧ IsProjectorSuperPair
          (InfoGeometry.Quantum.annihilationOp (E := E))
          (InfoGeometry.Quantum.creationOp (E := E))
      ∧ grandCanonicalFockEulerStep (E := E) η B Hf
          (einsteinInducedChemicalPotential (R := R) (K := Kgeo) (x := x)
            (scalar := scalar) (Λ := Λ) (V := V) (Γ := Γ)) ψ
            = ψ + η • Hf ψ := by
  have hClosure :
      SinkhornKMSClosure n T K
        (ibInducedObservableWeighted
          (F := F) (Xib := Xib) (Yib := Yib) (Tib := Tib)
          pTrajectory x0 t0 (omegaSeed (F := F) Ω)) β :=
    sinkhorn_kmsClosure_of_ibDynamics_weighted_from_jointKernel_commutator
      (n := n) (T := T) (K := K) (β := β)
      (prob := prob) (pTrajectory := pTrajectory)
      hStep (x0 := x0) (t0 := t0)
      (Ω := Ω) hΩ hJointKernel hCommOrthogonal
  exact realHilbertCompressionInterpretation_packaged_with_aqft_readiness_and_projectorSuperPair_base
    (n := n) (F := F) (E := E)
    (T := T) (K := K)
    (ω := ibInducedObservableWeighted
      (F := F) (Xib := Xib) (Yib := Yib) (Tib := Tib)
      pTrajectory x0 t0 (omegaSeed (F := F) Ω))
    (β := β) (η := η) (B := B) (Hf := Hf)
    (R := R) (Kgeo := Kgeo) (x := x)
    (scalar := scalar) (Λ := Λ) (V := V) (Γ := Γ) (ψ := ψ)
    hClosure hVacSplit

end ConcreteInterfaceInstances

end InfoGeometry.Canonical.AQFTOperatorInterface
