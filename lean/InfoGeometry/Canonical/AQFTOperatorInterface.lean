import InfoGeometry.Canonical.QFTTDFTLaunchpad
import Mathlib.Analysis.CStarAlgebra.Basic
import Mathlib.Analysis.CStarAlgebra.ContinuousLinearMap
import Mathlib.Analysis.InnerProductSpace.Adjoint

/-!
# Research.AQFTOperatorInterface

AQFT operator-algebra interface layer:

- abstract C*-ready / von-Neumann-ready signatures
- concrete finite-model realizations over existing `AlgebraEnd` infrastructure
- constructive closure theorems reusing the proved Sinkhorn-KMS and Fock vacuum bridges
-/

namespace InfoGeometry.Canonical.AQFTOperatorInterface

open InfoGeometry.Krein
open InfoGeometry.Canonical.KMSSinkhornBridge
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
Abstract von-Neumann-ready AQFT signature used in this library:
C*-ready plus completeness.
-/
abbrev IsVonNeumannReady : Prop :=
  IsCStarReady Obs ∧ CompleteSpace Obs

end AbstractSignatures

section Realizations

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]
variable {Obs : Type*} [NonUnitalNormedRing Obs] [StarRing Obs]

/--
Explicit realization map from the concrete finite doubled-space operator model
into an abstract operator algebra.
-/
structure AQFTOperatorRealization
    (F : Type*) [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F] where
  realize : AlgebraEnd F → Obs

/-- Theorem `cstarReady_of_instance`. -/
theorem cstarReady_of_instance
    [CStarRing Obs] :
    IsCStarReady (Obs := Obs) := by
  infer_instance

/-- Theorem `vonNeumannReady_of_instance`. -/
theorem vonNeumannReady_of_instance
    [CStarRing Obs] [CompleteSpace Obs] :
    IsVonNeumannReady (Obs := Obs) := by
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

/-- Concrete realization into real Hilbert bounded operators via first-leg compression. -/
def realHilbertCompressionRealization :
    AQFTOperatorRealization E (Obs := RealHilbertObs E) where
  realize := firstLegCompression (E := E)

/-- Theorem `realHilbertOp_cstarReady`. -/
theorem realHilbertOp_cstarReady :
    IsCStarReady (Obs := RealHilbertObs E) := by
  infer_instance

/-- Theorem `realHilbertOp_vonNeumannReady`. -/
theorem realHilbertOp_vonNeumannReady :
    IsVonNeumannReady (Obs := RealHilbertObs E) := by
  exact ⟨realHilbertOp_cstarReady (E := E), inferInstance⟩

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

/-- Complex-operator realization wrapper (complex-source counterpart). -/
structure ComplexAQFTOperatorRealization
    (Obs : Type*) [NonUnitalNormedRing Obs] [StarRing Obs] where
  realize : ComplexHilbertOp H → Obs

/-- Complex realization into Hilbert bounded operators via first-leg compression. -/
def complexHilbertCompressionRealization :
    ComplexAQFTOperatorRealization (H := H) (Obs := ComplexHilbertObs H) where
  realize := complexFirstLegCompression (H := H)

/-- Theorem `complexHilbertOp_cstarReady`. -/
theorem complexHilbertOp_cstarReady :
    IsCStarReady (Obs := ComplexHilbertObs H) := by
  infer_instance

/-- Theorem `complexHilbertOp_vonNeumannReady`. -/
theorem complexHilbertOp_vonNeumannReady :
    IsVonNeumannReady (Obs := ComplexHilbertObs H) := by
  exact ⟨complexHilbertOp_cstarReady (H := H), inferInstance⟩

end ConcreteHilbertModels

section KMSInterface

variable (n : Nat)
variable {F : Type} [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]
variable {Obs : Type*} [NonUnitalNormedRing Obs] [StarRing Obs] [CStarRing Obs]

/--
C*-ready interface theorem:
given any realization of concrete operators into a C*-algebraic target,
the constructive Sinkhorn-to-KMS closure still holds on the concrete dynamics.
-/
theorem sinkhorn_kmsClosure_with_cstarRealization
    (_real : AQFTOperatorRealization (F := F) (Obs := Obs))
    (T : SinkhornTrajectory n)
    (K : AlgebraEnd F)
    (ω : Nat → AlgebraEnd F →L[ℝ] ℝ)
    (β : ℝ)
    (hControl : SinkhornKMSControl n T K ω β) :
    IsCStarReady (Obs := Obs) ∧ SinkhornKMSClosure n T K ω β := by
  refine ⟨cstarReady_of_instance (Obs := Obs), ?_⟩
  exact aqft_kmsClosure_of_sinkhornControl
    (n := n) (T := T) (K := K) (ω := ω) (β := β) hControl

end KMSInterface

section FockInterface

variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
variable {Obs : Type*} [NonUnitalNormedRing Obs] [StarRing Obs] [CStarRing Obs] [CompleteSpace Obs]

/--
Von-Neumann-ready interface theorem:
given any realization of concrete Fock operators into a complete C*-target,
vacuum-transported Einstein residual still collapses the grand-canonical Euler step.
-/
theorem grandCanonicalFockEulerStep_with_vonNeumannRealization
    (_real : AQFTOperatorRealization (F := E) (Obs := Obs))
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
    IsVonNeumannReady (Obs := Obs)
      ∧ grandCanonicalFockEulerStep (E := E) η B H
          (einsteinInducedChemicalPotential (R := R) (K := Kgeo) (x := x)
            (scalar := scalar) (Λ := Λ) (V := V) (Γ := Γ)) ψ
            = ψ + η • H ψ := by
  refine ⟨vonNeumannReady_of_instance (Obs := Obs), ?_⟩
  exact grandCanonicalFockEulerStep_eq_hamiltonianStep_of_vacuumTransported
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
Unified interface package:
with explicit realization maps into C*- / von-Neumann-ready targets,
the concrete AQFT closures are preserved.
-/
theorem aqft_interface_package_with_realizations
    (realKMS : AQFTOperatorRealization (F := F) (Obs := ObsKMS))
    (realFock : AQFTOperatorRealization (F := E) (Obs := ObsFock))
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
    (hControl : SinkhornKMSControl n T K ω β)
    (hVacSplit : VacuumEinsteinOnTransportedSplit R Kgeo x scalar Λ V Γ) :
    IsCStarReady (Obs := ObsKMS)
      ∧ IsVonNeumannReady (Obs := ObsFock)
      ∧ SinkhornKMSClosure n T K ω β
      ∧ grandCanonicalFockEulerStep (E := E) η B H
          (einsteinInducedChemicalPotential (R := R) (K := Kgeo) (x := x)
            (scalar := scalar) (Λ := Λ) (V := V) (Γ := Γ)) ψ
            = ψ + η • H ψ := by
  have hK :=
    sinkhorn_kmsClosure_with_cstarRealization
      (n := n) (F := F) (Obs := ObsKMS) realKMS
      (T := T) (K := K) (ω := ω) (β := β) hControl
  have hF :=
    grandCanonicalFockEulerStep_with_vonNeumannRealization
      (E := E) (Obs := ObsFock) realFock
      (η := η) (B := B) (H := H)
      (R := R) (Kgeo := Kgeo) (x := x) (scalar := scalar) (Λ := Λ)
      (V := V) (Γ := Γ) (ψ := ψ) hVacSplit
  exact ⟨hK.1, hF.1, hK.2, hF.2⟩

end UnifiedInterface

section ConcreteInterfaceInstances

variable (n : Nat)
variable {F : Type} [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]
variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/--
Direct real-Hilbert instantiation of the unified AQFT interface package.
-/
theorem aqft_interface_package_realHilbert
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
    (hControl : SinkhornKMSControl n T K ω β)
    (hVacSplit : VacuumEinsteinOnTransportedSplit R Kgeo x scalar Λ V Γ) :
    IsCStarReady (Obs := RealHilbertObs F)
      ∧ IsVonNeumannReady (Obs := RealHilbertObs E)
      ∧ SinkhornKMSClosure n T K ω β
      ∧ grandCanonicalFockEulerStep (E := E) η B Hf
          (einsteinInducedChemicalPotential (R := R) (K := Kgeo) (x := x)
            (scalar := scalar) (Λ := Λ) (V := V) (Γ := Γ)) ψ
            = ψ + η • Hf ψ := by
  exact aqft_interface_package_with_realizations
    (n := n)
    (F := F) (ObsKMS := RealHilbertObs F)
    (E := E) (ObsFock := RealHilbertObs E)
    (realKMS := realHilbertCompressionRealization (E := F))
    (realFock := realHilbertCompressionRealization (E := E))
    (T := T) (K := K) (ω := ω) (β := β)
    (η := η) (B := B) (H := Hf)
    (R := R) (Kgeo := Kgeo) (x := x)
    (scalar := scalar) (Λ := Λ) (V := V) (Γ := Γ) (ψ := ψ)
    hControl hVacSplit

end ConcreteInterfaceInstances

end InfoGeometry.Canonical.AQFTOperatorInterface
