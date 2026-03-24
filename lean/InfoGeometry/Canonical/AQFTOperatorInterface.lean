import InfoGeometry.Canonical.KMSSinkhornBridge
import InfoGeometry.Canonical.GrandCanonicalExperts
import InfoGeometry.Canonical.BogoliubovFockSuper
import InfoGeometry.Canonical.RicciMongeAmpere
import InfoGeometry.Canonical.IBCore
import Mathlib.Analysis.CStarAlgebra.Basic
import Mathlib.Analysis.CStarAlgebra.ContinuousLinearMap
import Mathlib.Analysis.InnerProductSpace.Adjoint

/-!
# InfoGeometry.Canonical.AQFTOperatorInterface

AQFT operator-algebra preparation layer:

- abstract C*-ready / complete-C*-ready signatures
- concrete finite-model interpretation/compression maps over existing `AlgebraEnd` infrastructure
- static readiness packages and constructive AQFT endpoints
-/

namespace InfoGeometry.Canonical.AQFTOperatorInterface

open InfoGeometry.Krein
open InfoGeometry.Canonical.KMSSinkhornBridge
open InfoGeometry.Canonical.IB
open InfoGeometry.Canonical.MoE
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
    (F : Type*) (Obs : Type*)
    [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]
    [NonUnitalNormedRing Obs] [StarRing Obs] where
  interpret : AlgebraEnd F → Obs

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
    AQFTOperatorInterpretation E (RealHilbertObs E) where
  interpret := firstLegCompression (E := E)

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
    (H : Type*) (Obs : Type*)
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    [NonUnitalNormedRing Obs] [StarRing Obs] where
  interpret : ComplexHilbertOp H → Obs

/-- Complex interpretation into Hilbert bounded operators via first-leg compression. -/
def complexHilbertCompressionInterpretation :
    ComplexAQFTOperatorInterpretation H (ComplexHilbertObs H) where
  interpret := complexFirstLegCompression (H := H)

end ConcreteHilbertModels

section CanonicalEndpoint

variable {F : Type} [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]
variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/--
Static AQFT readiness data for the real Hilbert model.
-/
structure AQFTReadinessPackage
    (F E : Type)
    [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E] where
  isCStarReadyF : IsCStarReady (Obs := RealHilbertObs F)
  isCompleteCStarReadyE : IsCompleteCStarReady (Obs := RealHilbertObs E)
  interpretation : AQFTOperatorInterpretation E (RealHilbertObs E)
  projectorSuperPair :
    IsProjectorSuperPair (E := E)
      (InfoGeometry.Quantum.annihilationOp (E := E))
      (InfoGeometry.Quantum.creationOp (E := E))

/-- Canonical static readiness package for the real Hilbert AQFT model. -/
def aqftReadinessPackageRealHilbert :
    AQFTReadinessPackage F E where
  isCStarReadyF := by
    infer_instance
  isCompleteCStarReadyE := by
    exact ⟨by infer_instance, inferInstance⟩
  interpretation := realHilbertCompressionInterpretation (E := E)
  projectorSuperPair := projectorSuperPair_base (E := E)

/--
Constructive Fock-side payload:
vacuum-transported splitting identifies the grand-canonical Euler step with
the underlying Hamiltonian update.
-/
theorem grandCanonicalEulerStep_eq_of_vacuumSplit
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
    grandCanonicalFockEulerStep (E := E) η B Hf
      (einsteinInducedChemicalPotential (R := R) (K := Kgeo) (x := x)
        (scalar := scalar) (Λ := Λ) (V := V) (Γ := Γ)) ψ
      = ψ + η • Hf ψ := by
  change ψ + η •
      (grandCanonicalFockGenerator (E := E) B Hf
        (einsteinInducedChemicalPotential (R := R) (K := Kgeo) (x := x)
          (scalar := scalar) (Λ := Λ) (V := V) (Γ := Γ))) ψ
    = ψ + η • Hf ψ
  rw [grandCanonicalFockGenerator_eq_hamiltonian_of_vacuumTransported
    (E := E) (B := B) (H := Hf) (R := R) (K := Kgeo) (x := x)
    (scalar := scalar) (Λ := Λ) (V := V) (Γ := Γ) hVacSplit]

/--
Constructive thermal payload:
derive weighted Sinkhorn-KMS closure from IB dynamics through the
joint-kernel/commutator route.
-/
theorem ibWeightedKMSClosure_of_jointKernel_commutator
    (n : Nat)
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
    (x0 : Xib)
    (t0 : Tib)
    (Ω : InfoGeometry.Krein.DoubledSpace F)
    (hΩ : Ω ≠ 0)
    (hJointKernel : JointKernelOnOmega (F := F) K β Ω)
    (hCommOrthogonal : CommutatorOrthogonalOnOmega (F := F) Ω) :
    SinkhornKMSClosure n T K
      (ibInducedObservableWeighted
        (F := F) (Xib := Xib) (Yib := Yib) (Tib := Tib)
        pTrajectory x0 t0 (omegaSeed (F := F) Ω)) β := by
  exact sinkhorn_kmsClosure_of_ibDynamics_weighted_from_jointKernel_commutator
    (n := n) (T := T) (K := K) (β := β)
    (prob := prob) (pTrajectory := pTrajectory)
    hStep (x0 := x0) (t0 := t0)
    (Ω := Ω) hΩ hJointKernel hCommOrthogonal

end CanonicalEndpoint

end InfoGeometry.Canonical.AQFTOperatorInterface
