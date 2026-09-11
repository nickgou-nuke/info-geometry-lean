import InfoGeometry.Canonical.OperatorAlgebraReadiness
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Canonical.AQFTOperatorEndpoints
import InfoGeometry.Canonical.QFTTDFTLaunchpad
import InfoGeometry.Canonical.KMSSinkhornSeedState
import InfoGeometry.Canonical.KMSSinkhornScalarPotential
import InfoGeometry.Canonical.KMSSinkhornWeightedTransport
import InfoGeometry.Canonical.BogoliubovFockSuper
import InfoGeometry.Canonical.RicciMongeAmpere

open scoped InnerProductSpace

/-!
# OperatorAlgebraAQFTPackage

AQFT/TDFT packaging layer for operator-algebra readiness targets.
-/

namespace InfoGeometry.Canonical.OperatorAlgebraBridge

open InfoGeometry.Krein
open InfoGeometry.Canonical.AQFTOperatorInterface
open InfoGeometry.Canonical.KMSSinkhornBridge
open InfoGeometry.Canonical.BogoliubovFockSuper
open InfoGeometry.Canonical.RicciMongeAmpere

section UnifiedPackage

variable (n : Nat)
variable {F : Type} [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]
variable {ObsKMS : Type*}
  [NonUnitalNormedRing ObsKMS] [StarRing ObsKMS] [CStarRing ObsKMS]
variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
variable {ObsFock : Type*}
  [NonUnitalNormedRing ObsFock] [StarRing ObsFock] [CStarRing ObsFock]
  [CompleteSpace ObsFock]

/--
Canonical AQFT package combining operator-target readiness, Sinkhorn/KMS
closure, the canonical doubled-projector super-pair, and the vacuum-reduced
grand-canonical Euler law.
-/
theorem cstar_completeCStar_kms_fock_projectorSuperPair_base_package
    (T : InfoGeometry.Canonical.MoE.SinkhornTrajectory n)
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
    (V : InfoGeometry.Canonical.RicciMongeAmpere.SplitVielbein Kgeo x)
    (Γ : InfoGeometry.Canonical.RicciMongeAmpere.SpinConnection Kgeo x V)
    (ψ : DoubledSpace E)
    (h_closure : SinkhornKMSClosure n T K ω β)
    (h_vac_split : VacuumEinsteinOnTransportedSplit R Kgeo x scalar Λ V Γ) :
    IsCStarLayer (Obs := ObsKMS) ∧
      IsCompleteCStarLayer (Obs := ObsFock) ∧
      SinkhornKMSClosure n T K ω β ∧
      IsProjectorSuperPair
        (InfoGeometry.Quantum.annihilationOp (E := E))
        (InfoGeometry.Quantum.creationOp (E := E)) ∧
      grandCanonicalFockEulerStep (E := E) η B H
          (einsteinInducedChemicalPotential (R := R) (K := Kgeo) (x := x)
            (scalar := scalar) (Λ := Λ) (V := V) (Γ := Γ)) ψ
          = ψ + η • H ψ := by
  refine ⟨?_, ?_, ?_, projectorSuperPair_base (E := E), ?_⟩
  · infer_instance
  · exact ⟨by infer_instance, inferInstance⟩
  · exact h_closure
  · exact grandCanonicalEulerStep_eq_of_vacuumSplit
      (E := E) (η := η) (B := B) (Hf := H)
      (R := R) (Kgeo := Kgeo) (x := x)
      (scalar := scalar) (Λ := Λ) (V := V) (Γ := Γ) (ψ := ψ)
      h_vac_split

end UnifiedPackage

section UnifiedLaunchpadPackage

variable (n : Nat)
variable {F : Type} [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]
variable {ObsKMS : Type*}
  [NonUnitalNormedRing ObsKMS] [StarRing ObsKMS] [CStarRing ObsKMS]
variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
variable {ObsFock : Type*}
  [NonUnitalNormedRing ObsFock] [StarRing ObsFock] [CStarRing ObsFock]
  [CompleteSpace ObsFock]
variable {Θ : Type*} [NormedAddCommGroup Θ] [NormedSpace ℝ Θ]

/--
Canonical operator-layer version of the unified AQFT/TDFT launchpad packaged
with C* and complete-C* readiness.
-/
theorem cstar_completeCStar_kms_fock_tdft_launchpad_package
    (T : InfoGeometry.Canonical.MoE.SinkhornTrajectory n)
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
    (V : InfoGeometry.Canonical.RicciMongeAmpere.SplitVielbein Kgeo x)
    (Γ : InfoGeometry.Canonical.RicciMongeAmpere.SpinConnection Kgeo x V)
    (ψ0 : DoubledSpace E)
    (ψ : Θ → ℝ)
    (ψStar : (Θ →L[ℝ] ℝ) → ℝ)
    (flow : InfoGeometry.Canonical.RGFlow.InformationFlow E)
    (scale0 : ℝ)
    (hClosure : SinkhornKMSClosure n T K ω β)
    (hVacSplit : VacuumEinsteinOnTransportedSplit R Kgeo x scalar Λ V Γ)
    (hHK : InfoGeometry.Canonical.QFTTDFTLaunchpad.HohenbergKohnDualState ψ ψStar)
    (hStationary : InfoGeometry.Canonical.RGFlow.IsStationaryAtScale flow scale0) :
    IsCStarLayer (Obs := ObsKMS)
      ∧ IsCompleteCStarLayer (Obs := ObsFock)
      ∧ SinkhornKMSClosure n T K ω β
      ∧ grandCanonicalFockEulerStep (E := E) η B H
          (einsteinInducedChemicalPotential (R := R) (K := Kgeo) (x := x)
            (scalar := scalar) (Λ := Λ) (V := V) (Γ := Γ)) ψ0
          = ψ0 + η • H ψ0
      ∧ InfoGeometry.Canonical.QFTTDFTLaunchpad.HohenbergKohnDualState ψ ψStar
      ∧ InfoGeometry.Canonical.QFTTDFTLaunchpad.RungeGrossStationaryDualState flow scale0 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · infer_instance
  · exact ⟨by infer_instance, inferInstance⟩
  · exact hClosure
  · exact grandCanonicalEulerStep_eq_of_vacuumSplit
      (E := E) (η := η) (B := B) (Hf := H)
      (R := R) (Kgeo := Kgeo) (x := x)
      (scalar := scalar) (Λ := Λ) (V := V) (Γ := Γ) (ψ := ψ0)
      hVacSplit
  · exact hHK
  · exact InfoGeometry.Canonical.QFTTDFTLaunchpad.rungeGrossStationaryDualState_of_stationaryAtScale
      (flow := flow) (scale0 := scale0) hStationary

/--
Canonical operator-layer version of the unified AQFT/TDFT launchpad with the
explicit Bogoliubov projector-superalgebra carried alongside the readiness
package.
-/
theorem cstar_completeCStar_kms_fock_tdft_launchpad_with_bogoliubov_projector_package
    (T : InfoGeometry.Canonical.MoE.SinkhornTrajectory n)
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
    (V : InfoGeometry.Canonical.RicciMongeAmpere.SplitVielbein Kgeo x)
    (Γ : InfoGeometry.Canonical.RicciMongeAmpere.SpinConnection Kgeo x V)
    (ψ0 : DoubledSpace E)
    (ψ : Θ → ℝ)
    (ψStar : (Θ →L[ℝ] ℝ) → ℝ)
    (flow : InfoGeometry.Canonical.RGFlow.InformationFlow E)
    (scale0 : ℝ)
    (hClosure : SinkhornKMSClosure n T K ω β)
    (hVacSplit : VacuumEinsteinOnTransportedSplit R Kgeo x scalar Λ V Γ)
    (hHK : InfoGeometry.Canonical.QFTTDFTLaunchpad.HohenbergKohnDualState ψ ψStar)
    (hStationary : InfoGeometry.Canonical.RGFlow.IsStationaryAtScale flow scale0) :
    IsCStarLayer (Obs := ObsKMS)
      ∧ IsCompleteCStarLayer (Obs := ObsFock)
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
      ∧ InfoGeometry.Canonical.QFTTDFTLaunchpad.HohenbergKohnDualState ψ ψStar
      ∧ InfoGeometry.Canonical.QFTTDFTLaunchpad.RungeGrossStationaryDualState flow scale0 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · infer_instance
  · exact ⟨by infer_instance, inferInstance⟩
  · exact hClosure
  · exact (bogoliubov_projector_superalgebra (E := E) B).1
  · exact (bogoliubov_projector_superalgebra (E := E) B).2
  · exact grandCanonicalEulerStep_eq_of_vacuumSplit
      (E := E) (η := η) (B := B) (Hf := H)
      (R := R) (Kgeo := Kgeo) (x := x)
      (scalar := scalar) (Λ := Λ) (V := V) (Γ := Γ) (ψ := ψ0)
      hVacSplit
  · exact hHK
  · exact InfoGeometry.Canonical.QFTTDFTLaunchpad.rungeGrossStationaryDualState_of_stationaryAtScale
      (flow := flow) (scale0 := scale0) hStationary

/--
Canonical operator-layer version of the unified AQFT/TDFT launchpad carrying
the canonical doubled-projector super-pair alongside C* readiness.
-/
theorem cstar_completeCStar_kms_fock_tdft_launchpad_with_projectorSuperPair_base_package
    (T : InfoGeometry.Canonical.MoE.SinkhornTrajectory n)
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
    (V : InfoGeometry.Canonical.RicciMongeAmpere.SplitVielbein Kgeo x)
    (Γ : InfoGeometry.Canonical.RicciMongeAmpere.SpinConnection Kgeo x V)
    (ψ0 : DoubledSpace E)
    (ψ : Θ → ℝ)
    (ψStar : (Θ →L[ℝ] ℝ) → ℝ)
    (flow : InfoGeometry.Canonical.RGFlow.InformationFlow E)
    (scale0 : ℝ)
    (hClosure : SinkhornKMSClosure n T K ω β)
    (hVacSplit : VacuumEinsteinOnTransportedSplit R Kgeo x scalar Λ V Γ)
    (hHK : InfoGeometry.Canonical.QFTTDFTLaunchpad.HohenbergKohnDualState ψ ψStar)
    (hStationary : InfoGeometry.Canonical.RGFlow.IsStationaryAtScale flow scale0) :
    IsCStarLayer (Obs := ObsKMS)
      ∧ IsCompleteCStarLayer (Obs := ObsFock)
      ∧ SinkhornKMSClosure n T K ω β
      ∧ IsProjectorSuperPair
          (InfoGeometry.Quantum.annihilationOp (E := E))
          (InfoGeometry.Quantum.creationOp (E := E))
      ∧ grandCanonicalFockEulerStep (E := E) η B H
          (einsteinInducedChemicalPotential (R := R) (K := Kgeo) (x := x)
            (scalar := scalar) (Λ := Λ) (V := V) (Γ := Γ)) ψ0
          = ψ0 + η • H ψ0
      ∧ InfoGeometry.Canonical.QFTTDFTLaunchpad.HohenbergKohnDualState ψ ψStar
      ∧ InfoGeometry.Canonical.QFTTDFTLaunchpad.RungeGrossStationaryDualState flow scale0 := by
  refine ⟨?_, ?_, ?_, projectorSuperPair_base (E := E), ?_, ?_, ?_⟩
  · infer_instance
  · exact ⟨by infer_instance, inferInstance⟩
  · exact hClosure
  · exact grandCanonicalEulerStep_eq_of_vacuumSplit
      (E := E) (η := η) (B := B) (Hf := H)
      (R := R) (Kgeo := Kgeo) (x := x)
      (scalar := scalar) (Λ := Λ) (V := V) (Γ := Γ) (ψ := ψ0)
      hVacSplit
  · exact hHK
  · exact InfoGeometry.Canonical.QFTTDFTLaunchpad.rungeGrossStationaryDualState_of_stationaryAtScale
      (flow := flow) (scale0 := scale0) hStationary

end UnifiedLaunchpadPackage

end InfoGeometry.Canonical.OperatorAlgebraBridge
