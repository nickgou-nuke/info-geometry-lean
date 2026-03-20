import InfoGeometry.Geometry.LegendreDuality
import InfoGeometry.Canonical.BogoliubovFockSuper
import InfoGeometry.Canonical.KMSSinkhornBridge
import InfoGeometry.Canonical.RGFlow

/-!
# InfoGeometry.Canonical.QFTTDFTLaunchpad

Constructive launchpad layer for AQFT/TDFT-oriented developments.

- AQFT side: Sinkhorn-driven KMS closure and Bogoliubov/Fock vacuum reduction.
- TDFT side: Legendre involution (density/potential duality) and RG-stationary dual map.

This file packages already-proved AQFT and TDFT ingredients into a unified
canonical interface, with no new axioms.
-/

namespace InfoGeometry.Canonical.QFTTDFTLaunchpad

open InfoGeometry.Geometry
open InfoGeometry.Krein
open InfoGeometry.Canonical.BogoliubovFockSuper
open InfoGeometry.Canonical.KMSSinkhornBridge
open InfoGeometry.Canonical.MoE
open InfoGeometry.Canonical.RGFlow
open InfoGeometry.Canonical.RicciMongeAmpere

section AQFT

variable (n : Nat)
variable {F : Type} [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]

variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/--
Vacuum-transported Einstein residual collapses the grand-canonical Fock step
to the pure Hamiltonian Euler step.
-/
theorem grandCanonicalFockEulerStep_eq_hamiltonianStep_of_vacuumTransported
    (η : ℝ)
    (B : BogoliubovMixingParams)
    (H : FockEndomorphism E)
    (R : RicciTensor E)
    (Kgeo : InfoGeometry.Canonical.KaehlerGeometry.KaehlerInformationGeometry E)
    (x : E)
    (scalar Λ : ℝ)
    (V : SplitVielbein Kgeo x)
    (Γ : SpinConnection Kgeo x V)
    (ψ : DoubledSpace E)
    (hVacSplit : VacuumEinsteinOnTransportedSplit R Kgeo x scalar Λ V Γ) :
    grandCanonicalFockEulerStep (E := E) η B H
      (einsteinInducedChemicalPotential (R := R) (K := Kgeo) (x := x)
        (scalar := scalar) (Λ := Λ) (V := V) (Γ := Γ)) ψ
      = ψ + η • H ψ := by
  change ψ + η •
      (grandCanonicalFockGenerator (E := E) B H
        (einsteinInducedChemicalPotential (R := R) (K := Kgeo) (x := x)
          (scalar := scalar) (Λ := Λ) (V := V) (Γ := Γ))) ψ
      = ψ + η • H ψ
  rw [grandCanonicalFockGenerator_eq_hamiltonian_of_vacuumTransported
      (E := E) (B := B) (H := H) (R := R) (K := Kgeo) (x := x)
      (scalar := scalar) (Λ := Λ) (V := V) (Γ := Γ) hVacSplit]

end AQFT

section TDFT

variable {Θ : Type*} [NormedAddCommGroup Θ] [NormedSpace ℝ Θ]

/--
Hohenberg-Kohn-style duality state:
primal/dual data satisfy Fenchel majorization, Fenchel-Young equality along the
chosen gradient, and the primal/dual maps are mutually inverse.
-/
def HohenbergKohnDualState
    (ψ : Θ → ℝ)
    (ψStar : (Θ →L[ℝ] ℝ) → ℝ) : Prop :=
  ∃ grad : Θ → (Θ →L[ℝ] ℝ),
    ∃ gradStar : (Θ →L[ℝ] ℝ) → Θ,
      IsFenchelMajorized ψ ψStar
        ∧ Function.LeftInverse gradStar grad
        ∧ Function.RightInverse gradStar grad
        ∧ ∀ θ : Θ, FenchelYoungEquality ψ ψStar θ (grad θ)

/--
Explicit constructive duality state:
Fenchel/Legendre data together with inverse gradient maps directly yield the
Hohenberg-Kohn duality witness.
-/
theorem hohenbergKohnDualState_of_inverse_maps
    (ψ : Θ → ℝ)
    (ψStar : (Θ →L[ℝ] ℝ) → ℝ)
    (grad : Θ → (Θ →L[ℝ] ℝ))
    (gradStar : (Θ →L[ℝ] ℝ) → Θ)
    (hConj : IsFenchelMajorized ψ ψStar)
    (hLeft : Function.LeftInverse gradStar grad)
    (hRight : Function.RightInverse gradStar grad)
    (hFY : ∀ θ : Θ, FenchelYoungEquality ψ ψStar θ (grad θ)) :
    HohenbergKohnDualState ψ ψStar := by
  exact ⟨grad, gradStar, hConj, hLeft, hRight, hFY⟩

/--
Concrete convex/smooth Legendre hypotheses discharge the Hohenberg-Kohn duality state.
-/
theorem hohenbergKohnDualState_of_concreteLegendre
    (ψ : Θ → ℝ)
    (ψStar : (Θ →L[ℝ] ℝ) → ℝ)
    (hConj : IsFenchelConjugate ψ ψStar)
    (hSupport : ∀ η, BddAbove (legendreSupport ψ η))
    (gradStar : (Θ →L[ℝ] ℝ) → Θ)
    (hLeft : Function.LeftInverse gradStar (fun θ => fderiv ℝ ψ θ))
    (hRight : Function.RightInverse gradStar (fun θ => fderiv ℝ ψ θ))
    (hDualValue :
      ∀ θ, ψStar (fderiv ℝ ψ θ) = fderiv ℝ ψ θ θ - ψ θ) :
    HohenbergKohnDualState ψ ψStar := by
  exact hohenbergKohnDualState_of_inverse_maps
    (ψ := ψ) (ψStar := ψStar)
    (grad := fun θ => fderiv ℝ ψ θ)
    (gradStar := gradStar)
    (hConj := InfoGeometry.Geometry.isFenchelMajorized_of_concrete
      (ψ := ψ) (ψStar := ψStar) hConj hSupport)
    (hLeft := hLeft)
    (hRight := hRight)
    (hFY := InfoGeometry.Geometry.fenchelYoung_along_fderiv_of_concrete
      (ψ := ψ) (ψStar := ψStar) hDualValue)

/--
Explicit constructive Fenchel-gap closure:
Fenchel-Young equality along a chosen `grad` implies zero gap along that `grad`.
-/
theorem fenchelGap_zero_along_grad_of_fenchelYoung
    (ψ : Θ → ℝ)
    (ψStar : (Θ →L[ℝ] ℝ) → ℝ)
    (grad : Θ → (Θ →L[ℝ] ℝ))
    (hFY : ∀ θ : Θ, FenchelYoungEquality ψ ψStar θ (grad θ)) :
    ∀ θ : Θ, fenchelGap ψ ψStar θ (grad θ) = 0 :=
  InfoGeometry.Geometry.fenchelGap_zero_along_grad_of_fenchelYoung
    (ψ := ψ) (ψStar := ψStar) (grad := grad) hFY

/-- Concrete convex/smooth Legendre hypotheses imply zero Fenchel gap along `fderiv`. -/
theorem fenchelGap_zero_along_fderiv_of_concreteLegendre
    (ψ : Θ → ℝ)
    (ψStar : (Θ →L[ℝ] ℝ) → ℝ)
    (hDualValue :
      ∀ θ, ψStar (fderiv ℝ ψ θ) = fderiv ℝ ψ θ θ - ψ θ) :
    ∀ θ : Θ, fenchelGap ψ ψStar θ (fderiv ℝ ψ θ) = 0 :=
  InfoGeometry.Geometry.fenchelGap_eq_zero_along_fderiv_of_concrete
    (ψ := ψ) (ψStar := ψStar) hDualValue

variable {E : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/--
Runge-Gross-style stationary dual-map state at RG scale `scale0`.
-/
def RungeGrossStationaryDualState
    (flow : InformationFlow E)
    (scale0 : ℝ) : Prop :=
  ∀ x : E, HasDerivAt (fun t => (flow t).dualMap x) 0 scale0

/--
RG stationarity constructively implies stationary dual-map dynamics.
-/
theorem rungeGrossStationaryDualState_of_stationaryAtScale
    (flow : InformationFlow E)
    (scale0 : ℝ)
    (hStationary : IsStationaryAtScale flow scale0) :
    RungeGrossStationaryDualState flow scale0 := by
  exact hStationary.2

/--
Constructive stationary dual-map state from RG flow invariance.
-/
theorem rungeGrossStationaryDualState_of_flowInvariant
    (flow : InformationFlow E)
    (scale0 : ℝ) :
    FlowInvariantAtScale flow scale0 →
      RungeGrossStationaryDualState flow scale0 := by
  intro hInv
  exact rungeGrossStationaryDualState_of_stationaryAtScale
    (flow := flow) (scale0 := scale0)
    (isStationaryAtScale_of_flowInvariant (E := E) flow scale0 hInv)

/--
Constructive stationary dual-map state from modular-flow/Clifford-action
invariance on the bundle.
-/
theorem rungeGrossStationaryDualState_of_modularCliffordFlowInvariant
    {ι : Type*}
    (flow : InformationFlow E)
    (scale0 : ℝ)
    (σ : ℝ → E →ₗ[ℝ] E)
    (cliffordAction : ι → E →ₗ[ℝ] E)
    (unit : ι)
    (hInv : ModularCliffordFlowInvariantAtScale
      (E := E) (ι := ι) flow scale0 σ cliffordAction unit) :
    RungeGrossStationaryDualState flow scale0 := by
  exact rungeGrossStationaryDualState_of_stationaryAtScale
    (flow := flow) (scale0 := scale0)
    (isStationaryAtScale_of_modularCliffordFlowInvariant
      (E := E) (ι := ι) flow scale0 σ cliffordAction unit hInv)

/--
Constant-flow corollary of flow-invariant stationarity.
-/
theorem rungeGrossStationaryDualState_of_constantFlow
    (H : InfoGeometry.Convex.HessianGeometry E)
    (scale0 : ℝ) :
    RungeGrossStationaryDualState (constantFlow (E := E) H) scale0 := by
  exact rungeGrossStationaryDualState_of_modularCliffordFlowInvariant
    (E := E) (ι := Unit)
    (flow := constantFlow (E := E) H) (scale0 := scale0)
    (σ := fun _ : ℝ => (LinearMap.id : E →ₗ[ℝ] E))
    (cliffordAction := fun _ : Unit => (LinearMap.id : E →ₗ[ℝ] E))
    (unit := ())
    (modularCliffordFlowInvariant_constantFlow_id (E := E) H scale0)

end TDFT

section Launchpad

variable (n : Nat)
variable {F : Type} [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]
variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
variable {Θ : Type*} [NormedAddCommGroup Θ] [NormedSpace ℝ Θ]

/--
Unified constructive launchpad:
AQFT closure + vacuum-reduced Fock step + TDFT duality and RG stationarity.
-/
theorem aqft_tdft_constructive_launchpad
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
    (ψ0 : DoubledSpace E)
    (ψ : Θ → ℝ)
    (ψStar : (Θ →L[ℝ] ℝ) → ℝ)
    (flow : InformationFlow E)
    (scale0 : ℝ)
    (hClosure : SinkhornKMSClosure n T K ω β)
    (hVacSplit : VacuumEinsteinOnTransportedSplit R Kgeo x scalar Λ V Γ)
    (hHK : HohenbergKohnDualState ψ ψStar)
    (hStationary : IsStationaryAtScale flow scale0) :
    SinkhornKMSClosure n T K ω β
      ∧ grandCanonicalFockEulerStep (E := E) η B H
          (einsteinInducedChemicalPotential (R := R) (K := Kgeo) (x := x)
            (scalar := scalar) (Λ := Λ) (V := V) (Γ := Γ)) ψ0
            = ψ0 + η • H ψ0
      ∧ HohenbergKohnDualState ψ ψStar
      ∧ RungeGrossStationaryDualState flow scale0 := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact hClosure
  · exact grandCanonicalFockEulerStep_eq_hamiltonianStep_of_vacuumTransported
      (E := E) (η := η) (B := B) (H := H)
      (R := R) (Kgeo := Kgeo) (x := x) (scalar := scalar) (Λ := Λ)
      (V := V) (Γ := Γ) (ψ := ψ0) hVacSplit
  · exact hHK
  · exact rungeGrossStationaryDualState_of_stationaryAtScale
      (flow := flow) (scale0 := scale0) hStationary

/--
Constructive launchpad specialization with no explicit stationarity witness:
for constant RG flow, stationarity is derived canonically.
-/
theorem aqft_tdft_constructive_launchpad_of_constantFlow
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
    (ψ0 : DoubledSpace E)
    (ψ : Θ → ℝ)
    (ψStar : (Θ →L[ℝ] ℝ) → ℝ)
    (Hrg : InfoGeometry.Convex.HessianGeometry E)
    (scale0 : ℝ)
    (hClosure : SinkhornKMSClosure n T K ω β)
    (hVacSplit : VacuumEinsteinOnTransportedSplit R Kgeo x scalar Λ V Γ)
    (hHK : HohenbergKohnDualState ψ ψStar) :
    SinkhornKMSClosure n T K ω β
      ∧ grandCanonicalFockEulerStep (E := E) η B H
          (einsteinInducedChemicalPotential (R := R) (K := Kgeo) (x := x)
            (scalar := scalar) (Λ := Λ) (V := V) (Γ := Γ)) ψ0
            = ψ0 + η • H ψ0
      ∧ HohenbergKohnDualState ψ ψStar
      ∧ RungeGrossStationaryDualState (constantFlow (E := E) Hrg) scale0 := by
  exact aqft_tdft_constructive_launchpad
    (n := n) (T := T) (K := K) (ω := ω) (β := β)
    (η := η) (B := B) (H := H)
    (R := R) (Kgeo := Kgeo) (x := x) (scalar := scalar) (Λ := Λ)
    (V := V) (Γ := Γ) (ψ0 := ψ0)
    (ψ := ψ) (ψStar := ψStar)
    (flow := constantFlow (E := E) Hrg) (scale0 := scale0)
    (hClosure := hClosure) (hVacSplit := hVacSplit) (hHK := hHK)
    (hStationary := isStationaryAtScale_constantFlow (E := E) Hrg scale0)

/--
Invariant-flow specialization: no explicit stationarity witness argument;
stationarity is derived from flow invariance.
-/
theorem aqft_tdft_constructive_launchpad_of_flowInvariant
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
    (ψ0 : DoubledSpace E)
    (ψ : Θ → ℝ)
    (ψStar : (Θ →L[ℝ] ℝ) → ℝ)
    (flow : InformationFlow E)
    (scale0 : ℝ)
    (hClosure : SinkhornKMSClosure n T K ω β)
    (hVacSplit : VacuumEinsteinOnTransportedSplit R Kgeo x scalar Λ V Γ)
    (hHK : HohenbergKohnDualState ψ ψStar)
    (hInv : FlowInvariantAtScale flow scale0) :
    SinkhornKMSClosure n T K ω β
      ∧ grandCanonicalFockEulerStep (E := E) η B H
          (einsteinInducedChemicalPotential (R := R) (K := Kgeo) (x := x)
            (scalar := scalar) (Λ := Λ) (V := V) (Γ := Γ)) ψ0
            = ψ0 + η • H ψ0
      ∧ HohenbergKohnDualState ψ ψStar
      ∧ RungeGrossStationaryDualState flow scale0 := by
  exact aqft_tdft_constructive_launchpad
    (n := n) (T := T) (K := K) (ω := ω) (β := β)
    (η := η) (B := B) (H := H)
    (R := R) (Kgeo := Kgeo) (x := x) (scalar := scalar) (Λ := Λ)
    (V := V) (Γ := Γ) (ψ0 := ψ0)
    (ψ := ψ) (ψStar := ψStar)
    (flow := flow) (scale0 := scale0)
    (hClosure := hClosure) (hVacSplit := hVacSplit) (hHK := hHK)
    (hStationary := isStationaryAtScale_of_flowInvariant (E := E) flow scale0 hInv)

/--
Modular/Clifford-bundle specialization: no explicit stationarity witness
argument; stationarity is derived from modular-flow and Clifford-action
invariance.
-/
theorem aqft_tdft_constructive_launchpad_of_modularCliffordFlowInvariant
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
    (ψ0 : DoubledSpace E)
    (ψ : Θ → ℝ)
    (ψStar : (Θ →L[ℝ] ℝ) → ℝ)
    (flow : InformationFlow E)
    (scale0 : ℝ)
    {ι : Type*}
    (σ : ℝ → E →ₗ[ℝ] E)
    (cliffordAction : ι → E →ₗ[ℝ] E)
    (unit : ι)
    (hClosure : SinkhornKMSClosure n T K ω β)
    (hVacSplit : VacuumEinsteinOnTransportedSplit R Kgeo x scalar Λ V Γ)
    (hHK : HohenbergKohnDualState ψ ψStar)
    (hInv : ModularCliffordFlowInvariantAtScale
      (E := E) (ι := ι) flow scale0 σ cliffordAction unit) :
    SinkhornKMSClosure n T K ω β
      ∧ grandCanonicalFockEulerStep (E := E) η B H
          (einsteinInducedChemicalPotential (R := R) (K := Kgeo) (x := x)
            (scalar := scalar) (Λ := Λ) (V := V) (Γ := Γ)) ψ0
            = ψ0 + η • H ψ0
      ∧ HohenbergKohnDualState ψ ψStar
      ∧ RungeGrossStationaryDualState flow scale0 := by
  exact aqft_tdft_constructive_launchpad
    (n := n) (T := T) (K := K) (ω := ω) (β := β)
    (η := η) (B := B) (H := H)
    (R := R) (Kgeo := Kgeo) (x := x) (scalar := scalar) (Λ := Λ)
    (V := V) (Γ := Γ) (ψ0 := ψ0)
    (ψ := ψ) (ψStar := ψStar)
    (flow := flow) (scale0 := scale0)
    (hClosure := hClosure) (hVacSplit := hVacSplit) (hHK := hHK)
    (hStationary := isStationaryAtScale_of_modularCliffordFlowInvariant
      (E := E) (ι := ι) flow scale0 σ cliffordAction unit hInv)

end Launchpad

end InfoGeometry.Canonical.QFTTDFTLaunchpad
