import InfoGeometry.Geometry.LegendreDuality
import InfoGeometry.Canonical.BogoliubovFockSuper
import InfoGeometry.Canonical.KMSSinkhornBridge
import InfoGeometry.Canonical.RGFlow

/-!
# Research.QFTTDFTLaunchpad

Constructive launchpad layer for AQFT/TDFT-oriented developments:

- AQFT side: Sinkhorn-driven KMS closure and Bogoliubov/Fock vacuum reduction.
- TDFT side: Legendre involution (density/potential duality) and RG-stationary dual map.

This file intentionally reuses existing proved objects, with no new axioms.
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

/--
AQFT closure theorem:
Sinkhorn control yields exact KMS closure at every next iterate.
-/
theorem aqft_kmsClosure_of_sinkhornControl
    (T : SinkhornTrajectory n)
    (K : AlgebraEnd F)
    (ω : Nat → AlgebraEnd F →L[ℝ] ℝ)
    (β : ℝ)
    (hControl : SinkhornKMSControl n T K ω β) :
    SinkhornKMSClosure n T K ω β :=
  sinkhorn_step_kmsClosure_of_control
    (n := n) (T := T) (K := K) (ω := ω) (β := β) hControl

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
primal gradient and dual inverse are mutually inverse.
-/
def HohenbergKohnDualState
    (_ψ : Θ → ℝ)
    (_ψStar : (Θ →L[ℝ] ℝ) → ℝ) : Prop :=
  ∃ grad : Θ → (Θ →L[ℝ] ℝ),
    ∃ gradStar : (Θ →L[ℝ] ℝ) → Θ,
      Function.LeftInverse gradStar grad ∧ Function.RightInverse gradStar grad

/--
Explicit constructive duality state:
inverse gradient maps directly yield the Hohenberg-Kohn duality witness.
-/
theorem hohenbergKohnDualState_of_inverse_maps
    (ψ : Θ → ℝ)
    (ψStar : (Θ →L[ℝ] ℝ) → ℝ)
    (grad : Θ → (Θ →L[ℝ] ℝ))
    (gradStar : (Θ →L[ℝ] ℝ) → Θ)
    (hLeft : Function.LeftInverse gradStar grad)
    (hRight : Function.RightInverse gradStar grad) :
    HohenbergKohnDualState ψ ψStar := by
  refine ⟨grad, gradStar, ?_⟩
  exact legendre_involution_of_inverse_maps (grad := grad) (gradStar := gradStar) hLeft hRight

/--
Legendre involution assumptions discharge the Hohenberg-Kohn duality state.
-/
theorem hohenbergKohnDualState_of_legendreInvolution
    (ψ : Θ → ℝ)
    (ψStar : (Θ →L[ℝ] ℝ) → ℝ)
    (hLeg : LegendreInvolutionAssumptions ψ ψStar) :
    HohenbergKohnDualState ψ ψStar := by
  exact hohenbergKohnDualState_of_inverse_maps
    (ψ := ψ) (ψStar := ψStar)
    (grad := hLeg.grad) (gradStar := hLeg.gradStar)
    hLeg.left_inv hLeg.right_inv

/--
Concrete convex/smooth Legendre hypotheses discharge the Hohenberg-Kohn duality state.
-/
theorem hohenbergKohnDualState_of_concreteLegendre
    (ψ : Θ → ℝ)
    (ψStar : (Θ →L[ℝ] ℝ) → ℝ)
    (hConcrete : LegendreConcreteHypotheses ψ ψStar) :
    HohenbergKohnDualState ψ ψStar := by
  exact hohenbergKohnDualState_of_legendreInvolution
    (ψ := ψ) (ψStar := ψStar)
    (InfoGeometry.Geometry.legendreInvolutionAssumptions_of_concrete hConcrete)

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

/--
Under Legendre involution assumptions, the Fenchel gap vanishes along `grad`.
-/
theorem fenchelGap_zero_along_grad_of_legendreInvolution
    (ψ : Θ → ℝ)
    (ψStar : (Θ →L[ℝ] ℝ) → ℝ)
    (hLeg : LegendreInvolutionAssumptions ψ ψStar) :
    ∀ θ : Θ, fenchelGap ψ ψStar θ (hLeg.grad θ) = 0 :=
  fenchelGap_zero_along_grad_of_fenchelYoung
    (ψ := ψ) (ψStar := ψStar) (grad := hLeg.grad) hLeg.fenchelYoung_along_grad

/-- Concrete convex/smooth Legendre hypotheses imply zero Fenchel gap along `fderiv`. -/
theorem fenchelGap_zero_along_fderiv_of_concreteLegendre
    (ψ : Θ → ℝ)
    (ψStar : (Θ →L[ℝ] ℝ) → ℝ)
    (hConcrete : LegendreConcreteHypotheses ψ ψStar) :
    ∀ θ : Θ, fenchelGap ψ ψStar θ (fderiv ℝ ψ θ) = 0 :=
  InfoGeometry.Geometry.LegendreConcreteHypotheses.fenchelGap_eq_zero_along_fderiv hConcrete

variable {E : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/--
Runge-Gross-style stationary dual-map state at RG fixed point.
-/
def RungeGrossStationaryDualState
    (flow : InformationFlow E)
    (scale0 : ℝ) : Prop :=
  ∀ x : E, deriv (fun t => (flow t).dualMap x) scale0 = 0

/--
RG fixed point constructively implies stationary dual-map dynamics.
-/
theorem rungeGrossStationaryDualState_of_fixedPoint
    (flow : InformationFlow E)
    (scale0 : ℝ)
    (hFixed : IsFixedPoint flow scale0) :
    RungeGrossStationaryDualState flow scale0 := by
  intro x
  exact dual_map_invariant_at_fixed_point
    (flow := flow) (scale0 := scale0) hFixed x

end TDFT

section Launchpad

variable (n : Nat)
variable {F : Type} [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]
variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
variable {Θ : Type*} [NormedAddCommGroup Θ] [NormedSpace ℝ Θ]

/--
Unified constructive launchpad:
AQFT closure + vacuum-reduced Fock step + TDFT duality and fixed-point stationarity.
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
    (hControl : SinkhornKMSControl n T K ω β)
    (hVacSplit : VacuumEinsteinOnTransportedSplit R Kgeo x scalar Λ V Γ)
    (hLeg : LegendreInvolutionAssumptions ψ ψStar)
    (hFixed : IsFixedPoint flow scale0) :
    SinkhornKMSClosure n T K ω β
      ∧ grandCanonicalFockEulerStep (E := E) η B H
          (einsteinInducedChemicalPotential (R := R) (K := Kgeo) (x := x)
            (scalar := scalar) (Λ := Λ) (V := V) (Γ := Γ)) ψ0
            = ψ0 + η • H ψ0
      ∧ HohenbergKohnDualState ψ ψStar
      ∧ RungeGrossStationaryDualState flow scale0 := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact aqft_kmsClosure_of_sinkhornControl
      (n := n) (T := T) (K := K) (ω := ω) (β := β) hControl
  · exact grandCanonicalFockEulerStep_eq_hamiltonianStep_of_vacuumTransported
      (E := E) (η := η) (B := B) (H := H)
      (R := R) (Kgeo := Kgeo) (x := x) (scalar := scalar) (Λ := Λ)
      (V := V) (Γ := Γ) (ψ := ψ0) hVacSplit
  · exact hohenbergKohnDualState_of_legendreInvolution
      (ψ := ψ) (ψStar := ψStar) hLeg
  · exact rungeGrossStationaryDualState_of_fixedPoint
      (flow := flow) (scale0 := scale0) hFixed

end Launchpad

end InfoGeometry.Canonical.QFTTDFTLaunchpad
