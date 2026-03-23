import InfoGeometry.Geometry.LegendreDuality
import InfoGeometry.Canonical.BogoliubovFockSuper
import InfoGeometry.Canonical.KMSSinkhornBridge
import InfoGeometry.Canonical.RGFlow

/-!
# InfoGeometry.Canonical.QFTTDFTLaunchpad

Reduced constructive launchpad primitives for AQFT/TDFT-oriented developments.

This module now exposes only the primitives that still have real downstream
consumers:

- the vacuum-transported collapse of the grand-canonical Fock Euler step
- the Hohenberg-Kohn duality state predicate
- the Runge-Gross stationary dual-map state predicate and its basic stationarity witness
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
  intro x
  exact hStationary.2 x

end TDFT

end InfoGeometry.Canonical.QFTTDFTLaunchpad
