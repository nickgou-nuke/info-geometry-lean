import InfoGeometry.Geometry.LegendreDuality
import InfoGeometry.Canonical.RGFlow

/-!
# InfoGeometry.Canonical.QFTTDFTLaunchpad

Reduced constructive launchpad primitives for AQFT/TDFT-oriented developments.

This module now exposes only the primitives that still have real downstream
consumers:

- the Hohenberg-Kohn duality state predicate
- the Runge-Gross stationary dual-map state predicate and its basic stationarity property
-/

namespace InfoGeometry.Canonical.QFTTDFTLaunchpad

open InfoGeometry.Geometry
open RGFlow


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
