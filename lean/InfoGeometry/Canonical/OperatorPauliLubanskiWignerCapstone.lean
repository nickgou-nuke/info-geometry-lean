import InfoGeometry.Canonical.OperatorPauliLubanskiMassiveWigner
import InfoGeometry.Algebra.FiniteSpinAlgebra

/-!
# InfoGeometry.Canonical.OperatorPauliLubanskiWignerCapstone

Finite spin-`1/2` Wigner bifurcation on the repository-owned Pauli carrier.

The massive rest-frame branch is the `su(2)` little-group algebra.  The
massless future `+z` branch is the paired Weyl-helicity relation already owned
by `OperatorPauliLubanskiLift`.
-/

noncomputable section

namespace InfoGeometry.Canonical.OperatorPauliLubanskiWignerCapstone

open InfoGeometry.Canonical.OperatorPauliLubanskiLift
open InfoGeometry.Canonical.OperatorPauliLubanskiMassiveWigner
open InfoGeometry.Canonical.OperatorZornSpinCasimirLift
open InfoGeometry.Optics.CircularPolarizationSuperconnectionBridge

abbrev Mat2C := InfoGeometry.Algebra.FiniteSpin.Mat2C

/-- Massive finite Wigner branch: `W⁰ = 0`, `Wᵢ = mSᵢ`, `su(2)` closure,
and the spin-half second Casimir. -/
theorem massive_branch (m : ℂ) :
    pauliLubanski0 (massiveRestMomentum m) = 0 ∧
      (∀ i : Fin 3, massiveW m i = m • spinSpatial i) ∧
      (∀ i j : Fin 3,
        massiveW m i * massiveW m j - massiveW m j * massiveW m i =
          (Complex.I * m) •
            (∑ k : Fin 3, epsilon3 i j k • massiveW m k)) ∧
      pauliLubanskiSq (massiveRestMomentum m) =
        (-(3 / 4 : ℂ) * m ^ 2) • (1 : Mat2C) :=
  massive_wigner_spin_half_packet m

/-- Massless finite Wigner branch on the future `+z` null ray: positive
helicity in the left Weyl sector and negative helicity in the right Weyl
sector. -/
theorem massless_branch (E : ℂ) (mu : Fin 4) :
    pauliLubanskiComponent (nullZMomentum E) mu * circularPlus =
        (((2 : ℂ)⁻¹ * momentumComponent (nullZMomentum E) mu) • circularPlus) ∧
      rightPauliLubanskiComponent (nullZMomentum E) mu * circularMinus =
        ((-(2 : ℂ)⁻¹ * momentumComponent (nullZMomentum E) mu) • circularMinus) :=
  pauliLubanski_nullZ_helicity_packet E mu

/-- Complete finite spin-half Wigner classification packet at the algebraic
matrix level. -/
theorem finite_wigner_spin_half_packet (m E : ℂ) :
    (pauliLubanski0 (massiveRestMomentum m) = 0 ∧
      (∀ i : Fin 3, massiveW m i = m • spinSpatial i) ∧
      (∀ i j : Fin 3,
        massiveW m i * massiveW m j - massiveW m j * massiveW m i =
          (Complex.I * m) •
            (∑ k : Fin 3, epsilon3 i j k • massiveW m k)) ∧
      pauliLubanskiSq (massiveRestMomentum m) =
        (-(3 / 4 : ℂ) * m ^ 2) • (1 : Mat2C)) ∧
    (∀ mu : Fin 4,
      pauliLubanskiComponent (nullZMomentum E) mu * circularPlus =
          (((2 : ℂ)⁻¹ * momentumComponent (nullZMomentum E) mu) • circularPlus) ∧
        rightPauliLubanskiComponent (nullZMomentum E) mu * circularMinus =
          ((-(2 : ℂ)⁻¹ * momentumComponent (nullZMomentum E) mu) • circularMinus)) := by
  exact ⟨massive_branch m, fun mu => massless_branch E mu⟩

end InfoGeometry.Canonical.OperatorPauliLubanskiWignerCapstone

