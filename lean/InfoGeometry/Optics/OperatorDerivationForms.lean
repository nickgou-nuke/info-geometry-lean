/-
InfoGeometry/Optics/OperatorDerivationForms.lean

Derivation-valued forms for the operator-polarization connection.

The existing thermo owner supplies the linear Leibniz derivation and Onsager
reciprocity contracts.  This file wires those owners into the one-form carrier
without duplicating either concept.
-/

import InfoGeometry.Geometry.BilingualAnalyticity
import InfoGeometry.Thermo.SusceptibilityOnsagerStress
import InfoGeometry.OperatorAlgebra.NoncommutativePowerDerivative

noncomputable section

namespace InfoGeometry.Optics.OperatorDerivationForms

open InfoGeometry.Geometry.BilingualAnalyticity
open InfoGeometry.Thermo.SusceptibilityOnsagerStress

variable {Point Tangent Value : Type*}
variable [Ring Value] [Algebra ℝ Value]

/-- A finite family of operator-valued one-forms. -/
abbrev NOperatorForm (n : ℕ) : Type _ :=
  Fin n → OperatorOneForm Point Tangent Value

/-- A pointwise family of product-rule operator derivations. -/
abbrev DerivationField : Type _ :=
  Point → ThermodynamicOperatorDerivation Value

/-- Apply a derivation field to the values of a one-form. -/
def applyDerivationField
    (D : DerivationField (Point := Point) (Value := Value))
    (ω : OperatorOneForm Point Tangent Value) :
    OperatorOneForm Point Tangent Value :=
  fun p X => D p (ω p X)

@[simp]
theorem applyDerivationField_mul
    (D : DerivationField (Point := Point) (Value := Value))
    (ω ν : OperatorOneForm Point Tangent Value)
    (p : Point) (X : Tangent) :
    D p (ω p X * ν p X) =
      D p (ω p X) * ν p X + ω p X * D p (ν p X) :=
  (D p).map_mul (ω p X) (ν p X)

/-- The Onsager response contract already owned by the thermo subsystem. -/
abbrev OnsagerForm : Type _ := OnsagerTwoOperatorForm Value

/-- A Frechet derivative operator, when the value algebra is normed. -/
abbrev FrechetDerivation (𝕜 : Type*) (A : Type*) [NontriviallyNormedField 𝕜]
    [NormedRing A] [NormedAlgebra 𝕜 A] :=
  A →L[𝕜] A

/-- The canonical noncommutative power derivative from the existing owner. -/
abbrev powerFrechetDerivation
    {𝕜 A : Type*} [NontriviallyNormedField 𝕜]
    [NormedRing A] [NormedAlgebra 𝕜 A]
    (n : ℕ) (a : A) : FrechetDerivation 𝕜 A :=
  InfoGeometry.OperatorAlgebra.powerDerivative n a

theorem powerFrechetDerivation_is_derivative
    {𝕜 A : Type*} [NontriviallyNormedField 𝕜]
    [NormedRing A] [NormedAlgebra 𝕜 A]
    (n : ℕ) (a : A) :
    HasFDerivAt (fun x : A => x ^ n)
      (powerFrechetDerivation (𝕜 := 𝕜) n a) a :=
  InfoGeometry.OperatorAlgebra.hasFDerivAt_power_noncommutative n a

end InfoGeometry.Optics.OperatorDerivationForms
