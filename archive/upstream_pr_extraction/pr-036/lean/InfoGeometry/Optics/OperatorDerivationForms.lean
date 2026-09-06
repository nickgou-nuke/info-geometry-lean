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
import InfoGeometry.Optics.OperatorValuedConnection

noncomputable section

namespace InfoGeometry.Optics.OperatorDerivationForms

open InfoGeometry.Geometry.BilingualAnalyticity
open InfoGeometry.Thermo.SusceptibilityOnsagerStress
open InfoGeometry.Optics.OperatorValuedConnection

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

theorem applyDerivationField_wedgeSquare
    (D : DerivationField (Point := Point) (Value := Value))
    (ω : OperatorOneForm Point Tangent Value)
    (p : Point) (X Y : Tangent) :
    D p (wedgeSquare ω p X Y) =
      (D p (ω p X) * ω p Y + ω p X * D p (ω p Y)) -
        (D p (ω p Y) * ω p X + ω p Y * D p (ω p X)) := by
  unfold wedgeSquare
  rw [(D p).toLinearMap.map_sub, (D p).map_mul, (D p).map_mul]

theorem applyDerivationField_curvature
    (D : DerivationField (Point := Point) (Value := Value))
    (C : Connection (Point := Point) (Tangent := Tangent) (Value := Value))
    (p : Point) (X Y : Tangent) :
    D p (curvature C p X Y) =
      D p (C.derivative p X Y) +
        ((D p (C.form p X) * C.form p Y +
            C.form p X * D p (C.form p Y)) -
          (D p (C.form p Y) * C.form p X +
            C.form p Y * D p (C.form p X))) := by
  unfold curvature
  rw [(D p).toLinearMap.map_add]
  rw [applyDerivationField_wedgeSquare]

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

/-! ## Continuous Leibniz derivations -/

/-- A noncommutative Fréchet derivation: a native continuous linear map
together with the Leibniz law.  Mathlib's `Derivation` is reserved for a
commutative coefficient algebra, so the operator-algebra case must retain the
product rule explicitly. -/
structure FrechetOperatorDerivation
    (𝕜 A : Type*) [NontriviallyNormedField 𝕜]
    [NormedRing A] [NormedAlgebra 𝕜 A] where
  toContinuousLinearMap : A →L[𝕜] A
  leibniz : ∀ a b, toContinuousLinearMap (a * b) =
    toContinuousLinearMap a * b + a * toContinuousLinearMap b

namespace FrechetOperatorDerivation

variable {𝕜 A : Type*} [NontriviallyNormedField 𝕜]
variable [NormedRing A] [NormedAlgebra 𝕜 A]

instance : CoeFun (FrechetOperatorDerivation 𝕜 A) (fun _ => A → A) :=
  ⟨fun D => D.toContinuousLinearMap⟩

@[simp] theorem map_add (D : FrechetOperatorDerivation 𝕜 A) (a b : A) :
    D (a + b) = D a + D b :=
  D.toContinuousLinearMap.map_add a b

@[simp] theorem map_smul (D : FrechetOperatorDerivation 𝕜 A)
    (c : 𝕜) (a : A) :
    D (c • a) = c • D a :=
  D.toContinuousLinearMap.map_smul c a

/-- The continuous linear representative is the Fréchet derivative at every
point because the derivation itself is linear. -/
theorem hasFDerivAt (D : FrechetOperatorDerivation 𝕜 A) (a : A) :
    HasFDerivAt D D.toContinuousLinearMap a :=
  D.toContinuousLinearMap.hasFDerivAt

/-- A Fréchet derivation differentiates the full noncommutative curvature
two-operator form by the product rule in both wedge terms. -/
theorem map_curvature
    {Point Tangent : Type*}
    (D : FrechetOperatorDerivation 𝕜 A)
    (C : Connection (Point := Point) (Tangent := Tangent) (Value := A))
    (p : Point) (X Y : Tangent) :
    D (curvature C p X Y) =
      D (C.derivative p X Y) +
        ((D (C.form p X) * C.form p Y + C.form p X * D (C.form p Y)) -
          (D (C.form p Y) * C.form p X + C.form p Y * D (C.form p X))) := by
  unfold curvature wedgeSquare
  rw [D.toContinuousLinearMap.map_add, D.toContinuousLinearMap.map_sub,
    D.leibniz, D.leibniz]

end FrechetOperatorDerivation

section FiniteDimensional

variable {A : Type*} [NormedRing A] [NormedAlgebra ℝ A]
variable [FiniteDimensional ℝ A]

/-- On a finite-dimensional operator algebra, every thermodynamic linear
Leibniz derivation has a canonical continuous Fréchet realization. -/
noncomputable def frechetOperatorDerivationOfThermodynamic
    (D : ThermodynamicOperatorDerivation A) :
    FrechetOperatorDerivation ℝ A where
  toContinuousLinearMap := LinearMap.toContinuousLinearMap D.toLinearMap
  leibniz := D.map_mul

@[simp] theorem frechetOperatorDerivationOfThermodynamic_apply
    (D : ThermodynamicOperatorDerivation A) (a : A) :
    frechetOperatorDerivationOfThermodynamic D a = D a :=
  rfl

theorem frechetOperatorDerivationOfThermodynamic_hasFDerivAt
    (D : ThermodynamicOperatorDerivation A) (a : A) :
    HasFDerivAt D
      (frechetOperatorDerivationOfThermodynamic D).toContinuousLinearMap a := by
  simpa only [frechetOperatorDerivationOfThermodynamic_apply] using
    (frechetOperatorDerivationOfThermodynamic D).hasFDerivAt a

end FiniteDimensional

end InfoGeometry.Optics.OperatorDerivationForms
