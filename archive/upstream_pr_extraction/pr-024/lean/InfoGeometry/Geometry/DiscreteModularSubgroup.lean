/-
InfoGeometry/Geometry/DiscreteModularSubgroup.lean

Discrete modular subgroup inside the phase-linear operator Mobius algebra.

This module defines the arithmetic `SL(2, Z)` coefficient data and its
operator realization by scalar multiples of the identity endomorphism on the
doubled Krein carrier.

It introduces the modular generators

  T : Z ↦ Z + 1
  S : Z ↦ -Z⁻¹

as operator Mobius coefficient systems.

This file deliberately does not define modular forms. Automorphic forms need
the metric, growth, cusp, and automorphy-factor APIs.
-/

import Mathlib
import InfoGeometry.Geometry.BilingualPoincareMetric

noncomputable section

namespace InfoGeometry.Geometry

open scoped InnerProductSpace

open InfoGeometry.Krein
open InfoGeometry.Canonical.TomitaTakesaki
open InfoGeometry.Quantum

variable {E : Type}
variable [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

local notation "EndH" => DoubledEnd E

namespace BilingualUpperHalfPlane

variable {D : ProjectivePolarizedBigradedBogoliubovDatum (E := E)}

/-! ## Integer scalar endomorphisms -/

/--
Integer scalar multiplication, realized as a real scalar multiple of the
identity endomorphism on the doubled carrier.
-/
def intScalarEnd (n : ℤ) : EndH :=
  (n : ℝ) • (1 : EndH)

/--
Integer scalar endomorphisms commute with the Hestenes phase axis.
-/
theorem intScalarEnd_phaseLinear
    (n : ℤ) :
    PhaseLinear D (intScalarEnd (E := E) n) := by
  dsimp [intScalarEnd]
  exact PhaseLinear.smul (D := D) (n : ℝ) (PhaseLinear.one (D := D))

omit [CompleteSpace E] in
@[simp]
theorem intScalarEnd_zero :
    intScalarEnd (E := E) 0 = (0 : EndH) := by
  apply ContinuousLinearMap.ext
  intro v
  simp [intScalarEnd]

omit [CompleteSpace E] in
@[simp]
theorem intScalarEnd_one :
    intScalarEnd (E := E) 1 = (1 : EndH) := by
  apply ContinuousLinearMap.ext
  intro v
  simp [intScalarEnd]

omit [CompleteSpace E] in
@[simp]
theorem intScalarEnd_neg_one :
    intScalarEnd (E := E) (-1) = (-1 : EndH) := by
  apply ContinuousLinearMap.ext
  intro v
  simp [intScalarEnd]

/-! ## Arithmetic `SL(2, Z)` coefficient matrices -/

/--
A bare arithmetic `SL(2, Z)` matrix.

The determinant condition is

`a*d - b*c = 1`.
-/
structure ModularMatrix where
  a : ℤ
  b : ℤ
  c : ℤ
  d : ℤ
  det_eq_one : a * d - b * c = 1

namespace ModularMatrix

/--
The translation generator

`T = [[1, 1], [0, 1]]`.

Classically, `T • z = z + 1`.
-/
def T : ModularMatrix where
  a := 1
  b := 1
  c := 0
  d := 1
  det_eq_one := by norm_num

/--
The inversion generator

`S = [[0, -1], [1, 0]]`.

Classically, `S • z = -1 / z`.
-/
def S : ModularMatrix where
  a := 0
  b := -1
  c := 1
  d := 0
  det_eq_one := by norm_num

@[simp] theorem T_a : T.a = 1 := rfl
@[simp] theorem T_b : T.b = 1 := rfl
@[simp] theorem T_c : T.c = 0 := rfl
@[simp] theorem T_d : T.d = 1 := rfl

@[simp] theorem S_a : S.a = 0 := rfl
@[simp] theorem S_b : S.b = -1 := rfl
@[simp] theorem S_c : S.c = 1 := rfl
@[simp] theorem S_d : S.d = 0 := rfl

/--
Realize an arithmetic modular matrix as phase-linear operator Mobius
coefficients by multiplying the identity endomorphism by the integer entries.
-/
def toMobiusCoefficients
    (γ : ModularMatrix)
    {D : ProjectivePolarizedBigradedBogoliubovDatum (E := E)} :
    PhaseLinearMobiusCoefficients D where
  A := intScalarEnd (E := E) γ.a
  B := intScalarEnd (E := E) γ.b
  C := intScalarEnd (E := E) γ.c
  Dop := intScalarEnd (E := E) γ.d

  A_phase := intScalarEnd_phaseLinear (D := D) γ.a
  B_phase := intScalarEnd_phaseLinear (D := D) γ.b
  C_phase := intScalarEnd_phaseLinear (D := D) γ.c
  D_phase := intScalarEnd_phaseLinear (D := D) γ.d

/--
Operator coefficients for the translation generator.
-/
abbrev T_coefficients
    {D : ProjectivePolarizedBigradedBogoliubovDatum (E := E)} :
    PhaseLinearMobiusCoefficients D :=
  T.toMobiusCoefficients (D := D)

/--
Operator coefficients for the inversion generator.
-/
abbrev S_coefficients
    {D : ProjectivePolarizedBigradedBogoliubovDatum (E := E)} :
    PhaseLinearMobiusCoefficients D :=
  S.toMobiusCoefficients (D := D)

end ModularMatrix

/-! ## Automorphy denominator / factor -/

/--
The operator automorphy denominator attached to a modular matrix:

`j(γ, Z) = C τ + D`.

This is the coordinate-free replacement for the scalar factor `cz + d`.
-/
def modularAutomorphyFactor
    (γ : ModularMatrix)
    (Z : BilingualUpperHalfPlane D) : EndH :=
  mobiusDenominator (γ.toMobiusCoefficients (D := D)) Z

/--
The modular automorphy factor is phase-linear.
-/
theorem modularAutomorphyFactor_phaseLinear
    (γ : ModularMatrix)
    (Z : BilingualUpperHalfPlane D) :
    PhaseLinear D (modularAutomorphyFactor γ Z) := by
  dsimp [modularAutomorphyFactor]
  exact mobiusDenominator_phaseLinear
    (γ.toMobiusCoefficients (D := D)) Z

/--
For `T`, the automorphy denominator is the identity:

`j(T, Z) = 1`.
-/
@[simp]
theorem modularAutomorphyFactor_T
    (Z : BilingualUpperHalfPlane D) :
    modularAutomorphyFactor ModularMatrix.T Z = (1 : EndH) := by
  apply ContinuousLinearMap.ext
  intro v
  simp [
    modularAutomorphyFactor,
    ModularMatrix.toMobiusCoefficients,
    mobiusDenominator,
    intScalarEnd
  ]

/--
For `S`, the automorphy denominator is `τ`:

`j(S, Z) = τ`.
-/
@[simp]
theorem modularAutomorphyFactor_S
    (Z : BilingualUpperHalfPlane D) :
    modularAutomorphyFactor ModularMatrix.S Z = Z.tau := by
  apply ContinuousLinearMap.ext
  intro v
  simp [
    modularAutomorphyFactor,
    ModularMatrix.toMobiusCoefficients,
    mobiusDenominator,
    intScalarEnd
  ]

/-! ## Modular action data -/

/--
A proof-carrying datum allowing a modular matrix to act at a point.

This packages the two facts needed before the raw fractional-linear operator
can be upgraded to an actual point of the bilingual upper half-plane:

1. the denominator has a bounded inverse;
2. the transformed operator satisfies the `K`-positivity condition.
-/
structure ModularActionDatum
    (γ : ModularMatrix)
    (Z : BilingualUpperHalfPlane D) where
  denominator_inverse :
    MobiusDenominatorInverse
      (γ.toMobiusCoefficients (D := D)) Z

  positivity :
    KHalfPlanePositive D
      (moebiusActionOperator
        (γ.toMobiusCoefficients (D := D))
        Z
        denominator_inverse)

/--
The modular action as a proof-carrying Mobius action.
-/
def modularAction
    (γ : ModularMatrix)
    (Z : BilingualUpperHalfPlane D)
    (h : ModularActionDatum γ Z) :
    BilingualUpperHalfPlane D :=
  moebiusAction
    (γ.toMobiusCoefficients (D := D))
    Z
    h.denominator_inverse
    h.positivity

/--
The translation action datum owner target.

In the scalar model this is automatic: `T • z = z + 1`.
In the operator model, the positivity proof normally uses skewness of `K`
against the identity direction, e.g. `⟪v, K v⟫ = 0`.
-/
def ModularTActionOwnerTarget
    (D : ProjectivePolarizedBigradedBogoliubovDatum (E := E)) : Prop :=
  ∀ Z : BilingualUpperHalfPlane D,
    ∃ hDen :
      MobiusDenominatorInverse
        (ModularMatrix.T.toMobiusCoefficients (D := D)) Z,
      KHalfPlanePositive D
        (moebiusActionOperator
          (ModularMatrix.T.toMobiusCoefficients (D := D))
          Z
          hDen)

/--
The inversion action datum owner target.

In the scalar model this is automatic because `z ≠ 0` on the upper half-plane.
In the operator model, strict positivity gives strong injectivity evidence, but
bounded inverse data must still be supplied or proved.
-/
def ModularSActionOwnerTarget
    (D : ProjectivePolarizedBigradedBogoliubovDatum (E := E)) : Prop :=
  ∀ Z : BilingualUpperHalfPlane D,
    ∃ hDen :
      MobiusDenominatorInverse
        (ModularMatrix.S.toMobiusCoefficients (D := D)) Z,
      KHalfPlanePositive D
        (moebiusActionOperator
          (ModularMatrix.S.toMobiusCoefficients (D := D))
          Z
          hDen)

/--
Owner target for the full discrete modular action.
-/
def DiscreteModularActionOwnerTarget
    (D : ProjectivePolarizedBigradedBogoliubovDatum (E := E)) : Prop :=
  ∀ (γ : ModularMatrix) (Z : BilingualUpperHalfPlane D),
    ∃ hDen :
      MobiusDenominatorInverse
        (γ.toMobiusCoefficients (D := D)) Z,
      KHalfPlanePositive D
        (moebiusActionOperator
          (γ.toMobiusCoefficients (D := D))
          Z
          hDen)

end BilingualUpperHalfPlane

end InfoGeometry.Geometry
