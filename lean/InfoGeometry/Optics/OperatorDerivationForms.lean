/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/

/-
InfoGeometry/Optics/OperatorDerivationForms.lean

Derivation-valued forms for the operator-polarization connection.

The existing thermo owner supplies the linear Leibniz derivation and Onsager
reciprocity contracts.  This file wires those owners into the one-form carrier
without duplicating either concept.
-/

import InfoGeometry.Geometry.BilingualAnalyticity
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Thermo.SusceptibilityOnsagerStress
import InfoGeometry.OperatorAlgebra.NoncommutativePowerDerivative
import InfoGeometry.OperatorAlgebra.PeirceSpine.Tetraktys
import InfoGeometry.Optics.OperatorValuedConnection
import InfoGeometry.NCG.DerivationDifferential
import InfoGeometry.OperatorAlgebra.NoncommutativeMaurerCartanAdjointBridge
import InfoGeometry.Lie.ContinuousDerivationExponential

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

/-- The CE curvature of the identity operator-valued one-form, evaluated on
the two directed Peirce cones, is twice their Tetraktys spin
`Σ = [N₊, N₋]`. This realizes the Peirce spin as an actual degree-two
derivation-form value in the canonical inner-derivation system. -/
theorem peirceTetraktys_spin_as_innerCE_curvature
    {B : Type*} [Ring B] (P A C : B) :
    InfoGeometry.NCG.DerivationDifferential.curvature
        InfoGeometry.NCG.DerivationDifferential.innerSystem
        (fun X : B => X)
        (InfoGeometry.OperatorAlgebra.PeirceSpine.conePlus P A)
        (InfoGeometry.OperatorAlgebra.PeirceSpine.coneMinus P C) =
      (2 : ℤ) • InfoGeometry.OperatorAlgebra.PeirceSpine.genSig P A C := by
  simpa [InfoGeometry.NCG.bracket,
    InfoGeometry.OperatorAlgebra.PeirceSpine.genSig,
    InfoGeometry.OperatorAlgebra.PeirceSpine.comm] using
      (InfoGeometry.NCG.DerivationDifferential.innerSystem_identityForm_curvature
        (D := InfoGeometry.OperatorAlgebra.PeirceSpine.conePlus P A)
        (E := InfoGeometry.OperatorAlgebra.PeirceSpine.coneMinus P C))

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

/-- The Banach exponential of a continuous Fréchet operator derivation
preserves the associative operator product. This connects the explicit
Leibniz structure in this file to the generic continuous derivation flow,
without assuming commutativity of `A`. -/
theorem flow_mul
    {A : Type*} [NormedRing A] [NormedAlgebra ℝ A] [CompleteSpace A]
    (D : FrechetOperatorDerivation ℝ A)
    (t : ℝ) (a b : A) :
    InfoGeometry.Lie.ContinuousDerivationExponential.flow
        D.toContinuousLinearMap t (a * b) =
      InfoGeometry.Lie.ContinuousDerivationExponential.flow
        D.toContinuousLinearMap t a *
      InfoGeometry.Lie.ContinuousDerivationExponential.flow
        D.toContinuousLinearMap t b := by
  exact InfoGeometry.Lie.ContinuousDerivationExponential.flow_map_mul
    (mul := ContinuousLinearMap.mul ℝ A)
    D.toContinuousLinearMap
    (by
      intro x y
      simpa [ContinuousLinearMap.mul_apply] using D.leibniz x y)
    t a b

/-- Exponential flow transports idempotents to idempotents. This is the
cut-preservation fact needed before transporting a Peirce decomposition along
an operator derivation flow. -/
theorem flow_preserves_idempotent
    {A : Type*} [NormedRing A] [NormedAlgebra ℝ A] [CompleteSpace A]
    (D : FrechetOperatorDerivation ℝ A) (t : ℝ) {P : A}
    (hP : P * P = P) :
    InfoGeometry.Lie.ContinuousDerivationExponential.flow
        D.toContinuousLinearMap t P *
      InfoGeometry.Lie.ContinuousDerivationExponential.flow
        D.toContinuousLinearMap t P =
      InfoGeometry.Lie.ContinuousDerivationExponential.flow
        D.toContinuousLinearMap t P := by
  rw [← flow_mul D t P P, hP]

/-- The exponential automorphism of a continuous operator derivation
transports the Peirce tetraktys spin, and hence its canonical
Chevalley--Eilenberg curvature, to the spin of the transported cut and
cones. This identifies the operator-flow and derivation-form descriptions
without replacing the operator algebra by commuting coordinates. -/
theorem flow_transports_peirce_tetraktys_CE_curvature
    {A : Type*} [NormedRing A] [NormedAlgebra ℝ A] [CompleteSpace A]
    (D : FrechetOperatorDerivation ℝ A) (t : ℝ) (P a c : A) :
    InfoGeometry.Lie.ContinuousDerivationExponential.flow
        D.toContinuousLinearMap t
        (InfoGeometry.NCG.DerivationDifferential.curvature
          InfoGeometry.NCG.DerivationDifferential.innerSystem
          (fun x : A => x)
          (InfoGeometry.OperatorAlgebra.PeirceSpine.conePlus P a)
          (InfoGeometry.OperatorAlgebra.PeirceSpine.coneMinus P c)) =
      InfoGeometry.NCG.DerivationDifferential.curvature
        InfoGeometry.NCG.DerivationDifferential.innerSystem
        (fun x : A => x)
        (InfoGeometry.OperatorAlgebra.PeirceSpine.conePlus
          (InfoGeometry.Lie.ContinuousDerivationExponential.flow
            D.toContinuousLinearMap t P)
          (InfoGeometry.Lie.ContinuousDerivationExponential.flow
            D.toContinuousLinearMap t a))
        (InfoGeometry.OperatorAlgebra.PeirceSpine.coneMinus
          (InfoGeometry.Lie.ContinuousDerivationExponential.flow
            D.toContinuousLinearMap t P)
          (InfoGeometry.Lie.ContinuousDerivationExponential.flow
            D.toContinuousLinearMap t c)) := by
  let φ : A →ₗ[ℝ] A :=
    (InfoGeometry.Lie.ContinuousDerivationExponential.flow
      D.toContinuousLinearMap t).toLinearMap
  have hD : InfoGeometry.Lie.ContinuousDerivationExponential.IsDerivation
      (ContinuousLinearMap.mul ℝ A) D.toContinuousLinearMap := by
    intro x y
    simpa [ContinuousLinearMap.mul_apply] using D.leibniz x y
  have hmul (x y : A) : φ (x * y) = φ x * φ y := by
    change InfoGeometry.Lie.ContinuousDerivationExponential.flow
        D.toContinuousLinearMap t (x * y) =
      InfoGeometry.Lie.ContinuousDerivationExponential.flow
        D.toContinuousLinearMap t x *
      InfoGeometry.Lie.ContinuousDerivationExponential.flow
        D.toContinuousLinearMap t y
    exact InfoGeometry.Lie.ContinuousDerivationExponential.flow_map_mul
        (mul := ContinuousLinearMap.mul ℝ A)
        D.toContinuousLinearMap hD t x y
  have hDone : D.toContinuousLinearMap 1 = 0 := by
    have h := D.leibniz (1 : A) 1
    have h' : D.toContinuousLinearMap 1 + 0 =
        D.toContinuousLinearMap 1 + D.toContinuousLinearMap 1 := by
      simpa using h
    exact (add_left_cancel h').symm
  have hφone : φ 1 = 1 := by
    change InfoGeometry.Lie.ContinuousDerivationExponential.flow
        D.toContinuousLinearMap t 1 = 1
    exact InfoGeometry.Lie.ContinuousDerivationExponential.flow_apply_eq_self_of_apply_eq_zero
      D.toContinuousLinearMap 1 hDone t
  have hφcomp (x : A) : φ (1 - x) = 1 - φ x := by
    calc
      φ (1 - x) = φ 1 - φ x := φ.map_sub 1 x
      _ = 1 - φ x := by rw [hφone]
  have hplus (x y : A) :
      φ (InfoGeometry.OperatorAlgebra.PeirceSpine.conePlus x y) =
        InfoGeometry.OperatorAlgebra.PeirceSpine.conePlus (φ x) (φ y) := by
    change φ (x * y * (1 - x)) = φ x * φ y * (1 - φ x)
    calc
      φ (x * y * (1 - x)) = φ (x * y) * φ (1 - x) := hmul (x * y) (1 - x)
      _ = (φ x * φ y) * φ (1 - x) := by rw [hmul]
      _ = φ x * φ y * (1 - φ x) := by rw [hφcomp]
  have hminus (x y : A) :
      φ (InfoGeometry.OperatorAlgebra.PeirceSpine.coneMinus x y) =
        InfoGeometry.OperatorAlgebra.PeirceSpine.coneMinus (φ x) (φ y) := by
    change φ ((1 - x) * y * x) = (1 - φ x) * φ y * φ x
    calc
      φ ((1 - x) * y * x) = φ ((1 - x) * y) * φ x := hmul ((1 - x) * y) x
      _ = (φ (1 - x) * φ y) * φ x := by rw [hmul]
      _ = ((1 - φ x) * φ y) * φ x := by rw [hφcomp]
  have hsig :
      φ (InfoGeometry.OperatorAlgebra.PeirceSpine.genSig P a c) =
        InfoGeometry.OperatorAlgebra.PeirceSpine.genSig (φ P) (φ a) (φ c) := by
    change φ
        (InfoGeometry.OperatorAlgebra.PeirceSpine.conePlus P a *
          InfoGeometry.OperatorAlgebra.PeirceSpine.coneMinus P c -
         InfoGeometry.OperatorAlgebra.PeirceSpine.coneMinus P c *
          InfoGeometry.OperatorAlgebra.PeirceSpine.conePlus P a) =
      InfoGeometry.OperatorAlgebra.PeirceSpine.conePlus (φ P) (φ a) *
          InfoGeometry.OperatorAlgebra.PeirceSpine.coneMinus (φ P) (φ c) -
        InfoGeometry.OperatorAlgebra.PeirceSpine.coneMinus (φ P) (φ c) *
          InfoGeometry.OperatorAlgebra.PeirceSpine.conePlus (φ P) (φ a)
    calc
      _ = φ (InfoGeometry.OperatorAlgebra.PeirceSpine.conePlus P a *
            InfoGeometry.OperatorAlgebra.PeirceSpine.coneMinus P c) -
          φ (InfoGeometry.OperatorAlgebra.PeirceSpine.coneMinus P c *
            InfoGeometry.OperatorAlgebra.PeirceSpine.conePlus P a) :=
        φ.map_sub _ _
      _ = φ (InfoGeometry.OperatorAlgebra.PeirceSpine.conePlus P a) *
            φ (InfoGeometry.OperatorAlgebra.PeirceSpine.coneMinus P c) -
          φ (InfoGeometry.OperatorAlgebra.PeirceSpine.coneMinus P c) *
            φ (InfoGeometry.OperatorAlgebra.PeirceSpine.conePlus P a) := by
        rw [hmul, hmul]
      _ = _ := by rw [hplus, hminus]
  calc
    InfoGeometry.Lie.ContinuousDerivationExponential.flow
        D.toContinuousLinearMap t
        (InfoGeometry.NCG.DerivationDifferential.curvature
          InfoGeometry.NCG.DerivationDifferential.innerSystem
          (fun x : A => x)
          (InfoGeometry.OperatorAlgebra.PeirceSpine.conePlus P a)
          (InfoGeometry.OperatorAlgebra.PeirceSpine.coneMinus P c)) =
        φ (InfoGeometry.NCG.DerivationDifferential.curvature
          InfoGeometry.NCG.DerivationDifferential.innerSystem
          (fun x : A => x)
          (InfoGeometry.OperatorAlgebra.PeirceSpine.conePlus P a)
          (InfoGeometry.OperatorAlgebra.PeirceSpine.coneMinus P c)) := rfl
    _ = φ ((2 : ℤ) • InfoGeometry.OperatorAlgebra.PeirceSpine.genSig P a c) := by
      rw [peirceTetraktys_spin_as_innerCE_curvature]
    _ = (2 : ℤ) • φ (InfoGeometry.OperatorAlgebra.PeirceSpine.genSig P a c) :=
      (φ : A →+ A).map_zsmul (2 : ℤ)
        (InfoGeometry.OperatorAlgebra.PeirceSpine.genSig P a c)
    _ = (2 : ℤ) • InfoGeometry.OperatorAlgebra.PeirceSpine.genSig (φ P) (φ a) (φ c) := by
      rw [hsig]
    _ = InfoGeometry.NCG.DerivationDifferential.curvature
          InfoGeometry.NCG.DerivationDifferential.innerSystem
          (fun x : A => x)
          (InfoGeometry.OperatorAlgebra.PeirceSpine.conePlus (φ P) (φ a))
          (InfoGeometry.OperatorAlgebra.PeirceSpine.coneMinus (φ P) (φ c)) := by
      rw [peirceTetraktys_spin_as_innerCE_curvature]

/-- The exponential flow transports the complete Peirce tetraktys, not just
its spin component: parity, chirality, Jordan metric, and Lie curvature are
all computed from the transported cut and directed cones. -/
theorem flow_transports_peirce_tetraktys
    {A : Type*} [NormedRing A] [NormedAlgebra ℝ A] [CompleteSpace A]
    (D : FrechetOperatorDerivation ℝ A) (t : ℝ) (P a c : A) :
    let φ := InfoGeometry.Lie.ContinuousDerivationExponential.flow
      D.toContinuousLinearMap t
    φ (InfoGeometry.OperatorAlgebra.PeirceSpine.genPhi P a c) =
        InfoGeometry.OperatorAlgebra.PeirceSpine.genPhi (φ P) (φ a) (φ c) ∧
    φ (InfoGeometry.OperatorAlgebra.PeirceSpine.genJ P a c) =
        InfoGeometry.OperatorAlgebra.PeirceSpine.genJ (φ P) (φ a) (φ c) ∧
    φ (InfoGeometry.OperatorAlgebra.PeirceSpine.genV P a c) =
        InfoGeometry.OperatorAlgebra.PeirceSpine.genV (φ P) (φ a) (φ c) ∧
    φ (InfoGeometry.OperatorAlgebra.PeirceSpine.genSig P a c) =
        InfoGeometry.OperatorAlgebra.PeirceSpine.genSig (φ P) (φ a) (φ c) := by
  dsimp
  let φ : A →ₗ[ℝ] A :=
    (InfoGeometry.Lie.ContinuousDerivationExponential.flow
      D.toContinuousLinearMap t).toLinearMap
  have hD : InfoGeometry.Lie.ContinuousDerivationExponential.IsDerivation
      (ContinuousLinearMap.mul ℝ A) D.toContinuousLinearMap := by
    intro x y
    simpa [ContinuousLinearMap.mul_apply] using D.leibniz x y
  have hmul (x y : A) : φ (x * y) = φ x * φ y := by
    change InfoGeometry.Lie.ContinuousDerivationExponential.flow
        D.toContinuousLinearMap t (x * y) =
      InfoGeometry.Lie.ContinuousDerivationExponential.flow
        D.toContinuousLinearMap t x *
      InfoGeometry.Lie.ContinuousDerivationExponential.flow
        D.toContinuousLinearMap t y
    exact InfoGeometry.Lie.ContinuousDerivationExponential.flow_map_mul
      (mul := ContinuousLinearMap.mul ℝ A) D.toContinuousLinearMap hD t x y
  have hplus (x y : A) :
      φ (InfoGeometry.OperatorAlgebra.PeirceSpine.conePlus x y) =
        InfoGeometry.OperatorAlgebra.PeirceSpine.conePlus (φ x) (φ y) := by
    change φ (x * y * (1 - x)) = φ x * φ y * (1 - φ x)
    calc
      φ (x * y * (1 - x)) = φ (x * y) * φ (1 - x) := hmul (x * y) (1 - x)
      _ = φ x * φ y * φ (1 - x) := by rw [hmul]
      _ = φ x * φ y * (1 - φ x) := by rw [φ.map_sub, show φ 1 = 1 by
        change InfoGeometry.Lie.ContinuousDerivationExponential.flow
          D.toContinuousLinearMap t 1 = 1
        exact InfoGeometry.Lie.ContinuousDerivationExponential.flow_apply_eq_self_of_apply_eq_zero
          D.toContinuousLinearMap 1 (by
            have h := D.leibniz (1 : A) 1
            have h' : D.toContinuousLinearMap 1 + 0 =
                D.toContinuousLinearMap 1 + D.toContinuousLinearMap 1 := by simpa using h
            exact (add_left_cancel h').symm) t]
  have hminus (x y : A) :
      φ (InfoGeometry.OperatorAlgebra.PeirceSpine.coneMinus x y) =
        InfoGeometry.OperatorAlgebra.PeirceSpine.coneMinus (φ x) (φ y) := by
    change φ ((1 - x) * y * x) = (1 - φ x) * φ y * φ x
    calc
      φ ((1 - x) * y * x) = φ ((1 - x) * y) * φ x := hmul ((1 - x) * y) x
      _ = φ (1 - x) * φ y * φ x := by rw [hmul]
      _ = (1 - φ x) * φ y * φ x := by rw [φ.map_sub, show φ 1 = 1 by
        change InfoGeometry.Lie.ContinuousDerivationExponential.flow
          D.toContinuousLinearMap t 1 = 1
        exact InfoGeometry.Lie.ContinuousDerivationExponential.flow_apply_eq_self_of_apply_eq_zero
          D.toContinuousLinearMap 1 (by
            have h := D.leibniz (1 : A) 1
            have h' : D.toContinuousLinearMap 1 + 0 =
                D.toContinuousLinearMap 1 + D.toContinuousLinearMap 1 := by simpa using h
            exact (add_left_cancel h').symm) t]
  refine ⟨?_, ?_, ?_, ?_⟩
  · change φ (InfoGeometry.OperatorAlgebra.PeirceSpine.conePlus P a +
      InfoGeometry.OperatorAlgebra.PeirceSpine.coneMinus P c) =
        InfoGeometry.OperatorAlgebra.PeirceSpine.conePlus (φ P) (φ a) +
          InfoGeometry.OperatorAlgebra.PeirceSpine.coneMinus (φ P) (φ c)
    rw [φ.map_add, hplus, hminus]
  · change φ (InfoGeometry.OperatorAlgebra.PeirceSpine.conePlus P a -
      InfoGeometry.OperatorAlgebra.PeirceSpine.coneMinus P c) =
        InfoGeometry.OperatorAlgebra.PeirceSpine.conePlus (φ P) (φ a) -
          InfoGeometry.OperatorAlgebra.PeirceSpine.coneMinus (φ P) (φ c)
    rw [φ.map_sub, hplus, hminus]
  · change φ (InfoGeometry.OperatorAlgebra.PeirceSpine.conePlus P a *
      InfoGeometry.OperatorAlgebra.PeirceSpine.coneMinus P c +
      InfoGeometry.OperatorAlgebra.PeirceSpine.coneMinus P c *
        InfoGeometry.OperatorAlgebra.PeirceSpine.conePlus P a) =
      InfoGeometry.OperatorAlgebra.PeirceSpine.conePlus (φ P) (φ a) *
        InfoGeometry.OperatorAlgebra.PeirceSpine.coneMinus (φ P) (φ c) +
      InfoGeometry.OperatorAlgebra.PeirceSpine.coneMinus (φ P) (φ c) *
        InfoGeometry.OperatorAlgebra.PeirceSpine.conePlus (φ P) (φ a)
    rw [φ.map_add, hmul, hmul, hplus, hminus]
  · change φ (InfoGeometry.OperatorAlgebra.PeirceSpine.conePlus P a *
      InfoGeometry.OperatorAlgebra.PeirceSpine.coneMinus P c -
      InfoGeometry.OperatorAlgebra.PeirceSpine.coneMinus P c *
        InfoGeometry.OperatorAlgebra.PeirceSpine.conePlus P a) =
      InfoGeometry.OperatorAlgebra.PeirceSpine.conePlus (φ P) (φ a) *
        InfoGeometry.OperatorAlgebra.PeirceSpine.coneMinus (φ P) (φ c) -
      InfoGeometry.OperatorAlgebra.PeirceSpine.coneMinus (φ P) (φ c) *
        InfoGeometry.OperatorAlgebra.PeirceSpine.conePlus (φ P) (φ a)
    rw [φ.map_sub, hmul, hmul, hplus, hminus]

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

/-- The commutator of two continuous operator derivations is again a
continuous operator derivation.  This is the Lie-algebra operation needed
for derivation-based (Chevalley--Eilenberg) forms. -/
noncomputable def commutator
    (D E : FrechetOperatorDerivation 𝕜 A) :
    FrechetOperatorDerivation 𝕜 A where
  toContinuousLinearMap :=
    D.toContinuousLinearMap.comp E.toContinuousLinearMap -
      E.toContinuousLinearMap.comp D.toContinuousLinearMap
  leibniz := by
    intro a b
    change D (E (a * b)) - E (D (a * b)) = _
    simp only [D.leibniz, E.leibniz,
      D.toContinuousLinearMap.map_add, E.toContinuousLinearMap.map_add,
      ContinuousLinearMap.sub_apply, ContinuousLinearMap.comp_apply]
    noncomm_ring

@[simp] theorem commutator_apply
    (D E : FrechetOperatorDerivation 𝕜 A) (a : A) :
    commutator D E a = D (E a) - E (D a) :=
  rfl

theorem commutator_leibniz
    (D E : FrechetOperatorDerivation 𝕜 A) (a b : A) :
    commutator D E (a * b) =
      commutator D E a * b + a * commutator D E b :=
  (commutator D E).leibniz a b

end FrechetOperatorDerivation

namespace FrechetOperatorDerivation

open InfoGeometry.NCG.Calculus
open InfoGeometry.OperatorAlgebra.NoncommutativeMaurerCartanAdjointBridge

variable {A : Type*} [NormedRing A] [NormedAlgebra ℝ A]

/-- The canonical associative inner derivation is a continuous operator
derivation, using the existing left/right multiplier construction. -/
def ofInner (a : A) [CompleteSpace A] :
    FrechetOperatorDerivation ℝ A where
  toContinuousLinearMap := adCLM a
  leibniz := adCLM_leibniz a

@[simp] theorem ofInner_apply (a x : A) [CompleteSpace A] :
    ofInner a x = a * x - x * a :=
  rfl

/-- Forget the real scalar continuity structure and retain the underlying
integer-linear Leibniz derivation used by the canonical CE calculus. -/
noncomputable def toNCDerivation
    {A : Type*} [NormedRing A] [NormedAlgebra ℝ A]
    (D : FrechetOperatorDerivation ℝ A) : NCDerivation A where
  toLinearMap := D.toContinuousLinearMap.toLinearMap.restrictScalars ℤ
  leibniz' := by
    intro a b
    exact D.leibniz a b

@[simp] theorem toNCDerivation_apply
    {A : Type*} [NormedRing A] [NormedAlgebra ℝ A]
    (D : FrechetOperatorDerivation ℝ A) (a : A) :
    toNCDerivation D a = D a :=
  rfl

theorem toNCDerivation_ofInner_apply (a x : A) [CompleteSpace A] :
    toNCDerivation (ofInner a) x =
      InfoGeometry.NCG.DerivationDifferential.innerDerivation a x :=
  rfl

theorem toNCDerivation_ofInner (a : A) [CompleteSpace A] :
    toNCDerivation (ofInner a) =
      InfoGeometry.NCG.DerivationDifferential.innerDerivation a := by
  apply InfoGeometry.NCG.Calculus.NCDerivation.ext
  intro x
  exact toNCDerivation_ofInner_apply a x

theorem toNCDerivation_ofInner_commutator
    (a b : A) [CompleteSpace A] :
    toNCDerivation (commutator (ofInner a) (ofInner b)) =
      toNCDerivation (ofInner (a * b - b * a)) := by
  apply InfoGeometry.NCG.Calculus.NCDerivation.ext
  intro x
  simp only [toNCDerivation_apply, commutator_apply, ofInner_apply]
  noncomm_ring

theorem toNCDerivation_leibniz
    {A : Type*} [NormedRing A] [NormedAlgebra ℝ A]
    (D : FrechetOperatorDerivation ℝ A) (a b : A) :
    toNCDerivation D (a * b) =
      toNCDerivation D a * b + a * toNCDerivation D b :=
  (toNCDerivation D).leibniz a b

/-- The adapter preserves the Lie action pointwise.  This is the
commutator compatibility needed when a continuous derivation family is fed
to the canonical derivation-form calculus. -/
@[simp] theorem toNCDerivation_commutator_apply
    {A : Type*} [NormedRing A] [NormedAlgebra ℝ A]
    (D E : FrechetOperatorDerivation ℝ A) (a : A) :
    toNCDerivation (commutator D E) a =
      toNCDerivation D (toNCDerivation E a) -
        toNCDerivation E (toNCDerivation D a) := by
  simp [commutator_apply, toNCDerivation_apply]

end FrechetOperatorDerivation

namespace FrechetOperatorDerivation

open InfoGeometry.NCG.Calculus

noncomputable def toDerivationDifferentialSystem
    {A 𝔤 : Type*} [NormedRing A] [NormedAlgebra ℝ A] [AddGroup 𝔤]
    (derivation : 𝔤 → FrechetOperatorDerivation ℝ A)
    (bracket : 𝔤 → 𝔤 → 𝔤)
    (hbracket : ∀ D E a,
      derivation D (derivation E a) - derivation E (derivation D a) =
        derivation (bracket D E) a) :
    InfoGeometry.NCG.DerivationDifferential.System A 𝔤 where
  derivation := fun D => toNCDerivation (derivation D)
  bracket := bracket
  bracket_action := by
    intro D E a
    simpa only [toNCDerivation_apply] using hbracket D E a

@[simp] theorem toDerivationDifferentialSystem_derivation_apply
    {A 𝔤 : Type*} [NormedRing A] [NormedAlgebra ℝ A] [AddGroup 𝔤]
    (derivation : 𝔤 → FrechetOperatorDerivation ℝ A)
    (bracket : 𝔤 → 𝔤 → 𝔤)
    (hbracket : ∀ D E a,
      derivation D (derivation E a) - derivation E (derivation D a) =
        derivation (bracket D E) a)
    (D : 𝔤) (a : A) :
    (toDerivationDifferentialSystem derivation bracket hbracket).derivation D a =
      derivation D a := rfl

noncomputable def innerFrechetSystem
    (A : Type*) [NormedRing A] [NormedAlgebra ℝ A] [CompleteSpace A] :
    InfoGeometry.NCG.DerivationDifferential.System A A :=
  toDerivationDifferentialSystem
    (fun a : A => ofInner a)
    (fun a b : A => a * b - b * a)
    (by
      intro a b x
      simp only [ofInner_apply]
      noncomm_ring)

theorem innerFrechetSystem_covariant_curvature
    (A : Type*) [NormedRing A] [NormedAlgebra ℝ A] [CompleteSpace A]
    (Γ : A → A) (a D E : A) :
    InfoGeometry.NCG.DerivationDifferential.covariant
        (innerFrechetSystem A) Γ D
        (InfoGeometry.NCG.DerivationDifferential.covariant
          (innerFrechetSystem A) Γ E a) -
      InfoGeometry.NCG.DerivationDifferential.covariant
        (innerFrechetSystem A) Γ E
        (InfoGeometry.NCG.DerivationDifferential.covariant
          (innerFrechetSystem A) Γ D a) -
      InfoGeometry.NCG.DerivationDifferential.covariant
        (innerFrechetSystem A) Γ (D * E - E * D) a =
      InfoGeometry.NCG.DerivationDifferential.curvature
        (innerFrechetSystem A) Γ D E * a -
        a * InfoGeometry.NCG.DerivationDifferential.curvature
          (innerFrechetSystem A) Γ D E := by
  exact InfoGeometry.NCG.DerivationDifferential.covariant_commutator_sub_bracket
    (innerFrechetSystem A) Γ a D E

end FrechetOperatorDerivation

section FiniteDimensional

variable {A : Type*} [NormedRing A] [NormedAlgebra ℝ A]
variable [FiniteDimensional ℝ A]

/-- Continuous realization of a finite-dimensional real-linear Leibniz map.
This is the canonical constructor for transporting algebraic derivations into
the operator/Frechet layer. -/
noncomputable def frechetOperatorDerivationOfLinear
    (D : A →ₗ[ℝ] A)
    (hD : ∀ a b, D (a * b) = D a * b + a * D b) :
    FrechetOperatorDerivation ℝ A where
  toContinuousLinearMap := D.toContinuousLinearMap
  leibniz := hD

@[simp] theorem frechetOperatorDerivationOfLinear_apply
    (D : A →ₗ[ℝ] A)
    (hD : ∀ a b, D (a * b) = D a * b + a * D b) (a : A) :
    frechetOperatorDerivationOfLinear D hD a = D a :=
  rfl

theorem frechetOperatorDerivationOfLinear_hasFDerivAt
    (D : A →ₗ[ℝ] A)
    (hD : ∀ a b, D (a * b) = D a * b + a * D b) (a : A) :
    HasFDerivAt D
      (frechetOperatorDerivationOfLinear D hD).toContinuousLinearMap a := by
  rw [← LinearMap.coe_toContinuousLinearMap' D]
  exact ContinuousLinearMap.hasFDerivAt (LinearMap.toContinuousLinearMap D)

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
  rw [← LinearMap.coe_toContinuousLinearMap' D.toLinearMap]
  exact ContinuousLinearMap.hasFDerivAt (LinearMap.toContinuousLinearMap D.toLinearMap)

end FiniteDimensional

end InfoGeometry.Optics.OperatorDerivationForms
