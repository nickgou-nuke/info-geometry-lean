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
import InfoGeometry.Core.PeirceDecomposition
import InfoGeometry.Optics.OperatorValuedConnection
import InfoGeometry.NCG.DerivationDifferential
import InfoGeometry.OperatorAlgebra.NoncommutativeMaurerCartanAdjointBridge
import InfoGeometry.Lie.ContinuousDerivationExponential
import InfoGeometry.OperatorAlgebra.DerivationExteriorCalculus
import InfoGeometry.OperatorAlgebra.OperatorExteriorAlgebraGeneral

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

/-- Ordered `n`-tuple of pointwise operator-valued one-forms (`Point → Tangent → Value`).
Canonical disambiguating alias for `NOperatorForm`: for `n ≥ 2`, `OneFormTuple`
is a `Fin n`-indexed tuple of 1-forms, **not** an alternating `n`-form (`OpForm`,
`ActionOperatorForm`, `DerivationOperatorForm`, `OperatorFrechetForm`). -/
abbrev OneFormTuple (Point Tangent Value : Type*) (n : ℕ) : Type _ :=
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

/-- The derivative of an idempotent cut lies entirely in its two
off-diagonal Peirce corners. This is the infinitesimal tangent constraint
behind the finite-time theorem that derivation flows preserve idempotents. -/
theorem map_idempotent_is_offDiagonal
    (D : FrechetOperatorDerivation 𝕜 A) {P : A}
    (hP : P * P = P) :
    D P = P * D P * (1 - P) + (1 - P) * D P * P := by
  have hLeib : D P = D P * P + P * D P := by
    calc
      D P = D (P * P) := congrArg D.toContinuousLinearMap hP.symm
      _ = D P * P + P * D P := D.leibniz P P
  let Q : A := 1 - P
  have hPQ : P * Q = 0 := by
    dsimp [Q]
    rw [mul_sub, mul_one, hP, sub_self]
  have hQP : Q * P = 0 := by
    dsimp [Q]
    rw [sub_mul, one_mul, hP, sub_self]
  have hDiagP : P * D P * P = 0 := by
    have hTwice : P * D P * P = P * D P * P + P * D P * P := by
      calc
        P * D P * P = P * (D P * P + P * D P) * P :=
          congrArg (fun z : A => P * z * P) hLeib
        _ = (P * (D P * P)) * P + (P * (P * D P)) * P := by
          rw [mul_add, add_mul]
        _ = P * D P * (P * P) + (P * P) * D P * P := by noncomm_ring
        _ = P * D P * P + P * D P * P := by rw [hP]
    have hCancel :
        (P * D P * P) + (0 : A) = (P * D P * P) + (P * D P * P) := by
      simpa using hTwice
    exact (add_left_cancel hCancel).symm
  have hDiagQ : Q * D P * Q = 0 := by
    calc
      Q * D P * Q = Q * (D P * P + P * D P) * Q :=
        congrArg (fun z : A => Q * z * Q) hLeib
      _ = (Q * (D P * P)) * Q + (Q * (P * D P)) * Q := by
        rw [mul_add, add_mul]
      _ = Q * D P * (P * Q) + (Q * P) * D P * Q := by noncomm_ring
      _ = 0 := by rw [hPQ, hQP]; simp
  have hSum : P + Q = 1 := by
    dsimp [Q]
    abel
  calc
    D P = (P + Q) * D P * (P + Q) := by rw [hSum, one_mul, mul_one]
    _ = P * D P * P + P * D P * Q + Q * D P * P + Q * D P * Q := by
      noncomm_ring
    _ = P * D P * Q + Q * D P * P := by rw [hDiagP, hDiagQ]; abel
    _ = P * D P * (1 - P) + (1 - P) * D P * P := by rfl

/-- The projected curvature commutator is exactly the product of the two
opposite off-diagonal Peirce blocks: `P [D₁P, D₂P] P = Y₁X₂ - Y₂X₁`. -/
theorem projected_commutator_peirce
    (D₁ D₂ : FrechetOperatorDerivation 𝕜 A) {P : A}
    (hP : P * P = P) :
    P * (D₁ P * D₂ P - D₂ P * D₁ P) * P =
      (P * D₁ P * (1 - P)) * ((1 - P) * D₂ P * P) -
      (P * D₂ P * (1 - P)) * ((1 - P) * D₁ P * P) := by
  let Q : A := 1 - P
  have hPQ : P * Q = 0 := by
    dsimp [Q]
    rw [mul_sub, mul_one, hP, sub_self]
  have hQP : Q * P = 0 := by
    dsimp [Q]
    rw [sub_mul, one_mul, hP, sub_self]
  have hD1 := map_idempotent_is_offDiagonal D₁ hP
  have hD2 := map_idempotent_is_offDiagonal D₂ hP
  change D₁ P = P * D₁ P * Q + Q * D₁ P * P at hD1
  change D₂ P = P * D₂ P * Q + Q * D₂ P * P at hD2
  let Y1 : A := P * D₁ P * Q
  let X1 : A := Q * D₁ P * P
  let Y2 : A := P * D₂ P * Q
  let X2 : A := Q * D₂ P * P
  have hYY : P * (Y1 * Y2) * P = 0 := by
    simp only [Y1, Y2, mul_assoc]
    rw [hQP]
    simp
  have hXY : P * (X1 * Y2) * P = 0 := by
    simp only [X1, Y2, mul_assoc]
    rw [← mul_assoc, hPQ, zero_mul]
  have hXX : P * (X1 * X2) * P = 0 := by
    simp only [X1, X2, mul_assoc]
    rw [← mul_assoc, hPQ, zero_mul]
  have hYX : P * (Y1 * X2) * P = Y1 * X2 := by
    simp only [Y1, X2, mul_assoc]
    rw [← mul_assoc, hP]
  have hY2X1 : P * (Y2 * X1) * P = Y2 * X1 := by
    simp only [Y2, X1, mul_assoc]
    rw [← mul_assoc, hP]
  calc
    P * (D₁ P * D₂ P - D₂ P * D₁ P) * P
        = P * ((Y1 + X1) * (Y2 + X2)) * P -
          P * ((Y2 + X2) * (Y1 + X1)) * P := by
          rw [hD1, hD2]
          simp only [Y1, X1, Y2, X2]
          noncomm_ring
    _ = (Y1 * X2) - (Y2 * X1) := by
          rw [show P * ((Y1 + X1) * (Y2 + X2)) * P =
            P * (Y1 * Y2) * P + P * (Y1 * X2) * P +
            P * (X1 * Y2) * P + P * (X1 * X2) * P by noncomm_ring]
          rw [show P * ((Y2 + X2) * (Y1 + X1)) * P =
            P * (Y2 * Y1) * P + P * (Y2 * X1) * P +
            P * (X2 * Y1) * P + P * (X2 * X1) * P by noncomm_ring]
          rw [hYY, hYX, hXY, hXX, hY2X1]
          have hYY' : P * (Y2 * Y1) * P = 0 := by
            simp only [Y2, Y1, mul_assoc]
            rw [hQP]
            simp
          have hX2Y1 : P * (X2 * Y1) * P = 0 := by
            simp only [X2, Y1, mul_assoc]
            rw [← mul_assoc, hPQ, zero_mul]
          have hX2X1 : P * (X2 * X1) * P = 0 := by
            simp only [X2, X1, mul_assoc]
            rw [← mul_assoc, hPQ, zero_mul]
          rw [hYY', hX2Y1, hX2X1]
          abel
    _ = (P * D₁ P * (1 - P)) * ((1 - P) * D₂ P * P) -
        (P * D₂ P * (1 - P)) * ((1 - P) * D₁ P * P) := by
          simp only [Y1, X2, Y2, X1, Q]

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

/-- Exponential derivation flow transports all four associative Peirce
components by applying the same flow to the cut and the operator. No
idempotency assumption is needed for this coordinate identity; the
idempotency hypotheses enter only when the components are interpreted as
orthogonal Peirce sectors. -/
theorem flow_transports_peirce_components
    {A : Type*} [NormedRing A] [NormedAlgebra ℝ A] [CompleteSpace A]
    (D : FrechetOperatorDerivation ℝ A) (t : ℝ) (P X : A) :
    let φ := InfoGeometry.Lie.ContinuousDerivationExponential.flow
      D.toContinuousLinearMap t
    φ (InfoGeometry.Core.PeirceDecomposition.component11 P X) =
        InfoGeometry.Core.PeirceDecomposition.component11 (φ P) (φ X) ∧
    φ (InfoGeometry.Core.PeirceDecomposition.component10 P X) =
        InfoGeometry.Core.PeirceDecomposition.component10 (φ P) (φ X) ∧
    φ (InfoGeometry.Core.PeirceDecomposition.component01 P X) =
        InfoGeometry.Core.PeirceDecomposition.component01 (φ P) (φ X) ∧
    φ (InfoGeometry.Core.PeirceDecomposition.component00 P X) =
        InfoGeometry.Core.PeirceDecomposition.component00 (φ P) (φ X) := by
  dsimp
  let φ : A →ₗ[ℝ] A :=
    (InfoGeometry.Lie.ContinuousDerivationExponential.flow
      D.toContinuousLinearMap t).toLinearMap
  have hD : InfoGeometry.Lie.ContinuousDerivationExponential.IsDerivation
      (ContinuousLinearMap.mul ℝ A) D.toContinuousLinearMap := by
    intro a b
    simpa [ContinuousLinearMap.mul_apply] using D.leibniz a b
  have hmul (a b : A) : φ (a * b) = φ a * φ b := by
    change InfoGeometry.Lie.ContinuousDerivationExponential.flow
        D.toContinuousLinearMap t (a * b) = _
    exact InfoGeometry.Lie.ContinuousDerivationExponential.flow_map_mul
      (mul := ContinuousLinearMap.mul ℝ A) D.toContinuousLinearMap hD t a b
  have hD1 : D.toContinuousLinearMap 1 = 0 := by
    have h := D.leibniz (1 : A) 1
    have h' : D.toContinuousLinearMap 1 + 0 =
        D.toContinuousLinearMap 1 + D.toContinuousLinearMap 1 := by
      simpa using h
    exact (add_left_cancel h').symm
  have hφ1 : φ 1 = 1 := by
    change InfoGeometry.Lie.ContinuousDerivationExponential.flow
        D.toContinuousLinearMap t 1 = 1
    exact InfoGeometry.Lie.ContinuousDerivationExponential.flow_apply_eq_self_of_apply_eq_zero
      D.toContinuousLinearMap 1 hD1 t
  have hφcomp (a : A) : φ (1 - a) = 1 - φ a := by
    rw [φ.map_sub, hφ1]
  refine ⟨?_, ?_, ?_, ?_⟩
  · change φ (P * X * P) = φ P * φ X * φ P
    rw [hmul, hmul]
  · change φ (P * X * (1 - P)) = φ P * φ X * (1 - φ P)
    rw [hmul, hmul, hφcomp]
  · change φ ((1 - P) * X * P) = (1 - φ P) * φ X * φ P
    rw [hmul, hmul, hφcomp]
  · change φ ((1 - P) * X * (1 - P)) = (1 - φ P) * φ X * (1 - φ P)
    rw [hmul, hmul, hφcomp]

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

/-- Every component of the Peirce Tetraktys has the derivative prescribed by
the same derivation along its exponential orbit. -/
theorem hasStrictDerivAt_flow_peirce_tetraktys
    {A : Type*} [NormedRing A] [NormedAlgebra ℝ A] [CompleteSpace A]
    (D : FrechetOperatorDerivation ℝ A) (t : ℝ) (P a c : A) :
    HasStrictDerivAt
      (fun s : ℝ =>
        InfoGeometry.OperatorAlgebra.PeirceSpine.genPhi
          (InfoGeometry.Lie.ContinuousDerivationExponential.flow D.toContinuousLinearMap s P)
          (InfoGeometry.Lie.ContinuousDerivationExponential.flow D.toContinuousLinearMap s a)
          (InfoGeometry.Lie.ContinuousDerivationExponential.flow D.toContinuousLinearMap s c))
      (D.toContinuousLinearMap
        (InfoGeometry.Lie.ContinuousDerivationExponential.flow D.toContinuousLinearMap t
          (InfoGeometry.OperatorAlgebra.PeirceSpine.genPhi P a c))) t ∧
    HasStrictDerivAt
      (fun s : ℝ =>
        InfoGeometry.OperatorAlgebra.PeirceSpine.genJ
          (InfoGeometry.Lie.ContinuousDerivationExponential.flow D.toContinuousLinearMap s P)
          (InfoGeometry.Lie.ContinuousDerivationExponential.flow D.toContinuousLinearMap s a)
          (InfoGeometry.Lie.ContinuousDerivationExponential.flow D.toContinuousLinearMap s c))
      (D.toContinuousLinearMap
        (InfoGeometry.Lie.ContinuousDerivationExponential.flow D.toContinuousLinearMap t
          (InfoGeometry.OperatorAlgebra.PeirceSpine.genJ P a c))) t ∧
    HasStrictDerivAt
      (fun s : ℝ =>
        InfoGeometry.OperatorAlgebra.PeirceSpine.genV
          (InfoGeometry.Lie.ContinuousDerivationExponential.flow D.toContinuousLinearMap s P)
          (InfoGeometry.Lie.ContinuousDerivationExponential.flow D.toContinuousLinearMap s a)
          (InfoGeometry.Lie.ContinuousDerivationExponential.flow D.toContinuousLinearMap s c))
      (D.toContinuousLinearMap
        (InfoGeometry.Lie.ContinuousDerivationExponential.flow D.toContinuousLinearMap t
          (InfoGeometry.OperatorAlgebra.PeirceSpine.genV P a c))) t ∧
    HasStrictDerivAt
      (fun s : ℝ =>
        InfoGeometry.OperatorAlgebra.PeirceSpine.genSig
          (InfoGeometry.Lie.ContinuousDerivationExponential.flow D.toContinuousLinearMap s P)
          (InfoGeometry.Lie.ContinuousDerivationExponential.flow D.toContinuousLinearMap s a)
          (InfoGeometry.Lie.ContinuousDerivationExponential.flow D.toContinuousLinearMap s c))
      (D.toContinuousLinearMap
        (InfoGeometry.Lie.ContinuousDerivationExponential.flow D.toContinuousLinearMap t
          (InfoGeometry.OperatorAlgebra.PeirceSpine.genSig P a c))) t := by
  have hPhi (s : ℝ) :
      InfoGeometry.OperatorAlgebra.PeirceSpine.genPhi
          (InfoGeometry.Lie.ContinuousDerivationExponential.flow D.toContinuousLinearMap s P)
          (InfoGeometry.Lie.ContinuousDerivationExponential.flow D.toContinuousLinearMap s a)
          (InfoGeometry.Lie.ContinuousDerivationExponential.flow D.toContinuousLinearMap s c) =
        InfoGeometry.Lie.ContinuousDerivationExponential.flow D.toContinuousLinearMap s
          (InfoGeometry.OperatorAlgebra.PeirceSpine.genPhi P a c) := by
    have h := flow_transports_peirce_tetraktys D s P a c
    dsimp at h
    exact h.1.symm
  have hJ (s : ℝ) :
      InfoGeometry.OperatorAlgebra.PeirceSpine.genJ
          (InfoGeometry.Lie.ContinuousDerivationExponential.flow D.toContinuousLinearMap s P)
          (InfoGeometry.Lie.ContinuousDerivationExponential.flow D.toContinuousLinearMap s a)
          (InfoGeometry.Lie.ContinuousDerivationExponential.flow D.toContinuousLinearMap s c) =
        InfoGeometry.Lie.ContinuousDerivationExponential.flow D.toContinuousLinearMap s
          (InfoGeometry.OperatorAlgebra.PeirceSpine.genJ P a c) := by
    have h := flow_transports_peirce_tetraktys D s P a c
    dsimp at h
    exact h.2.1.symm
  have hV (s : ℝ) :
      InfoGeometry.OperatorAlgebra.PeirceSpine.genV
          (InfoGeometry.Lie.ContinuousDerivationExponential.flow D.toContinuousLinearMap s P)
          (InfoGeometry.Lie.ContinuousDerivationExponential.flow D.toContinuousLinearMap s a)
          (InfoGeometry.Lie.ContinuousDerivationExponential.flow D.toContinuousLinearMap s c) =
        InfoGeometry.Lie.ContinuousDerivationExponential.flow D.toContinuousLinearMap s
          (InfoGeometry.OperatorAlgebra.PeirceSpine.genV P a c) := by
    have h := flow_transports_peirce_tetraktys D s P a c
    dsimp at h
    exact h.2.2.1.symm
  have hSig (s : ℝ) :
      InfoGeometry.OperatorAlgebra.PeirceSpine.genSig
          (InfoGeometry.Lie.ContinuousDerivationExponential.flow D.toContinuousLinearMap s P)
          (InfoGeometry.Lie.ContinuousDerivationExponential.flow D.toContinuousLinearMap s a)
          (InfoGeometry.Lie.ContinuousDerivationExponential.flow D.toContinuousLinearMap s c) =
        InfoGeometry.Lie.ContinuousDerivationExponential.flow D.toContinuousLinearMap s
          (InfoGeometry.OperatorAlgebra.PeirceSpine.genSig P a c) := by
    have h := flow_transports_peirce_tetraktys D s P a c
    dsimp at h
    exact h.2.2.2.symm
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [funext hPhi]
    exact InfoGeometry.Lie.ContinuousDerivationExponential.hasStrictDerivAt_orbit
      D.toContinuousLinearMap
      (InfoGeometry.OperatorAlgebra.PeirceSpine.genPhi P a c) t
  · rw [funext hJ]
    exact InfoGeometry.Lie.ContinuousDerivationExponential.hasStrictDerivAt_orbit
      D.toContinuousLinearMap
      (InfoGeometry.OperatorAlgebra.PeirceSpine.genJ P a c) t
  · rw [funext hV]
    exact InfoGeometry.Lie.ContinuousDerivationExponential.hasStrictDerivAt_orbit
      D.toContinuousLinearMap
      (InfoGeometry.OperatorAlgebra.PeirceSpine.genV P a c) t
  · rw [funext hSig]
    exact InfoGeometry.Lie.ContinuousDerivationExponential.hasStrictDerivAt_orbit
      D.toContinuousLinearMap
      (InfoGeometry.OperatorAlgebra.PeirceSpine.genSig P a c) t

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

namespace InfoGeometry.Optics.OperatorDerivationForms

open InfoGeometry.Geometry.BilingualAnalyticity
open InfoGeometry.Thermo.SusceptibilityOnsagerStress

/-! ## Typed Disambiguation of `NOperatorForm` / `OneFormTuple` vs Alternating Forms -/

section OneFormTupleDisambiguation

open InfoGeometry.OperatorAlgebra.General
open InfoGeometry.OperatorAlgebra.DerivationDifferentialForms

/-- Definitional identity between `OneFormTuple` and `NOperatorForm`. -/
theorem oneFormTuple_eq_nOperatorForm
    (Point Tangent Value : Type*) [Ring Value] [Algebra ℝ Value] (n : ℕ) :
    OneFormTuple Point Tangent Value n =
      NOperatorForm (Point := Point) (Tangent := Tangent) (Value := Value) n :=
  rfl

/-- At degree `n = 1`, `OneFormTuple` is equivalent to a single `OperatorOneForm`. -/
def oneFormTupleOneEquiv (Point Tangent Value : Type*) :
    OneFormTuple Point Tangent Value 1 ≃ OperatorOneForm Point Tangent Value where
  toFun ω := ω 0
  invFun α := fun _ => α
  left_inv ω := funext fun i => by rw [Fin.eq_zero i]
  right_inv _ := rfl

/-- At degree `n = 1`, `NOperatorForm 1` is equivalent to a single `OperatorOneForm`. -/
def nOperatorFormOneEquiv
    {Point Tangent Value : Type*} [Ring Value] [Algebra ℝ Value] :
    NOperatorForm (Point := Point) (Tangent := Tangent) (Value := Value) 1 ≃
      OperatorOneForm Point Tangent Value :=
  oneFormTupleOneEquiv Point Tangent Value

/-- Embed an `R`-linear 1-form `OpForm R V A 1` into `OneFormTuple P V A 1` (constant in `P`). -/
def opFormOneToOneFormTuple (P : Type*) {R V A : Type*} [Ring R]
    [AddCommGroup V] [Module R V] [Ring A] [Module R A]
    (η : OpForm R V A 1) : OneFormTuple P V A 1 :=
  fun _ _ v => η (fun _ => v)

@[simp] theorem opFormOneToOneFormTuple_apply (P : Type*) {R V A : Type*} [Ring R]
    [AddCommGroup V] [Module R V] [Ring A] [Module R A]
    (η : OpForm R V A 1) (i : Fin 1) (p : P) (v : V) :
    opFormOneToOneFormTuple P η i p v = η (fun _ => v) :=
  rfl

/-- `R`-linear isomorphism `(V →ₗ[R] A) ≃ₗ[R] OpForm R V A 1`. -/
def oneFormLinearToOpFormOne {R V A : Type*} [CommRing R]
    [AddCommGroup V] [Module R V] [Ring A] [Module R A] :
    (V →ₗ[R] A) ≃ₗ[R] OpForm R V A 1 where
  toLinearMap :=
    { toFun := AlternatingMap.ofSubsingleton R V A (0 : Fin 1)
      map_add' := fun _ _ => by ext v; rfl
      map_smul' := fun _ _ => by ext v; rfl }
  invFun η :=
    { toFun := fun x => η (fun _ => x)
      map_add' := fun x y => by
        have h : (fun _ : Fin 1 => x + y) = Function.update (fun _ => x) 0 (x + y) :=
          funext fun i => by fin_cases i; rfl
        have h0 : (fun _ : Fin 1 => x) = Function.update (fun _ => x) 0 x :=
          funext fun i => by fin_cases i; rfl
        have h1 : (fun _ : Fin 1 => y) = Function.update (fun _ => x) 0 y :=
          funext fun i => by fin_cases i; rfl
        rw [h, η.map_update_add, ← h0, ← h1]
      map_smul' := fun c x => by
        have h : (fun _ : Fin 1 => c • x) = Function.update (fun _ => x) 0 (c • x) :=
          funext fun i => by fin_cases i; rfl
        have h0 : (fun _ : Fin 1 => x) = Function.update (fun _ => x) 0 x :=
          funext fun i => by fin_cases i; rfl
        change η (fun _ => c • x) = c • η (fun _ => x)
        rw [h, η.map_update_smul, ← h0] }
  left_inv _ := by ext x; rfl
  right_inv η := by
    ext v
    change η (fun _ => v 0) = η v
    congr 1
    ext i
    rw [Fin.eq_zero i]

/-- Embed an `ActionOperatorForm K 1` into `OneFormTuple P K.L A 1`. -/
def actionOneFormToOneFormTuple (P : Type*) {R A : Type*} [CommRing R]
    [Ring A] [Module R A] (K : InfoGeometry.Algebra.LieActionLane R A)
    (η : ActionOperatorForm K 1) : OneFormTuple P K.L A 1 :=
  opFormOneToOneFormTuple P η

/-- Embed a `DerivationOperatorForm K 1` into `OneFormTuple P K.L A 1`. -/
def derivationOneFormToOneFormTuple (P : Type*) {R A : Type*} [CommRing R]
    [Ring A] [Module R A] [IsScalarTower R A A] [SMulCommClass R A A]
    (K : InfoGeometry.Algebra.DerivationLieLane R A)
    (η : DerivationOperatorForm K 1) : OneFormTuple P K.L A 1 :=
  opFormOneToOneFormTuple P η

/-- Slot evaluation of an alternating `n`-form at a base tuple `v : Fin n → V`
along coordinate `i : Fin n`, producing an `R`-linear 1-form `V →ₗ[R] A`. -/
def opFormSlotOneForm {R V A : Type*} [Ring R]
    [AddCommGroup V] [Module R V] [Ring A] [Module R A]
    {n : ℕ} (ω : OpForm R V A n) (v : Fin n → V) (i : Fin n) : V →ₗ[R] A where
  toFun x := ω (Function.update v i x)
  map_add' x y := ω.map_update_add v i x y
  map_smul' c x := ω.map_update_smul v i c x

/-- Project an alternating `n`-form `OpForm R V A n` at `v : Fin n → V`
to a `Fin n`-indexed `OneFormTuple P V A n`. -/
def opFormToOneFormTuple (P : Type*) {R V A : Type*} [Ring R]
    [AddCommGroup V] [Module R V] [Ring A] [Module R A]
    {n : ℕ} (ω : OpForm R V A n) (v : Fin n → V) : OneFormTuple P V A n :=
  fun i _ x => opFormSlotOneForm ω v i x

/-- Project a `DerivationOperatorForm K n` at `v` to `OneFormTuple P K.L A n`. -/
def derivationFormToOneFormTuple (P : Type*) {R A : Type*} [CommRing R]
    [Ring A] [Module R A] [IsScalarTower R A A] [SMulCommClass R A A]
    (K : InfoGeometry.Algebra.DerivationLieLane R A)
    {n : ℕ} (ω : DerivationOperatorForm K n) (v : Fin n → K.L) :
    OneFormTuple P K.L A n :=
  fun i _ x => ω (Function.update v i x)

/-- Currying the remaining `n` slots of an alternating `(n + 1)`-form at `w : Fin n → V`
produces an `R`-linear 1-form `V →ₗ[R] A`. -/
def opFormCurryFirstLinear {R V A : Type*} [Ring R]
    [AddCommGroup V] [Module R V] [Ring A] [Module R A]
    {n : ℕ} (ω : OpForm R V A (n + 1)) (w : Fin n → V) : V →ₗ[R] A where
  toFun x := ω (Matrix.vecCons x w)
  map_add' x y := by
    have h1 : Matrix.vecCons (x + y) w =
        Function.update (Matrix.vecCons x w) 0 (x + y) := by
      ext i; cases i using Fin.cases <;> rfl
    have h0 : Matrix.vecCons x w =
        Function.update (Matrix.vecCons x w) 0 x := by
      ext i; cases i using Fin.cases <;> rfl
    have h2 : Matrix.vecCons y w =
        Function.update (Matrix.vecCons x w) 0 y := by
      ext i; cases i using Fin.cases <;> rfl
    rw [h1, ω.map_update_add, ← h0, ← h2]
  map_smul' c x := by
    have h1 : Matrix.vecCons (c • x) w =
        Function.update (Matrix.vecCons x w) 0 (c • x) := by
      ext i; cases i using Fin.cases <;> rfl
    have h0 : Matrix.vecCons x w =
        Function.update (Matrix.vecCons x w) 0 x := by
      ext i; cases i using Fin.cases <;> rfl
    change ω (Matrix.vecCons (c • x) w) = c • ω (Matrix.vecCons x w)
    rw [h1, ω.map_update_smul, ← h0]

@[simp] theorem opFormCurryFirstLinear_mem {R V A : Type*} [Ring R]
    [AddCommGroup V] [Module R V] [Ring A] [Module R A]
    {n : ℕ} (ω : OpForm R V A (n + 1)) (w : Fin n → V) (j : Fin n) :
    opFormCurryFirstLinear ω w (w j) = 0 := by
  exact ω.map_eq_zero_of_eq (Matrix.vecCons (w j) w) (i := 0) (j := j.succ)
    rfl (Fin.succ_ne_zero j).symm

/-- Iterated noncommutative wedge of a `Fin (n + 1)`-tuple of `ActionOperatorForm K 1`
into `ActionOperatorForm K (n + 1)`. -/
def actionWedgeTupleSucc {R A : Type*} [CommRing R] [NonUnitalNonAssocRing A]
    [Module R A] [IsScalarTower R A A] [SMulCommClass R A A]
    (K : InfoGeometry.Algebra.LieActionLane R A) :
    ∀ {n : ℕ}, (Fin (n + 1) → ActionOperatorForm K 1) → ActionOperatorForm K (n + 1)
  | 0, α => α 0
  | m + 1, α =>
    reindexForm (Nat.add_comm 1 (m + 1))
      (actionWedge K (α 0) (actionWedgeTupleSucc K (fun i => α i.succ)))

/-- Iterated noncommutative wedge of a `Fin (n + 1)`-tuple of `DerivationOperatorForm K 1`
into `DerivationOperatorForm K (n + 1)`. -/
def ceWedgeTupleSucc {R A : Type*} [CommRing R] [NonUnitalNonAssocRing A]
    [Module R A] [IsScalarTower R A A] [SMulCommClass R A A]
    (K : InfoGeometry.Algebra.DerivationLieLane R A) {n : ℕ}
    (α : Fin (n + 1) → DerivationOperatorForm K 1) :
    DerivationOperatorForm K (n + 1) :=
  actionWedgeTupleSucc K.toLieActionLane α

@[simp] theorem ceWedgeTupleSucc_one {R A : Type*} [CommRing R] [NonUnitalNonAssocRing A]
    [Module R A] [IsScalarTower R A A] [SMulCommClass R A A]
    (K : InfoGeometry.Algebra.DerivationLieLane R A)
    (α : Fin 1 → DerivationOperatorForm K 1) :
    ceWedgeTupleSucc K α = α 0 :=
  rfl

theorem ceWedgeTupleSucc_two_apply {R A : Type*} [CommRing R] [NonUnitalNonAssocRing A]
    [Module R A] [IsScalarTower R A A] [SMulCommClass R A A]
    (K : InfoGeometry.Algebra.DerivationLieLane R A)
    (α : Fin 2 → DerivationOperatorForm K 1) (x y : K.L) :
    ceWedgeTupleSucc K α ![x, y] = α 0 ![x] * α 1 ![y] - α 0 ![y] * α 1 ![x] := by
  change (reindexForm (Nat.add_comm 1 1) (ceWedge K (α 0) (α 1))) ![x, y] = _
  simp [ceWedge_one_one_apply]

/-- Iterated noncommutative wedge of `Fin (n + 1)`-tuples of `OpForm R V A 1`. -/
def opFormWedgeTupleSucc {R V A : Type*} [CommRing R]
    [AddCommGroup V] [Module R V] [Ring A] [Module R A]
    [IsScalarTower R A A] [SMulCommClass R A A] :
    ∀ {n : ℕ}, (Fin (n + 1) → OpForm R V A 1) → OpForm R V A (n + 1)
  | 0, α => α 0
  | m + 1, α =>
    reindexForm (Nat.add_comm 1 (m + 1))
      (opWedge (α 0) (opFormWedgeTupleSucc (fun i => α i.succ)))

/-- Iterated noncommutative wedge of `Fin n`-tuples of `OpForm R V A 1` for all `n : ℕ`. -/
def opFormWedgeTuple {R V A : Type*} [CommRing R]
    [AddCommGroup V] [Module R V] [Ring A] [Module R A]
    [IsScalarTower R A A] [SMulCommClass R A A] :
    ∀ n : ℕ, (Fin n → OpForm R V A 1) → OpForm R V A n
  | 0, _ => AlternatingMap.constLinearEquivOfIsEmpty (1 : A)
  | _ + 1, α => opFormWedgeTupleSucc α

/-- Contrast witness 1 (`n = 2`): `NOperatorForm 2` admits constant nonzero maps that do not
even vanish at `0`, whereas every `OpForm ℝ ℝ ℝ 1` is linear (`η 0 = 0`). -/
theorem nOperatorForm_two_not_linear_witness :
    ∃ ω : NOperatorForm (Point := Unit) (Tangent := ℝ) (Value := ℝ) 2,
      ω 0 () (0 : ℝ) ≠ 0 :=
  ⟨fun _ _ _ => (1 : ℝ), one_ne_zero⟩

theorem opForm_one_map_zero (η : OpForm ℝ ℝ ℝ 1) :
    η (fun _ => (0 : ℝ)) = 0 := by
  have h : (fun _ : Fin 1 => (0 : ℝ)) = Function.update (fun _ => (0 : ℝ)) 0 (0 : ℝ) :=
    funext fun i => by fin_cases i; rfl
  rw [h, η.map_update_zero]

/-- Contrast witness 2 (`n = 2`): even a linear `NOperatorForm 2` has nonzero diagonal values
at `(1, 1)`, whereas every alternating `OpForm ℝ ℝ ℝ 2` vanishes on `![x, x]`. -/
theorem nOperatorForm_two_linear_diag_nonzero_witness :
    ∃ ω : NOperatorForm (Point := Unit) (Tangent := ℝ) (Value := ℝ) 2,
      (∀ i p, IsLinearMap ℝ (ω i p)) ∧ ω 0 () (1 : ℝ) ≠ 0 ∧ ω 1 () (1 : ℝ) ≠ 0 :=
  ⟨fun _ _ x => x,
    fun _ _ => ⟨fun _ _ => rfl, fun _ _ => rfl⟩,
    one_ne_zero, one_ne_zero⟩

theorem opForm_two_diag_zero (η : OpForm ℝ ℝ ℝ 2) (x : ℝ) :
    η ![x, x] = 0 :=
  η.map_eq_zero_of_eq ![x, x] (i := 0) (j := 1) rfl (by decide)

end OneFormTupleDisambiguation

/-! ## `FrechetOperatorDerivation` Lie Algebra & Unified M1A Spine Adapters -/

namespace FrechetOperatorDerivation

section SpineAdapters

attribute [local instance 100] LieRing.ofAssociativeRing LieAlgebra.ofAssociativeAlgebra

open InfoGeometry.Algebra
open InfoGeometry.Algebra.DerivationLieLane
open InfoGeometry.OperatorAlgebra.DerivationDifferentialForms
open InfoGeometry.NCG.Calculus

section AlgebraicInstances

variable {𝕜 A : Type*} [NontriviallyNormedField 𝕜]
variable [NormedRing A] [NormedAlgebra 𝕜 A]

@[ext] theorem ext {D E : FrechetOperatorDerivation 𝕜 A}
    (h : ∀ a : A, D a = E a) : D = E := by
  cases D with
  | mk f hf =>
    cases E with
    | mk g hg =>
      congr
      exact ContinuousLinearMap.ext h

instance : Zero (FrechetOperatorDerivation 𝕜 A) where
  zero :=
    { toContinuousLinearMap := 0
      leibniz := fun _ _ => by simp }

instance : Add (FrechetOperatorDerivation 𝕜 A) where
  add D E :=
    { toContinuousLinearMap := D.toContinuousLinearMap + E.toContinuousLinearMap
      leibniz := fun a b => by
        change D (a * b) + E (a * b) = (D a + E a) * b + a * (D b + E b)
        rw [D.leibniz, E.leibniz, add_mul, mul_add]
        abel }

instance : Neg (FrechetOperatorDerivation 𝕜 A) where
  neg D :=
    { toContinuousLinearMap := -D.toContinuousLinearMap
      leibniz := fun a b => by
        change -D (a * b) = (-D a) * b + a * (-D b)
        rw [D.leibniz, neg_add, neg_mul, mul_neg] }

instance : Sub (FrechetOperatorDerivation 𝕜 A) where
  sub D E :=
    { toContinuousLinearMap := D.toContinuousLinearMap - E.toContinuousLinearMap
      leibniz := fun a b => by
        change D (a * b) - E (a * b) = (D a - E a) * b + a * (D b - E b)
        rw [D.leibniz, E.leibniz, sub_mul, mul_sub]
        abel }

instance : SMul 𝕜 (FrechetOperatorDerivation 𝕜 A) where
  smul c D :=
    { toContinuousLinearMap := c • D.toContinuousLinearMap
      leibniz := fun a b => by
        change c • D (a * b) = (c • D a) * b + a * (c • D b)
        rw [D.leibniz, smul_add, Algebra.smul_mul_assoc, Algebra.mul_smul_comm] }

@[simp] theorem zero_apply (a : A) : (0 : FrechetOperatorDerivation 𝕜 A) a = 0 := rfl
@[simp] theorem add_apply (D E : FrechetOperatorDerivation 𝕜 A) (a : A) :
    (D + E) a = D a + E a := rfl
@[simp] theorem neg_apply (D : FrechetOperatorDerivation 𝕜 A) (a : A) :
    (-D) a = -D a := rfl
@[simp] theorem sub_apply (D E : FrechetOperatorDerivation 𝕜 A) (a : A) :
    (D - E) a = D a - E a := rfl
@[simp] theorem smul_apply (c : 𝕜) (D : FrechetOperatorDerivation 𝕜 A) (a : A) :
    (c • D) a = c • D a := rfl

instance : AddCommGroup (FrechetOperatorDerivation 𝕜 A) where
  add_assoc D E F := by ext a; exact add_assoc (D a) (E a) (F a)
  zero_add D := by ext a; exact zero_add (D a)
  add_zero D := by ext a; exact add_zero (D a)
  neg_add_cancel D := by ext a; exact neg_add_cancel (D a)
  add_comm D E := by ext a; exact add_comm (D a) (E a)
  sub_eq_add_neg D E := by ext a; exact sub_eq_add_neg (D a) (E a)
  nsmul := nsmulRec
  zsmul := zsmulRec

instance : Module 𝕜 (FrechetOperatorDerivation 𝕜 A) where
  one_smul D := by ext a; exact one_smul 𝕜 (D a)
  mul_smul c₁ c₂ D := by ext a; exact mul_smul c₁ c₂ (D a)
  smul_zero c := by ext a; exact smul_zero c
  smul_add c D E := by ext a; exact smul_add c (D a) (E a)
  add_smul c₁ c₂ D := by ext a; exact add_smul c₁ c₂ (D a)
  zero_smul D := by ext a; exact zero_smul 𝕜 (D a)

instance : Bracket (FrechetOperatorDerivation 𝕜 A) (FrechetOperatorDerivation 𝕜 A) where
  bracket := commutator

@[simp] theorem lie_eq_commutator (D E : FrechetOperatorDerivation 𝕜 A) :
    ⁅D, E⁆ = commutator D E := rfl

@[simp] theorem lie_apply (D E : FrechetOperatorDerivation 𝕜 A) (a : A) :
    ⁅D, E⁆ a = D (E a) - E (D a) := rfl

instance : LieRing (FrechetOperatorDerivation 𝕜 A) where
  add_lie D E F := by
    ext a
    simp only [lie_apply, add_apply, F.map_add]
    abel
  lie_add D E F := by
    ext a
    simp only [lie_apply, add_apply, D.map_add]
    abel
  lie_self D := by
    ext a
    simp only [lie_apply, zero_apply, sub_self]
  leibniz_lie D E F := by
    ext a
    simp only [lie_apply, add_apply, D.toContinuousLinearMap.map_sub,
      E.toContinuousLinearMap.map_sub, F.toContinuousLinearMap.map_sub]
    abel

instance : LieAlgebra 𝕜 (FrechetOperatorDerivation 𝕜 A) where
  lie_smul c D E := by
    ext a
    simp only [lie_apply, smul_apply, D.map_smul, smul_sub]

/-- Forget continuity to obtain an element of `NonAssocDerivation.derivations 𝕜 A`. -/
def toDerivations (D : FrechetOperatorDerivation 𝕜 A) : NonAssocDerivation.derivations 𝕜 A :=
  ⟨D.toContinuousLinearMap.toLinearMap, D.leibniz⟩

@[simp] theorem toDerivations_apply (D : FrechetOperatorDerivation 𝕜 A) (a : A) :
    (D.toDerivations : Module.End 𝕜 A) a = D a :=
  rfl

/-- Canonical faithful Lie algebra homomorphism from continuous Fréchet derivations
into `NonAssocDerivation.derivations 𝕜 A`. -/
def toDerivationsLieHom (𝕜 A : Type*) [NontriviallyNormedField 𝕜]
    [NormedRing A] [NormedAlgebra 𝕜 A] :
    FrechetOperatorDerivation 𝕜 A →ₗ⁅𝕜⁆ NonAssocDerivation.derivations 𝕜 A where
  toFun := toDerivations
  map_add' _ _ := Subtype.ext (LinearMap.ext fun _ => rfl)
  map_smul' _ _ := Subtype.ext (LinearMap.ext fun _ => rfl)
  map_lie' := Subtype.ext (LinearMap.ext fun _ => rfl)

theorem toDerivationsLieHom_injective (𝕜 A : Type*) [NontriviallyNormedField 𝕜]
    [NormedRing A] [NormedAlgebra 𝕜 A] :
    Function.Injective (toDerivationsLieHom 𝕜 A) := by
  intro D E h
  ext a
  exact congrArg (fun T : NonAssocDerivation.derivations 𝕜 A => (T : Module.End 𝕜 A) a) h

/-- Canonical faithful `DerivationLieLane 𝕜 A` on `FrechetOperatorDerivation 𝕜 A`. -/
def derivationLieLane (𝕜 A : Type*) [NontriviallyNormedField 𝕜]
    [NormedRing A] [NormedAlgebra 𝕜 A] : DerivationLieLane 𝕜 A where
  L := FrechetOperatorDerivation 𝕜 A
  lieRing := inferInstance
  lieAlgebra := inferInstance
  act := toDerivationsLieHom 𝕜 A
  faithful := toDerivationsLieHom_injective 𝕜 A

/-- Underlying `LieActionLane 𝕜 A` of `FrechetOperatorDerivation.derivationLieLane 𝕜 A`. -/
def lieActionLane (𝕜 A : Type*) [NontriviallyNormedField 𝕜]
    [NormedRing A] [NormedAlgebra 𝕜 A] : LieActionLane 𝕜 A :=
  (derivationLieLane 𝕜 A).toLieActionLane

theorem lieActionLane_isLeibniz (𝕜 A : Type*) [NontriviallyNormedField 𝕜]
    [NormedRing A] [NormedAlgebra 𝕜 A] :
    IsLeibnizAction (lieActionLane 𝕜 A) :=
  (derivationLieLane 𝕜 A).isLeibnizAction

/-- Lie subalgebra of `NonAssocDerivation.derivations 𝕜 A` consisting of continuous
Fréchet operator derivations. -/
def continuousLieSubalgebra (𝕜 A : Type*) [NontriviallyNormedField 𝕜]
    [NormedRing A] [NormedAlgebra 𝕜 A] :
    LieSubalgebra 𝕜 (NonAssocDerivation.derivations 𝕜 A) :=
  (toDerivationsLieHom 𝕜 A).range

/-- Faithful `DerivationLieLane 𝕜 A` on `continuousLieSubalgebra 𝕜 A`. -/
def continuousSubalgebraLane (𝕜 A : Type*) [NontriviallyNormedField 𝕜]
    [NormedRing A] [NormedAlgebra 𝕜 A] : DerivationLieLane 𝕜 A :=
  lieSubalgebraLane (continuousLieSubalgebra 𝕜 A)

/-- Equivariant identification between `derivationLieLane 𝕜 A` and
`continuousSubalgebraLane 𝕜 A`. -/
def derivationLieLaneEquivContinuousSubalgebra (𝕜 A : Type*) [NontriviallyNormedField 𝕜]
    [NormedRing A] [NormedAlgebra 𝕜 A] :
    DerivationLaneEquiv (derivationLieLane 𝕜 A) (continuousSubalgebraLane 𝕜 A) where
  map := LieEquiv.ofInjective (toDerivationsLieHom 𝕜 A) (toDerivationsLieHom_injective 𝕜 A)
  equivariant _ := rfl

/-- Faithfulness-free `LieActionLane 𝕜 A` induced by any Lie algebra homomorphism
`L →ₗ⁅𝕜⁆ FrechetOperatorDerivation 𝕜 A`. -/
def toLieActionLaneOfHom {L : Type*} [LieRing L] [LieAlgebra 𝕜 L]
    (act : L →ₗ⁅𝕜⁆ FrechetOperatorDerivation 𝕜 A) : LieActionLane 𝕜 A :=
  toLieActionLaneFromHom ((toDerivationsLieHom 𝕜 A).comp act)

theorem toLieActionLaneOfHom_isLeibniz {L : Type*} [LieRing L] [LieAlgebra 𝕜 L]
    (act : L →ₗ⁅𝕜⁆ FrechetOperatorDerivation 𝕜 A) :
    IsLeibnizAction (toLieActionLaneOfHom act) :=
  toLieActionLaneFromHom_isLeibniz ((toDerivationsLieHom 𝕜 A).comp act)

/-- Faithful range `DerivationLieLane 𝕜 A` of `act : L →ₗ⁅𝕜⁆ FrechetOperatorDerivation 𝕜 A`. -/
def rangeDerivationLieLaneOfHom {L : Type*} [LieRing L] [LieAlgebra 𝕜 L]
    (act : L →ₗ⁅𝕜⁆ FrechetOperatorDerivation 𝕜 A) : DerivationLieLane 𝕜 A :=
  rangeDerivationLieLane ((toDerivationsLieHom 𝕜 A).comp act)

/-- Faithful quotient `DerivationLieLane 𝕜 A` of `act : L →ₗ⁅𝕜⁆ FrechetOperatorDerivation 𝕜 A`. -/
def quotientDerivationLieLaneOfHom {L : Type*} [LieRing L] [LieAlgebra 𝕜 L]
    (act : L →ₗ⁅𝕜⁆ FrechetOperatorDerivation 𝕜 A) : DerivationLieLane 𝕜 A :=
  quotientDerivationLieLane ((toDerivationsLieHom 𝕜 A).comp act)

/-- Single-derivation Lie homomorphism `𝕜 →ₗ⁅𝕜⁆ FrechetOperatorDerivation 𝕜 A`
given by `c ↦ c • D`. -/
def singleLieHom (D : FrechetOperatorDerivation 𝕜 A) :
    𝕜 →ₗ⁅𝕜⁆ FrechetOperatorDerivation 𝕜 A where
  toFun c := c • D
  map_add' c₁ c₂ := add_smul c₁ c₂ D
  map_smul' c₁ c₂ := smul_eq_mul c₁ c₂ ▸ mul_smul c₁ c₂ D
  map_lie' {c₁ c₂} := by
    ext a
    change (c₁ * c₂ - c₂ * c₁) • D a = c₁ • D (c₂ • D a) - c₂ • D (c₁ • D a)
    rw [mul_comm c₁ c₂, sub_self, zero_smul, D.map_smul, D.map_smul,
      smul_smul, smul_smul, mul_comm c₁ c₂, sub_self]

/-- One-generator `LieActionLane 𝕜 A` attached to a single `FrechetOperatorDerivation D`. -/
def singleLieActionLane (D : FrechetOperatorDerivation 𝕜 A) : LieActionLane 𝕜 A :=
  toLieActionLaneOfHom (singleLieHom D)

theorem singleLieActionLane_isLeibniz (D : FrechetOperatorDerivation 𝕜 A) :
    IsLeibnizAction (singleLieActionLane D) :=
  toLieActionLaneOfHom_isLeibniz (singleLieHom D)

/-- Faithful `DerivationLieLane 𝕜 A` on the Lie subalgebra spanned by a single
`FrechetOperatorDerivation D`. -/
def singleDerivationLieLane (D : FrechetOperatorDerivation 𝕜 A) : DerivationLieLane 𝕜 A :=
  lieSubalgebraLane (LieSubalgebra.lieSpan 𝕜 (NonAssocDerivation.derivations 𝕜 A) {D.toDerivations})

end AlgebraicInstances

section RealBridges

variable {A : Type*} [NormedRing A] [NormedAlgebra ℝ A]

/-- Inner derivation Lie homomorphism `A →ₗ⁅ℝ⁆ FrechetOperatorDerivation ℝ A`
on a complete normed algebra `A`. -/
def ofInnerLieHom (A : Type*) [NormedRing A] [NormedAlgebra ℝ A] [CompleteSpace A] :
    A →ₗ⁅ℝ⁆ FrechetOperatorDerivation ℝ A where
  toFun a := ofInner a
  map_add' a b := by
    ext x
    change (a + b) * x - x * (a + b) = (a * x - x * a) + (b * x - x * b)
    noncomm_ring
  map_smul' r a := by
    ext x
    change (r • a) * x - x * (r • a) = r • (a * x - x * a)
    simp only [Algebra.smul_mul_assoc, Algebra.mul_smul_comm, smul_sub]
  map_lie' {a b} := by
    ext x
    change ofInner (a * b - b * a) x = ⁅ofInner a, ofInner b⁆ x
    simp only [lie_apply, ofInner_apply]
    noncomm_ring

theorem ofInnerLieActionLane_apply [CompleteSpace A] (x a : A) :
    (toLieActionLaneOfHom (ofInnerLieHom A)).operatorAction x a =
      (innerLieActionLane A).operatorAction x a :=
  rfl

theorem toNCDerivation_apply_eq_toDerivations
    (D : FrechetOperatorDerivation ℝ A) (a : A) :
    toNCDerivation D a = (D.toDerivations : Module.End ℝ A) a :=
  rfl

theorem toNCDerivation_eq_ncDerivationEquivDerivations_symm
    (D : FrechetOperatorDerivation ℝ A) :
    ncDerivationEquivDerivations (toNCDerivation D) =
      ⟨(D.toDerivations : Module.End ℝ A).restrictScalars ℤ, D.leibniz⟩ :=
  rfl

theorem toDerivationDifferentialSystem_derivation_eq_toDerivations
    {𝔤 : Type*} [AddGroup 𝔤]
    (derivation : 𝔤 → FrechetOperatorDerivation ℝ A)
    (bracket : 𝔤 → 𝔤 → 𝔤)
    (hbracket : ∀ D E a,
      derivation D (derivation E a) - derivation E (derivation D a) =
        derivation (bracket D E) a)
    (D : 𝔤) (a : A) :
    (toDerivationDifferentialSystem derivation bracket hbracket).derivation D a =
      ((derivation D).toDerivations : Module.End ℝ A) a :=
  rfl

/-- Lift a continuous derivation family into M1A/NCG's `LieSystem A 𝔤`. -/
def toDerivationDifferentialLieSystem
    {𝔤 : Type*} [AddCommGroup 𝔤]
    (derivation : 𝔤 → FrechetOperatorDerivation ℝ A)
    (derivation_zero : derivation 0 = 0)
    (derivation_add : ∀ D E, derivation (D + E) = derivation D + derivation E)
    (bracket : 𝔤 → 𝔤 → 𝔤)
    (hbracket : ∀ D E a,
      derivation D (derivation E a) - derivation E (derivation D a) =
        derivation (bracket D E) a)
    (bracket_zero : ∀ D, bracket 0 D = 0)
    (bracket_add_left : ∀ D E F, bracket (D + E) F = bracket D F + bracket E F)
    (bracket_add_right : ∀ D E F, bracket D (E + F) = bracket D E + bracket D F)
    (bracket_neg_left : ∀ D E, bracket (-D) E = -bracket D E)
    (bracket_neg_right : ∀ D E, bracket D (-E) = -bracket D E)
    (bracket_skew : ∀ D E, bracket E D = -bracket D E)
    (bracket_jacobi : ∀ D E F,
      bracket D (bracket E F) + bracket E (bracket F D) + bracket F (bracket D E) = 0) :
    InfoGeometry.NCG.DerivationDifferential.LieSystem A 𝔤 where
  toSystem := toDerivationDifferentialSystem derivation bracket hbracket
  derivation_zero := by
    apply NCDerivation.ext
    intro a
    change toNCDerivation (derivation 0) a = 0
    rw [derivation_zero]
    rfl
  derivation_add := fun D E => by
    apply NCDerivation.ext
    intro a
    change toNCDerivation (derivation (D + E)) a =
      toNCDerivation (derivation D) a + toNCDerivation (derivation E) a
    rw [derivation_add]
    rfl
  bracket_zero := bracket_zero
  bracket_add_left := bracket_add_left
  bracket_add_right := bracket_add_right
  bracket_neg_left := bracket_neg_left
  bracket_neg_right := bracket_neg_right
  bracket_skew := bracket_skew
  bracket_jacobi := bracket_jacobi

theorem toDerivationDifferentialLieSystem_toSystem
    {𝔤 : Type*} [AddCommGroup 𝔤]
    (derivation : 𝔤 → FrechetOperatorDerivation ℝ A)
    (derivation_zero : derivation 0 = 0)
    (derivation_add : ∀ D E, derivation (D + E) = derivation D + derivation E)
    (bracket : 𝔤 → 𝔤 → 𝔤)
    (hbracket : ∀ D E a,
      derivation D (derivation E a) - derivation E (derivation D a) =
        derivation (bracket D E) a)
    (bracket_zero : ∀ D, bracket 0 D = 0)
    (bracket_add_left : ∀ D E F, bracket (D + E) F = bracket D F + bracket E F)
    (bracket_add_right : ∀ D E F, bracket D (E + F) = bracket D E + bracket D F)
    (bracket_neg_left : ∀ D E, bracket (-D) E = -bracket D E)
    (bracket_neg_right : ∀ D E, bracket D (-E) = -bracket D E)
    (bracket_skew : ∀ D E, bracket E D = -bracket D E)
    (bracket_jacobi : ∀ D E F,
      bracket D (bracket E F) + bracket E (bracket F D) + bracket F (bracket D E) = 0) :
    (toDerivationDifferentialLieSystem derivation derivation_zero derivation_add bracket hbracket
      bracket_zero bracket_add_left bracket_add_right bracket_neg_left bracket_neg_right
      bracket_skew bracket_jacobi).toSystem =
      toDerivationDifferentialSystem derivation bracket hbracket :=
  rfl

/-- Unconditional faithful `DerivationLieLane ℤ A` on the image of
`toDerivationDifferentialLieSystem`. -/
def toDerivationDifferentialLieSystem_derivationLieLane
    {𝔤 : Type*} [AddCommGroup 𝔤]
    (derivation : 𝔤 → FrechetOperatorDerivation ℝ A)
    (derivation_zero : derivation 0 = 0)
    (derivation_add : ∀ D E, derivation (D + E) = derivation D + derivation E)
    (bracket : 𝔤 → 𝔤 → 𝔤)
    (hbracket : ∀ D E a,
      derivation D (derivation E a) - derivation E (derivation D a) =
        derivation (bracket D E) a)
    (bracket_zero : ∀ D, bracket 0 D = 0)
    (bracket_add_left : ∀ D E F, bracket (D + E) F = bracket D F + bracket E F)
    (bracket_add_right : ∀ D E F, bracket D (E + F) = bracket D E + bracket D F)
    (bracket_neg_left : ∀ D E, bracket (-D) E = -bracket D E)
    (bracket_neg_right : ∀ D E, bracket D (-E) = -bracket D E)
    (bracket_skew : ∀ D E, bracket E D = -bracket D E)
    (bracket_jacobi : ∀ D E F,
      bracket D (bracket E F) + bracket E (bracket F D) + bracket F (bracket D E) = 0) :
    DerivationLieLane ℤ A :=
  lieSystemToDerivationLieLane
    (toDerivationDifferentialLieSystem derivation derivation_zero derivation_add bracket hbracket
      bracket_zero bracket_add_left bracket_add_right bracket_neg_left bracket_neg_right
      bracket_skew bracket_jacobi)

/-- Non-faithful `LieActionLane ℤ A` on `toDerivationDifferentialLieSystem` when
`bracket g g = 0`. -/
def toDerivationDifferentialLieSystem_lieActionLane
    {𝔤 : Type*} [AddCommGroup 𝔤]
    (derivation : 𝔤 → FrechetOperatorDerivation ℝ A)
    (derivation_zero : derivation 0 = 0)
    (derivation_add : ∀ D E, derivation (D + E) = derivation D + derivation E)
    (bracket : 𝔤 → 𝔤 → 𝔤)
    (hbracket : ∀ D E a,
      derivation D (derivation E a) - derivation E (derivation D a) =
        derivation (bracket D E) a)
    (bracket_zero : ∀ D, bracket 0 D = 0)
    (bracket_add_left : ∀ D E F, bracket (D + E) F = bracket D F + bracket E F)
    (bracket_add_right : ∀ D E F, bracket D (E + F) = bracket D E + bracket D F)
    (bracket_neg_left : ∀ D E, bracket (-D) E = -bracket D E)
    (bracket_neg_right : ∀ D E, bracket D (-E) = -bracket D E)
    (bracket_skew : ∀ D E, bracket E D = -bracket D E)
    (bracket_jacobi : ∀ D E F,
      bracket D (bracket E F) + bracket E (bracket F D) + bracket F (bracket D E) = 0)
    (hself : ∀ g : 𝔤, bracket g g = 0) :
    LieActionLane ℤ A :=
  lieSystemToLieActionLane
    (toDerivationDifferentialLieSystem derivation derivation_zero derivation_add bracket hbracket
      bracket_zero bracket_add_left bracket_add_right bracket_neg_left bracket_neg_right
      bracket_skew bracket_jacobi)
    hself

/-- Canonical `LieSystem A A` realizing `innerFrechetSystem A`. -/
def innerFrechetLieSystem (A : Type*) [NormedRing A] [NormedAlgebra ℝ A] [CompleteSpace A] :
    InfoGeometry.NCG.DerivationDifferential.LieSystem A A :=
  toDerivationDifferentialLieSystem
    (fun a : A => ofInner a)
    (by ext x; simp [ofInner_apply])
    (fun a b => by ext x; simp only [ofInner_apply, add_apply]; noncomm_ring)
    (fun a b : A => a * b - b * a)
    (by intro a b x; simp only [ofInner_apply]; noncomm_ring)
    (fun D => by simp)
    (fun D E F => by noncomm_ring)
    (fun D E F => by noncomm_ring)
    (fun D E => by noncomm_ring)
    (fun D E => by noncomm_ring)
    (fun D E => by noncomm_ring)
    (fun D E F => by noncomm_ring)

theorem innerFrechetLieSystem_toSystem (A : Type*)
    [NormedRing A] [NormedAlgebra ℝ A] [CompleteSpace A] :
    (innerFrechetLieSystem A).toSystem = innerFrechetSystem A :=
  rfl

/-- Unconditional faithful `DerivationLieLane ℤ A` on the image of `innerFrechetLieSystem A`. -/
def innerFrechetDerivationLieLane (A : Type*)
    [NormedRing A] [NormedAlgebra ℝ A] [CompleteSpace A] : DerivationLieLane ℤ A :=
  lieSystemToDerivationLieLane (innerFrechetLieSystem A)

/-- Non-faithful `LieActionLane ℤ A` on `innerFrechetLieSystem A` (`sub_self`). -/
def innerFrechetLieActionLane (A : Type*)
    [NormedRing A] [NormedAlgebra ℝ A] [CompleteSpace A] : LieActionLane ℤ A :=
  lieSystemToLieActionLane (innerFrechetLieSystem A) (fun g => sub_self (g * g))

theorem frechetOperatorDerivationOfThermodynamic_toDerivations
    [FiniteDimensional ℝ A] (D : ThermodynamicOperatorDerivation A) :
    ((frechetOperatorDerivationOfThermodynamic D).toDerivations : Module.End ℝ A) =
      D.toLinearMap := by
  ext a
  rfl

end RealBridges

end SpineAdapters

end FrechetOperatorDerivation

end InfoGeometry.Optics.OperatorDerivationForms
