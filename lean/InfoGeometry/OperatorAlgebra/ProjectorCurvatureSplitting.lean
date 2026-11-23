/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.OperatorAlgebra.PeirceSpine.Basic
import InfoGeometry.OperatorAlgebra.DerivationDifferentialForms
import InfoGeometry.OperatorAlgebra.DerivationMatrixGeometry
import InfoGeometry.Clifford.Cl11TensorTowerLimit
import InfoGeometry.Canonical.TensorLimitExactConnection
import InfoGeometry.Canonical.TensorExactCurvatureNonzero

/-!
# Parameter-dependent projector differentiation and two-direction projected curvature

For an idempotent `P : A` (`P * P = P`) in an arbitrary associative ring `A` and
Leibniz derivations `D : A → A` (`D (a * b) = D a * b + a * D b`), differentiating
`P * P = P` yields `P * D P + D P * P = D P`, forcing the diagonal Peirce corners
to vanish (`P * D P * P = 0` and `(1 - P) * D P * (1 - P) = 0`) and splitting

`D_i P = X_i + Y_i`,
where `X_i := coneMinus P (D_i P) = (1 - P) * D_i P * P`
and `Y_i := conePlus P (D_i P) = P * D_i P * (1 - P)`.

Consequently, the two-direction projected curvature (adiabatic/Berry-type curvature
on the `P`-image) satisfies
`P * [D_1 P, D_2 P] * P = Y_1 * X_2 - Y_2 * X_1`,
while the complementary block satisfies
`(1 - P) * [D_1 P, D_2 P] * (1 - P) = X_1 * Y_2 - X_2 * Y_1`.

Specializations are provided for `NonAssocDerivation.derivations`,
`DerivationLieLane`, `StarRing` involutions (`Y_i = star X_i`), cyclic traces,
`Cl11TensorTowerLimit.Stage` and `Cl11TensorTowerLimit.Limit`, and concrete
nonzero `2 × 2` and `⋆`-preserving `3 × 3` real matrix witnesses.
-/

set_option autoImplicit false

noncomputable section

namespace InfoGeometry.OperatorAlgebra.ProjectorCurvatureSplitting

open InfoGeometry.OperatorAlgebra.PeirceSpine
open InfoGeometry.Algebra
open InfoGeometry.Algebra.DerivationLieLane
open InfoGeometry.OperatorAlgebra.DerivationDifferentialForms
open InfoGeometry.OperatorAlgebra.DerivationMatrixGeometry
open InfoGeometry.Clifford.Cl11TensorTowerLimit
open InfoGeometry.Canonical.TensorStageExactConnection
open InfoGeometry.Canonical.TensorLimitExactConnection
open InfoGeometry.Canonical.TensorExactCurvatureNonzero
open InfoGeometry.Canonical.RealStarColimitUniversal
open InfoGeometry.Examples.RealMatrixModeWitness

/-! ## Section 1: General associative ring projector differentiation -/

section RingProjectorCurvature

variable {A : Type*} [Ring A]

/-- Differentiating `P * P = P` along a Leibniz map `D` yields `P * D P + D P * P = D P`. -/
theorem projector_deriv_anticomm_eq {P : A} (hP : P * P = P)
    (D : A → A) (hD : ∀ a b : A, D (a * b) = D a * b + a * D b) :
    P * D P + D P * P = D P := by
  have h := hD P P
  rw [hP] at h
  rw [add_comm] at h
  exact h.symm

/-- Every element `T` satisfying `P * T + T * P = T` has vanishing diagonal Peirce corners. -/
theorem projector_tangent_diagonal_corners_zero {P T : A} (hP : P * P = P)
    (hT : P * T + T * P = T) :
    P * T * P = 0 ∧ (1 - P) * T * (1 - P) = 0 := by
  have hPT : P * T * P = 0 := by
    have hmul := congrArg (fun z : A => P * z * P) hT
    have hcalc : P * T * P + P * T * P = P * T * P := by
      calc
        P * T * P + P * T * P = (P * P) * T * P + P * T * (P * P) := by rw [hP]
        _ = P * (P * T + T * P) * P := by noncomm_ring
        _ = P * T * P := hmul
    exact add_left_cancel (by simpa only [add_zero] using hcalc)
  have h1PT : (1 - P) * T * (1 - P) = 0 := by
    calc
      (1 - P) * T * (1 - P) = T - (P * T + T * P) + P * T * P := by noncomm_ring
      _ = 0 := by rw [hT, hPT, sub_self, zero_add]
  exact ⟨hPT, h1PT⟩

/-- For any Leibniz map `D`, the diagonal Peirce corners of `D P` vanish. -/
theorem projector_deriv_diagonal_corners_zero {P : A} (hP : P * P = P)
    (D : A → A) (hD : ∀ a b : A, D (a * b) = D a * b + a * D b) :
    P * D P * P = 0 ∧ (1 - P) * D P * (1 - P) = 0 :=
  projector_tangent_diagonal_corners_zero hP (projector_deriv_anticomm_eq hP D hD)

/-- The Peirce-even part of `D P` vanishes. -/
theorem projector_deriv_evenGrade_zero {P : A} (hP : P * P = P)
    (D : A → A) (hD : ∀ a b : A, D (a * b) = D a * b + a * D b) :
    evenGrade P (D P) = 0 := by
  rcases projector_deriv_diagonal_corners_zero hP D hD with ⟨h11, h00⟩
  simp only [evenGrade, h11, h00, add_zero]

/-- `D P` is purely Peirce-odd. -/
theorem projector_deriv_oddGrade_eq {P : A} (hP : P * P = P)
    (D : A → A) (hD : ∀ a b : A, D (a * b) = D a * b + a * D b) :
    oddGrade P (D P) = D P := by
  have hsum := (grade_projection_laws hP (D P)).2.2.2.2
  rw [projector_deriv_evenGrade_zero hP D hD, zero_add] at hsum
  exact hsum

/-- **F11 Core Splitting**: `D P = X + Y` where `X = coneMinus P (D P) = (1 - P) * D P * P`
and `Y = conePlus P (D P) = P * D P * (1 - P)`. -/
theorem projector_deriv_peirce_split {P : A} (hP : P * P = P)
    (D : A → A) (hD : ∀ a b : A, D (a * b) = D a * b + a * D b) :
    D P = coneMinus P (D P) + conePlus P (D P) := by
  have hodd := projector_deriv_oddGrade_eq hP D hD
  simpa only [oddGrade, coneMinus, conePlus, add_comm] using hodd.symm

/-- **F11 Projected Two-Direction Curvature**:
`P * [D₁ P, D₂ P] * P = Y₁ * X₂ - Y₂ * X₁`,
where `X_i := coneMinus P (D_i P) = (1 - P) * D_i P * P`
and `Y_i := conePlus P (D_i P) = P * D_i P * (1 - P)`. -/
theorem projected_two_direction_curvature {P : A} (hP : P * P = P)
    (D₁ D₂ : A → A)
    (hD₁ : ∀ a b : A, D₁ (a * b) = D₁ a * b + a * D₁ b)
    (hD₂ : ∀ a b : A, D₂ (a * b) = D₂ a * b + a * D₂ b) :
    P * (D₁ P * D₂ P - D₂ P * D₁ P) * P =
      conePlus P (D₁ P) * coneMinus P (D₂ P) -
        conePlus P (D₂ P) * coneMinus P (D₁ P) := by
  have h₁ := projector_deriv_peirce_split hP D₁ hD₁
  have h₂ := projector_deriv_peirce_split hP D₂ hD₂
  calc
    P * (D₁ P * D₂ P - D₂ P * D₁ P) * P =
        P * ((coneMinus P (D₁ P) + conePlus P (D₁ P)) *
              (coneMinus P (D₂ P) + conePlus P (D₂ P)) -
            (coneMinus P (D₂ P) + conePlus P (D₂ P)) *
              (coneMinus P (D₁ P) + conePlus P (D₁ P))) * P := by
          conv_lhs => rw [h₁, h₂]
    _ = conePlus P (D₁ P) * coneMinus P (D₂ P) -
          conePlus P (D₂ P) * coneMinus P (D₁ P) := by
          peirce_nf hP

/-- Complementary `(1 - P)` block of the two-direction curvature:
`(1 - P) * [D₁ P, D₂ P] * (1 - P) = X₁ * Y₂ - X₂ * Y₁`. -/
theorem projected_complement_two_direction_curvature {P : A} (hP : P * P = P)
    (D₁ D₂ : A → A)
    (hD₁ : ∀ a b : A, D₁ (a * b) = D₁ a * b + a * D₁ b)
    (hD₂ : ∀ a b : A, D₂ (a * b) = D₂ a * b + a * D₂ b) :
    (1 - P) * (D₁ P * D₂ P - D₂ P * D₁ P) * (1 - P) =
      coneMinus P (D₁ P) * conePlus P (D₂ P) -
        coneMinus P (D₂ P) * conePlus P (D₁ P) := by
  have h₁ := projector_deriv_peirce_split hP D₁ hD₁
  have h₂ := projector_deriv_peirce_split hP D₂ hD₂
  calc
    (1 - P) * (D₁ P * D₂ P - D₂ P * D₁ P) * (1 - P) =
        (1 - P) * ((coneMinus P (D₁ P) + conePlus P (D₁ P)) *
                    (coneMinus P (D₂ P) + conePlus P (D₂ P)) -
                  (coneMinus P (D₂ P) + conePlus P (D₂ P)) *
                    (coneMinus P (D₁ P) + conePlus P (D₁ P))) * (1 - P) := by
          conv_lhs => rw [h₁, h₂]
    _ = coneMinus P (D₁ P) * conePlus P (D₂ P) -
          coneMinus P (D₂ P) * conePlus P (D₁ P) := by
          peirce_nf hP

/-- Full Peirce decomposition of the commutator `[D₁ P, D₂ P]` into its `P`-block
and `(1 - P)`-block. -/
theorem projector_deriv_commutator_decomposition {P : A} (hP : P * P = P)
    (D₁ D₂ : A → A)
    (hD₁ : ∀ a b : A, D₁ (a * b) = D₁ a * b + a * D₁ b)
    (hD₂ : ∀ a b : A, D₂ (a * b) = D₂ a * b + a * D₂ b) :
    D₁ P * D₂ P - D₂ P * D₁ P =
      (conePlus P (D₁ P) * coneMinus P (D₂ P) -
        conePlus P (D₂ P) * coneMinus P (D₁ P)) +
      (coneMinus P (D₁ P) * conePlus P (D₂ P) -
        coneMinus P (D₂ P) * conePlus P (D₁ P)) := by
  have h₁ := projector_deriv_peirce_split hP D₁ hD₁
  have h₂ := projector_deriv_peirce_split hP D₂ hD₂
  calc
    D₁ P * D₂ P - D₂ P * D₁ P =
        (coneMinus P (D₁ P) + conePlus P (D₁ P)) *
          (coneMinus P (D₂ P) + conePlus P (D₂ P)) -
        (coneMinus P (D₂ P) + conePlus P (D₂ P)) *
          (coneMinus P (D₁ P) + conePlus P (D₁ P)) := by
          conv_lhs => rw [h₁, h₂]
    _ = (conePlus P (D₁ P) * coneMinus P (D₂ P) -
          conePlus P (D₂ P) * coneMinus P (D₁ P)) +
        (coneMinus P (D₁ P) * conePlus P (D₂ P) -
          coneMinus P (D₂ P) * conePlus P (D₁ P)) := by
          peirce_nf hP

/-- The commutator `[D₁ P, D₂ P]` is Peirce-even and commutes with `P`. -/
theorem projector_deriv_commutator_evenGrade {P : A} (hP : P * P = P)
    (D₁ D₂ : A → A)
    (hD₁ : ∀ a b : A, D₁ (a * b) = D₁ a * b + a * D₁ b)
    (hD₂ : ∀ a b : A, D₂ (a * b) = D₂ a * b + a * D₂ b) :
    let C := D₁ P * D₂ P - D₂ P * D₁ P
    evenGrade P C = C ∧ oddGrade P C = 0 ∧ P * C = C * P := by
  have hdecomp := projector_deriv_commutator_decomposition hP D₁ D₂ hD₁ hD₂
  dsimp only
  rw [hdecomp]
  refine ⟨?_, ?_, ?_⟩
  · peirce_nf hP
  · peirce_nf hP
  · have hL : P * ((conePlus P (D₁ P) * coneMinus P (D₂ P) -
        conePlus P (D₂ P) * coneMinus P (D₁ P)) +
      (coneMinus P (D₁ P) * conePlus P (D₂ P) -
        coneMinus P (D₂ P) * conePlus P (D₁ P))) =
      conePlus P (D₁ P) * coneMinus P (D₂ P) -
        conePlus P (D₂ P) * coneMinus P (D₁ P) := by peirce_nf hP
    have hR : ((conePlus P (D₁ P) * coneMinus P (D₂ P) -
        conePlus P (D₂ P) * coneMinus P (D₁ P)) +
      (coneMinus P (D₁ P) * conePlus P (D₂ P) -
        coneMinus P (D₂ P) * conePlus P (D₁ P))) * P =
      conePlus P (D₁ P) * coneMinus P (D₂ P) -
        conePlus P (D₂ P) * coneMinus P (D₁ P) := by peirce_nf hP
    rw [hL, hR]

end RingProjectorCurvature

/-! ## Section 2: `NonAssocDerivation` and `DerivationLieLane` specializations -/

section DerivationLaneSpecializations

variable {R A : Type*} [CommRing R] [Ring A] [Algebra R A]

/-- Specialization of `projector_deriv_peirce_split` to `NonAssocDerivation.derivations R A`. -/
theorem nonAssocDerivation_projector_deriv_peirce_split
    {P : A} (hP : P * P = P) (D : NonAssocDerivation.derivations R A) :
    (D : Module.End R A) P =
      coneMinus P ((D : Module.End R A) P) + conePlus P ((D : Module.End R A) P) :=
  projector_deriv_peirce_split hP (D : Module.End R A)
    (NonAssocDerivation.derivations_leibniz R A D)

/-- Specialization of `projected_two_direction_curvature` to `NonAssocDerivation.derivations R A`. -/
theorem nonAssocDerivation_projected_two_direction_curvature
    {P : A} (hP : P * P = P) (D₁ D₂ : NonAssocDerivation.derivations R A) :
    P * ((D₁ : Module.End R A) P * (D₂ : Module.End R A) P -
          (D₂ : Module.End R A) P * (D₁ : Module.End R A) P) * P =
      conePlus P ((D₁ : Module.End R A) P) * coneMinus P ((D₂ : Module.End R A) P) -
        conePlus P ((D₂ : Module.End R A) P) * coneMinus P ((D₁ : Module.End R A) P) :=
  projected_two_direction_curvature hP (D₁ : Module.End R A) (D₂ : Module.End R A)
    (NonAssocDerivation.derivations_leibniz R A D₁)
    (NonAssocDerivation.derivations_leibniz R A D₂)

/-- Specialization of `projector_deriv_peirce_split` to any `DerivationLieLane R A`. -/
theorem lane_projector_deriv_peirce_split (K : DerivationLieLane R A)
    {P : A} (hP : P * P = P) (x : K.L) :
    K.operatorAction x P =
      coneMinus P (K.operatorAction x P) + conePlus P (K.operatorAction x P) :=
  projector_deriv_peirce_split hP (K.operatorAction x) (K.operatorAction_leibniz x)

/-- Specialization of `projected_two_direction_curvature` to any `DerivationLieLane R A`. -/
theorem lane_projected_two_direction_curvature (K : DerivationLieLane R A)
    {P : A} (hP : P * P = P) (x y : K.L) :
    P * (K.operatorAction x P * K.operatorAction y P -
          K.operatorAction y P * K.operatorAction x P) * P =
      conePlus P (K.operatorAction x P) * coneMinus P (K.operatorAction y P) -
        conePlus P (K.operatorAction y P) * coneMinus P (K.operatorAction x P) :=
  projected_two_direction_curvature hP (K.operatorAction x) (K.operatorAction y)
    (K.operatorAction_leibniz x) (K.operatorAction_leibniz y)

/-- Connection between `projected_two_direction_curvature` and the exact CE one-form
curvature `connectionCurvature K (exteriorDerivativeZero K P)`. -/
theorem lane_projected_exactCurvature (K : DerivationLieLane R A)
    {P : A} (hP : P * P = P) (x y : K.L) :
    P * connectionCurvature K (exteriorDerivativeZero K P) x y * P =
      conePlus P (K.operatorAction x P) * coneMinus P (K.operatorAction y P) -
        conePlus P (K.operatorAction y P) * coneMinus P (K.operatorAction x P) := by
  rw [connectionCurvature, exteriorDerivativeOne_exteriorDerivativeZero, zero_add,
    connectionWedgeSquare_apply]
  exact lane_projected_two_direction_curvature K hP x y

end DerivationLaneSpecializations

/-! ## Section 3: `StarRing` adjoint and cyclic trace specializations -/

section StarAndTraceSpecializations

section StarSpec

variable {A : Type*} [Ring A] [StarRing A]

/-- For self-adjoint `P` and `T`, `star (coneMinus P T) = conePlus P T`. -/
theorem star_coneMinus_eq_conePlus_of_selfAdjoint {P T : A}
    (hPs : star P = P) (hTs : star T = T) :
    star (coneMinus P T) = conePlus P T := by
  simp only [coneMinus, conePlus, star_mul, star_sub, star_one, hPs, hTs, mul_assoc]

/-- For self-adjoint `P` and `T`, `star (conePlus P T) = coneMinus P T`. -/
theorem star_conePlus_eq_coneMinus_of_selfAdjoint {P T : A}
    (hPs : star P = P) (hTs : star T = T) :
    star (conePlus P T) = coneMinus P T := by
  simp only [conePlus, coneMinus, star_mul, star_sub, star_one, hPs, hTs, mul_assoc]

/-- When `star P = P` and `D` commutes with `star`, `star X = Y` and `star Y = X`. -/
theorem star_projector_deriv_corners {P : A} (hPs : star P = P)
    (D : A → A) (hDstar : ∀ a : A, D (star a) = star (D a)) :
    star (coneMinus P (D P)) = conePlus P (D P) ∧
      star (conePlus P (D P)) = coneMinus P (D P) := by
  have hDP : star (D P) = D P := by
    rw [← hDstar P, hPs]
  exact ⟨star_coneMinus_eq_conePlus_of_selfAdjoint hPs hDP,
    star_conePlus_eq_coneMinus_of_selfAdjoint hPs hDP⟩

/-- Adjoint specialization of `projected_two_direction_curvature`:
`P * [D₁ P, D₂ P] * P = star X₁ * X₂ - star X₂ * X₁`. -/
theorem projected_two_direction_curvature_star {P : A}
    (hP : P * P = P) (hPs : star P = P)
    (D₁ D₂ : A → A)
    (hD₁ : ∀ a b : A, D₁ (a * b) = D₁ a * b + a * D₁ b)
    (hD₂ : ∀ a b : A, D₂ (a * b) = D₂ a * b + a * D₂ b)
    (hD₁star : ∀ a : A, D₁ (star a) = star (D₁ a))
    (hD₂star : ∀ a : A, D₂ (star a) = star (D₂ a)) :
    P * (D₁ P * D₂ P - D₂ P * D₁ P) * P =
      star (coneMinus P (D₁ P)) * coneMinus P (D₂ P) -
        star (coneMinus P (D₂ P)) * coneMinus P (D₁ P) := by
  rw [projected_two_direction_curvature hP D₁ D₂ hD₁ hD₂,
    (star_projector_deriv_corners hPs D₁ hD₁star).1,
    (star_projector_deriv_corners hPs D₂ hD₂star).1]

/-- Adjoint specialization on the complementary block:
`(1 - P) * [D₁ P, D₂ P] * (1 - P) = X₁ * star X₂ - X₂ * star X₁`. -/
theorem projected_complement_two_direction_curvature_star {P : A}
    (hP : P * P = P) (hPs : star P = P)
    (D₁ D₂ : A → A)
    (hD₁ : ∀ a b : A, D₁ (a * b) = D₁ a * b + a * D₁ b)
    (hD₂ : ∀ a b : A, D₂ (a * b) = D₂ a * b + a * D₂ b)
    (hD₁star : ∀ a : A, D₁ (star a) = star (D₁ a))
    (hD₂star : ∀ a : A, D₂ (star a) = star (D₂ a)) :
    (1 - P) * (D₁ P * D₂ P - D₂ P * D₁ P) * (1 - P) =
      coneMinus P (D₁ P) * star (coneMinus P (D₂ P)) -
        coneMinus P (D₂ P) * star (coneMinus P (D₁ P)) := by
  rw [projected_complement_two_direction_curvature hP D₁ D₂ hD₁ hD₂,
    (star_projector_deriv_corners hPs D₁ hD₁star).1,
    (star_projector_deriv_corners hPs D₂ hD₂star).1]

end StarSpec

section TraceSpec

variable {A S : Type*} [Ring A] [AddCommGroup S]

/-- Any cyclic additive map annihilates the commutator `[D₁ P, D₂ P]`. -/
theorem trace_projector_deriv_commutator_eq_zero (tr : A →+ S)
    (htr : ∀ a b : A, tr (a * b) = tr (b * a))
    (P : A) (D₁ D₂ : A → A) :
    tr (D₁ P * D₂ P - D₂ P * D₁ P) = 0 := by
  rw [map_sub, htr (D₁ P) (D₂ P), sub_self]

/-- Cyclic trace of the projected two-direction curvature. -/
theorem trace_projected_two_direction_curvature (tr : A →+ S)
    {P : A} (hP : P * P = P)
    (D₁ D₂ : A → A)
    (hD₁ : ∀ a b : A, D₁ (a * b) = D₁ a * b + a * D₁ b)
    (hD₂ : ∀ a b : A, D₂ (a * b) = D₂ a * b + a * D₂ b) :
    tr (P * (D₁ P * D₂ P - D₂ P * D₁ P) * P) =
      tr (conePlus P (D₁ P) * coneMinus P (D₂ P)) -
        tr (conePlus P (D₂ P) * coneMinus P (D₁ P)) := by
  rw [projected_two_direction_curvature hP D₁ D₂ hD₁ hD₂, map_sub]

/-- The cyclic traces of the `P`-block and `(1 - P)`-block sum to zero. -/
theorem trace_projected_curvature_add_complement_eq_zero (tr : A →+ S)
    (htr : ∀ a b : A, tr (a * b) = tr (b * a))
    {P : A} (hP : P * P = P)
    (D₁ D₂ : A → A)
    (hD₁ : ∀ a b : A, D₁ (a * b) = D₁ a * b + a * D₁ b)
    (hD₂ : ∀ a b : A, D₂ (a * b) = D₂ a * b + a * D₂ b) :
    tr (P * (D₁ P * D₂ P - D₂ P * D₁ P) * P) +
      tr ((1 - P) * (D₁ P * D₂ P - D₂ P * D₁ P) * (1 - P)) = 0 := by
  rw [← map_add]
  have hsum :
      P * (D₁ P * D₂ P - D₂ P * D₁ P) * P +
        (1 - P) * (D₁ P * D₂ P - D₂ P * D₁ P) * (1 - P) =
        D₁ P * D₂ P - D₂ P * D₁ P := by
    calc
      P * (D₁ P * D₂ P - D₂ P * D₁ P) * P +
          (1 - P) * (D₁ P * D₂ P - D₂ P * D₁ P) * (1 - P) =
          (conePlus P (D₁ P) * coneMinus P (D₂ P) -
            conePlus P (D₂ P) * coneMinus P (D₁ P)) +
          (coneMinus P (D₁ P) * conePlus P (D₂ P) -
            coneMinus P (D₂ P) * conePlus P (D₁ P)) := by
            rw [projected_two_direction_curvature hP D₁ D₂ hD₁ hD₂,
              projected_complement_two_direction_curvature hP D₁ D₂ hD₁ hD₂]
      _ = D₁ P * D₂ P - D₂ P * D₁ P :=
            (projector_deriv_commutator_decomposition hP D₁ D₂ hD₁ hD₂).symm
  rw [hsum]
  exact trace_projector_deriv_commutator_eq_zero tr htr P D₁ D₂

/-- Matrix trace specialization of `trace_projected_two_direction_curvature`. -/
theorem matrix_trace_projected_two_direction_curvature
    {R n : Type*} [CommRing R] [Fintype n] [DecidableEq n]
    {P : Matrix n n R} (hP : P * P = P)
    (D₁ D₂ : Matrix n n R → Matrix n n R)
    (hD₁ : ∀ a b : Matrix n n R, D₁ (a * b) = D₁ a * b + a * D₁ b)
    (hD₂ : ∀ a b : Matrix n n R, D₂ (a * b) = D₂ a * b + a * D₂ b) :
    Matrix.trace (P * (D₁ P * D₂ P - D₂ P * D₁ P) * P) =
      Matrix.trace (conePlus P (D₁ P) * coneMinus P (D₂ P)) -
        Matrix.trace (conePlus P (D₂ P) * coneMinus P (D₁ P)) :=
  trace_projected_two_direction_curvature (Matrix.traceAddMonoidHom n R) hP D₁ D₂ hD₁ hD₂

end TraceSpec

end StarAndTraceSpecializations

/-! ## Section 4: `Cl11TensorTowerLimit.Stage` and `Limit` instantiations -/

section TensorTowerInstantiations

/-- Finite-stage `Cl(1,1)` matrix tower specialization of `projected_two_direction_curvature`. -/
theorem stage_projected_two_direction_curvature (n : ℕ)
    {P : Stage n} (hP : P * P = P)
    (D₁ D₂ : (matrixDerivationsLane ℝ (InfoGeometry.Clifford.TowerMatrix.Idx n)).L) :
    P * ((matrixDerivationsLane ℝ (InfoGeometry.Clifford.TowerMatrix.Idx n)).operatorAction D₁ P *
          (matrixDerivationsLane ℝ (InfoGeometry.Clifford.TowerMatrix.Idx n)).operatorAction D₂ P -
        (matrixDerivationsLane ℝ (InfoGeometry.Clifford.TowerMatrix.Idx n)).operatorAction D₂ P *
          (matrixDerivationsLane ℝ (InfoGeometry.Clifford.TowerMatrix.Idx n)).operatorAction D₁ P) * P =
      conePlus P ((matrixDerivationsLane ℝ (InfoGeometry.Clifford.TowerMatrix.Idx n)).operatorAction D₁ P) *
          coneMinus P ((matrixDerivationsLane ℝ (InfoGeometry.Clifford.TowerMatrix.Idx n)).operatorAction D₂ P) -
        conePlus P ((matrixDerivationsLane ℝ (InfoGeometry.Clifford.TowerMatrix.Idx n)).operatorAction D₂ P) *
          coneMinus P ((matrixDerivationsLane ℝ (InfoGeometry.Clifford.TowerMatrix.Idx n)).operatorAction D₁ P) :=
  lane_projected_two_direction_curvature
    (matrixDerivationsLane ℝ (InfoGeometry.Clifford.TowerMatrix.Idx n)) hP D₁ D₂

/-- Direct-limit specialization on `Cl11TensorTowerLimit.Limit` for arbitrary Leibniz derivations. -/
theorem limit_projected_two_direction_curvature
    {P : Limit} (hP : P * P = P) (D₁ D₂ : limitDerivationsLane.L) :
    P * (limitDerivationsLane.operatorAction D₁ P * limitDerivationsLane.operatorAction D₂ P -
          limitDerivationsLane.operatorAction D₂ P * limitDerivationsLane.operatorAction D₁ P) * P =
      conePlus P (limitDerivationsLane.operatorAction D₁ P) *
          coneMinus P (limitDerivationsLane.operatorAction D₂ P) -
        conePlus P (limitDerivationsLane.operatorAction D₂ P) *
          coneMinus P (limitDerivationsLane.operatorAction D₁ P) :=
  lane_projected_two_direction_curvature limitDerivationsLane hP D₁ D₂

/-- Direct-limit `StarRing` specialization for `⋆`-preserving derivations on `Limit`. -/
theorem limit_projected_two_direction_curvature_star
    {P : Limit} (hP : P * P = P) (hPs : star P = P)
    (D₁ D₂ : limitDerivationsLane.L)
    (hD₁star : ∀ a : Limit,
      limitDerivationsLane.operatorAction D₁ (star a) =
        star (limitDerivationsLane.operatorAction D₁ a))
    (hD₂star : ∀ a : Limit,
      limitDerivationsLane.operatorAction D₂ (star a) =
        star (limitDerivationsLane.operatorAction D₂ a)) :
    P * (limitDerivationsLane.operatorAction D₁ P * limitDerivationsLane.operatorAction D₂ P -
          limitDerivationsLane.operatorAction D₂ P * limitDerivationsLane.operatorAction D₁ P) * P =
      star (coneMinus P (limitDerivationsLane.operatorAction D₁ P)) *
          coneMinus P (limitDerivationsLane.operatorAction D₂ P) -
        star (coneMinus P (limitDerivationsLane.operatorAction D₂ P)) *
          coneMinus P (limitDerivationsLane.operatorAction D₁ P) :=
  projected_two_direction_curvature_star hP hPs
    (limitDerivationsLane.operatorAction D₁) (limitDerivationsLane.operatorAction D₂)
    (limitDerivationsLane.operatorAction_leibniz D₁)
    (limitDerivationsLane.operatorAction_leibniz D₂)
    hD₁star hD₂star

/-- Concrete dense-mode witness in `Cl11TensorTowerLimit.Limit`:
the projected two-direction curvature of `P = ofStage 2 p` along the inner derivations
`x` and `star x` equals `-P` and is nonzero. -/
theorem limit_denseMode_projected_curvature :
    let P := ofStage 2 p
    let D₁ := limitInnerLieHom (ofStage 2 x)
    let D₂ := limitInnerLieHom (ofStage 2 (star x))
    P * (limitDerivationsLane.operatorAction D₁ P * limitDerivationsLane.operatorAction D₂ P -
          limitDerivationsLane.operatorAction D₂ P * limitDerivationsLane.operatorAction D₁ P) * P =
      -P ∧
    P * (limitDerivationsLane.operatorAction D₁ P * limitDerivationsLane.operatorAction D₂ P -
          limitDerivationsLane.operatorAction D₂ P * limitDerivationsLane.operatorAction D₁ P) * P ≠
      0 := by
  have hP : ofStage 2 p * ofStage 2 p = ofStage 2 p :=
    limit_idempotent p_isIdempotentElem
  have hp_ne : p ≠ 0 := by
    intro h
    have hh : p (((0 : Fin 1), 0), 0) (((0 : Fin 1), 0), 0) = 0 :=
      congrArg (fun M : Stage 2 => M (((0 : Fin 1), 0), 0) (((0 : Fin 1), 0), 0)) h
    norm_num [p] at hh
  have hP_ne : ofStage 2 p ≠ 0 :=
    fun h => hp_ne ((ofStage_eq_zero_iff 2 p).mp h)
  have hpx : ofStage 2 p * ofStage 2 x = ofStage 2 x := by
    rw [← ofStage_mul, p_mul_x]
  have hxp : ofStage 2 x * ofStage 2 p = 0 := by
    rw [← ofStage_mul, x_mul_p, ofStage_zero]
  have hxsx : ofStage 2 x * ofStage 2 (star x) = ofStage 2 p := by
    rw [← ofStage_mul, x_mul_star_x]
  have hsxp : ofStage 2 (star x) * ofStage 2 p = ofStage 2 (star x) := by
    have hs : star x * p = star x := by
      simpa only [star_mul, p_isSelfAdjoint.star_eq, star_star] using congrArg star p_mul_x
    rw [← ofStage_mul, hs]
  have hpsx : ofStage 2 p * ofStage 2 (star x) = 0 := by
    have hs : p * star x = 0 := by
      simpa only [star_mul, p_isSelfAdjoint.star_eq, star_zero] using congrArg star x_mul_p
    rw [← ofStage_mul, hs, ofStage_zero]
  have hD₁P : limitDerivationsLane.operatorAction (limitInnerLieHom (ofStage 2 x)) (ofStage 2 p) =
      -(ofStage 2 x) := by
    change ofStage 2 x * ofStage 2 p - ofStage 2 p * ofStage 2 x = -(ofStage 2 x)
    rw [hxp, hpx, zero_sub]
  have hD₂P : limitDerivationsLane.operatorAction
      (limitInnerLieHom (ofStage 2 (star x))) (ofStage 2 p) = ofStage 2 (star x) := by
    change ofStage 2 (star x) * ofStage 2 p - ofStage 2 p * ofStage 2 (star x) = ofStage 2 (star x)
    rw [hsxp, hpsx, sub_zero]
  have heq :
      ofStage 2 p *
          (limitDerivationsLane.operatorAction (limitInnerLieHom (ofStage 2 x)) (ofStage 2 p) *
              limitDerivationsLane.operatorAction (limitInnerLieHom (ofStage 2 (star x)))
                (ofStage 2 p) -
            limitDerivationsLane.operatorAction (limitInnerLieHom (ofStage 2 (star x)))
                (ofStage 2 p) *
              limitDerivationsLane.operatorAction (limitInnerLieHom (ofStage 2 x)) (ofStage 2 p)) *
          ofStage 2 p = -(ofStage 2 p) := by
    rw [limit_projected_two_direction_curvature hP
      (limitInnerLieHom (ofStage 2 x)) (limitInnerLieHom (ofStage 2 (star x)))]
    rw [hD₁P, hD₂P]
    have hc1 : conePlus (ofStage 2 p) (-(ofStage 2 x)) = -(ofStage 2 x) := by
      simp only [conePlus, mul_neg, neg_mul, hpx, mul_sub, mul_one, hxp, neg_zero, sub_zero]
    have hc2 : coneMinus (ofStage 2 p) (ofStage 2 (star x)) = ofStage 2 (star x) := by
      simp only [coneMinus, sub_mul, one_mul, hpsx, sub_zero, hsxp]
    have hc3 : conePlus (ofStage 2 p) (ofStage 2 (star x)) = 0 := by
      simp only [conePlus, hpsx, zero_mul]
    rw [hc1, hc2, hc3, zero_mul, sub_zero, neg_mul, hxsx]
  refine ⟨heq, ?_⟩
  rw [heq, neg_ne_zero]
  exact hP_ne

end TensorTowerInstantiations

/-! ## Section 5: Concrete finite matrix witnesses (including OpenGauss T16 non-commutativity) -/

section ConcreteMatrixWitnesses

abbrev Mat2R := Matrix (Fin 2) (Fin 2) ℝ
abbrev Mat3R := Matrix (Fin 3) (Fin 3) ℝ

def mat2P : Mat2R := !![1, 0; 0, 0]
def mat2E01 : Mat2R := !![0, 1; 0, 0]
def mat2E10 : Mat2R := !![0, 0; 1, 0]

/-- Explicit `Fin 2` real matrix non-commutativity witness (Trap T16). -/
theorem mat2_noncommutative : mat2E01 * mat2E10 ≠ mat2E10 * mat2E01 := by
  intro h
  have hh := congrArg (fun M : Mat2R => M 0 0) h
  norm_num [mat2E01, mat2E10, Matrix.mul_apply, Fin.sum_univ_two] at hh

theorem mat2P_idempotent : mat2P * mat2P = mat2P := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [mat2P, Matrix.mul_apply, Fin.sum_univ_two]

/-- On `M₂(ℝ)`, the projected two-direction curvature of `mat2P` along inner derivations
`E₀₁` and `E₁₀` equals `-mat2P`. -/
theorem mat2_projected_curvature_eq :
    let D₁ := matrixInnerLieHom ℝ (Fin 2) mat2E01
    let D₂ := matrixInnerLieHom ℝ (Fin 2) mat2E10
    mat2P * ((matrixDerivationsLane ℝ (Fin 2)).operatorAction D₁ mat2P *
              (matrixDerivationsLane ℝ (Fin 2)).operatorAction D₂ mat2P -
            (matrixDerivationsLane ℝ (Fin 2)).operatorAction D₂ mat2P *
              (matrixDerivationsLane ℝ (Fin 2)).operatorAction D₁ mat2P) * mat2P =
      -mat2P := by
  dsimp only
  let D₁ := matrixInnerLieHom ℝ (Fin 2) mat2E01
  let D₂ := matrixInnerLieHom ℝ (Fin 2) mat2E10
  have hD₁ : (matrixDerivationsLane ℝ (Fin 2)).operatorAction D₁ mat2P = -mat2E01 := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      norm_num [D₁, mat2P, mat2E01, Matrix.mul_apply, Fin.sum_univ_two]
  have hD₂ : (matrixDerivationsLane ℝ (Fin 2)).operatorAction D₂ mat2P = mat2E10 := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      norm_num [D₂, mat2P, mat2E10, Matrix.mul_apply, Fin.sum_univ_two]
  rw [hD₁, hD₂]
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [mat2P, mat2E01, mat2E10, Matrix.mul_apply, Fin.sum_univ_two]

theorem mat2_projected_curvature_ne_zero :
    let D₁ := matrixInnerLieHom ℝ (Fin 2) mat2E01
    let D₂ := matrixInnerLieHom ℝ (Fin 2) mat2E10
    mat2P * ((matrixDerivationsLane ℝ (Fin 2)).operatorAction D₁ mat2P *
              (matrixDerivationsLane ℝ (Fin 2)).operatorAction D₂ mat2P -
            (matrixDerivationsLane ℝ (Fin 2)).operatorAction D₂ mat2P *
              (matrixDerivationsLane ℝ (Fin 2)).operatorAction D₁ mat2P) * mat2P ≠ 0 := by
  dsimp only
  rw [mat2_projected_curvature_eq]
  intro h
  have hh := congrArg (fun M : Mat2R => M 0 0) h
  norm_num [mat2P] at hh

theorem mat2_projected_curvature_trace_ne_zero :
    let D₁ := matrixInnerLieHom ℝ (Fin 2) mat2E01
    let D₂ := matrixInnerLieHom ℝ (Fin 2) mat2E10
    Matrix.trace (mat2P * ((matrixDerivationsLane ℝ (Fin 2)).operatorAction D₁ mat2P *
              (matrixDerivationsLane ℝ (Fin 2)).operatorAction D₂ mat2P -
            (matrixDerivationsLane ℝ (Fin 2)).operatorAction D₂ mat2P *
              (matrixDerivationsLane ℝ (Fin 2)).operatorAction D₁ mat2P) * mat2P) = -1 := by
  dsimp only
  rw [mat2_projected_curvature_eq]
  norm_num [Matrix.trace, mat2P, Fin.sum_univ_two]

def mat3P : Mat3R := !![1, 0, 0; 0, 1, 0; 0, 0, 0]
def mat3S1 : Mat3R := !![0, 0, 1; 0, 0, 0; -1, 0, 0]
def mat3S2 : Mat3R := !![0, 0, 0; 0, 0, 1; 0, -1, 0]

/-- Explicit `Fin 3` real matrix non-commutativity witness (Trap T16). -/
theorem mat3_noncommutative : mat3S1 * mat3S2 ≠ mat3S2 * mat3S1 := by
  intro h
  have hh := congrArg (fun M : Mat3R => M 0 1) h
  norm_num [mat3S1, mat3S2, Matrix.mul_apply, Fin.sum_univ_three] at hh

theorem mat3P_idempotent : mat3P * mat3P = mat3P := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [mat3P, Matrix.mul_apply, Fin.sum_univ_three]

theorem mat3P_selfAdjoint : star mat3P = mat3P := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [mat3P, Matrix.star_apply]

theorem mat3S1_skewAdjoint : star mat3S1 = -mat3S1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [mat3S1, Matrix.star_apply]

theorem mat3S2_skewAdjoint : star mat3S2 = -mat3S2 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [mat3S2, Matrix.star_apply]

/-- Inner derivation by any skew-adjoint matrix commutes with `star`. -/
theorem mat3_inner_star_comm {S : Mat3R} (hS : star S = -S) (M : Mat3R) :
    (matrixDerivationsLane ℝ (Fin 3)).operatorAction
        (matrixInnerLieHom ℝ (Fin 3) S) (star M) =
      star ((matrixDerivationsLane ℝ (Fin 3)).operatorAction
        (matrixInnerLieHom ℝ (Fin 3) S) M) := by
  change S * star M - star M * S = star (S * M - M * S)
  rw [star_sub, star_mul, star_mul, hS]
  noncomm_ring

/-- Nonzero `⋆`-preserving projected curvature witness in `M₃(ℝ)` (rank-2 projector `mat3P`,
skew-adjoint inner derivations `mat3S1`, `mat3S2`), matching `star X₁ * X₂ - star X₂ * X₁ ≠ 0`. -/
theorem mat3_projected_curvature_star_ne_zero :
    let D₁ := matrixInnerLieHom ℝ (Fin 3) mat3S1
    let D₂ := matrixInnerLieHom ℝ (Fin 3) mat3S2
    let X₁ := coneMinus mat3P ((matrixDerivationsLane ℝ (Fin 3)).operatorAction D₁ mat3P)
    let X₂ := coneMinus mat3P ((matrixDerivationsLane ℝ (Fin 3)).operatorAction D₂ mat3P)
    mat3P * ((matrixDerivationsLane ℝ (Fin 3)).operatorAction D₁ mat3P *
              (matrixDerivationsLane ℝ (Fin 3)).operatorAction D₂ mat3P -
            (matrixDerivationsLane ℝ (Fin 3)).operatorAction D₂ mat3P *
              (matrixDerivationsLane ℝ (Fin 3)).operatorAction D₁ mat3P) * mat3P =
      star X₁ * X₂ - star X₂ * X₁ ∧
    mat3P * ((matrixDerivationsLane ℝ (Fin 3)).operatorAction D₁ mat3P *
              (matrixDerivationsLane ℝ (Fin 3)).operatorAction D₂ mat3P -
            (matrixDerivationsLane ℝ (Fin 3)).operatorAction D₂ mat3P *
              (matrixDerivationsLane ℝ (Fin 3)).operatorAction D₁ mat3P) * mat3P ≠ 0 := by
  let D₁ := matrixInnerLieHom ℝ (Fin 3) mat3S1
  let D₂ := matrixInnerLieHom ℝ (Fin 3) mat3S2
  have hstar := projected_two_direction_curvature_star mat3P_idempotent mat3P_selfAdjoint
    ((matrixDerivationsLane ℝ (Fin 3)).operatorAction D₁)
    ((matrixDerivationsLane ℝ (Fin 3)).operatorAction D₂)
    ((matrixDerivationsLane ℝ (Fin 3)).operatorAction_leibniz D₁)
    ((matrixDerivationsLane ℝ (Fin 3)).operatorAction_leibniz D₂)
    (mat3_inner_star_comm mat3S1_skewAdjoint)
    (mat3_inner_star_comm mat3S2_skewAdjoint)
  refine ⟨hstar, ?_⟩
  intro hzero
  have hentry := congrArg (fun M : Mat3R => M 0 1) hzero
  norm_num [D₁, D₂, mat3P, mat3S1, mat3S2, Matrix.mul_apply, Fin.sum_univ_three] at hentry

end ConcreteMatrixWitnesses

end InfoGeometry.OperatorAlgebra.ProjectorCurvatureSplitting
