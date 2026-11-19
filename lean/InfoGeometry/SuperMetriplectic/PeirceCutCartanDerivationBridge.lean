/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.SuperMetriplectic.Axioms
import InfoGeometry.Core.SymmetricLie
import InfoGeometry.Algebra.DerivationLieLane
import InfoGeometry.Canonical.PeirceFrechetOperatorArchetypes
import InfoGeometry.Canonical.OperatorFrechetDerivationJet
import InfoGeometry.Canonical.FrechetPeirceLieStabilizer
import InfoGeometry.Canonical.SouriauOnsagerBKMPositivity
import InfoGeometry.Thermo.OnsagerOperatorClosure
import InfoGeometry.OperatorAlgebra.PeirceSpine.Tetraktys
import Mathlib.Tactic.NoncommRing

/-!
# Peirce Cut Cartan–Onsager–Derivation Bridge

Connects idempotent Peirce cuts `P : PeirceCut n` on `FiniteOperatorAlgebra n`
and their continuous inner derivations `cutDerivation P` (`ad_P`) to:
1. A generic `[Ring B] [Algebra ℝ B]` `SymmetricLieAlgebra B` via `invS P = 2 • P - 1`
   and conjugation `X ↦ invS P * X * invS P` (without `Core.conjugationLieEquiv`);
2. Exact `Submodule` identifications `ker (ad_P ∘ₗ ad_P) = ker ad_P = S_P.𝔨` and
   `range ad_P = S_P.𝔭`, yielding `CartanOnsagerSplit (FiniteOperatorAlgebra n)`,
   `ParityOnsagerSystem (FiniteOperatorAlgebra n)` (via Hilbert–Schmidt and BKM forms),
   and `peirceCartanLinearEquiv`;
3. `OperatorFrechetDerivationJet.realDerivationsLane`, a faithful
   `peirceCutDerivationLieLane : DerivationLieLane ℝ (FiniteOperatorAlgebra n)`, and
   a lifted Cartan involution on `NonAssocDerivation.derivations ℝ (FiniteOperatorAlgebra n)`
   whose `evenLieSubalgebra` equals `cutStabilizer P`.
-/

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 100000

noncomputable section

namespace InfoGeometry.SuperMetriplectic.PeirceCutCartanDerivationBridge

open InfoGeometry.Core
open InfoGeometry.Algebra
open InfoGeometry.Algebra.NonAssocDerivation
open InfoGeometry.OperatorAlgebra.PeirceSpine
open InfoGeometry.Optics.OperatorDerivationForms
open InfoGeometry.Canonical.PeirceFrechetOperatorArchetypes
open InfoGeometry.Canonical.OperatorFrechetDerivationJet
open InfoGeometry.Canonical.FrechetPeirceLieStabilizer
open InfoGeometry.Thermo.OnsagerClosure
open InfoGeometry.Thermo.OnsagerClosure.OnsagerCasimirSystem
open SouriauOnsagerBKM

/-! ## Part 1: Generic `[Ring B] [Algebra ℝ B]` `SymmetricLieAlgebra B` from an idempotent -/

section GenericIdempotentSymmetricLie

attribute [local instance 100] LieRing.ofAssociativeRing LieAlgebra.ofAssociativeAlgebra

theorem invS_eq_two_smul_sub_one {B : Type*} [Ring B] [Algebra ℝ B] (P : B) :
    invS P = (2 : ℝ) • P - 1 := by
  unfold invS
  rw [show (2 : ℝ) • P = P + P from by rw [← one_add_one_eq_two, add_smul, one_smul]]
  abel

theorem invS_sq_eq_one {B : Type*} [Ring B] (P : B) (hP : P * P = P) :
    invS P * invS P = 1 :=
  (archetype_A2_peirce_cartan_grading_and_tangent_closure hP P P).1

theorem invS_mul_idem {B : Type*} [Ring B] (P : B) (hP : P * P = P) :
    invS P * P = P ∧ P * invS P = P := by
  constructor <;> peirce_nf hP

/-- Conjugation algebra automorphism `X ↦ S * X * S` for any `S` with `S * S = 1`. -/
def conjugationAlgEquivOfSqOne {B : Type*} [Ring B] [Algebra ℝ B]
    (S : B) (hS : S * S = 1) : B ≃ₐ[ℝ] B where
  toFun X := S * X * S
  invFun X := S * X * S
  left_inv X := by
    calc
      S * (S * X * S) * S = (S * S) * X * (S * S) := by noncomm_ring
      _ = X := by rw [hS]; simp
  right_inv X := by
    calc
      S * (S * X * S) * S = (S * S) * X * (S * S) := by noncomm_ring
      _ = X := by rw [hS]; simp
  map_mul' X Y := by
    calc
      S * (X * Y) * S = S * X * 1 * Y * S := by noncomm_ring
      _ = S * X * (S * S) * Y * S := by rw [hS]
      _ = (S * X * S) * (S * Y * S) := by noncomm_ring
  map_add' X Y := by simp [mul_add, add_mul]
  commutes' r := by
    calc
      S * algebraMap ℝ B r * S = (S * algebraMap ℝ B r) * S := rfl
      _ = (algebraMap ℝ B r * S) * S := by rw [Algebra.commutes]
      _ = algebraMap ℝ B r * (S * S) := by rw [mul_assoc]
      _ = algebraMap ℝ B r := by rw [hS, mul_one]

@[simp] theorem conjugationAlgEquivOfSqOne_apply {B : Type*} [Ring B] [Algebra ℝ B]
    (S : B) (hS : S * S = 1) (X : B) :
    conjugationAlgEquivOfSqOne S hS X = S * X * S := rfl

theorem conjugationAlgEquivOfSqOne_involutive {B : Type*} [Ring B] [Algebra ℝ B]
    (S : B) (hS : S * S = 1) :
    Function.Involutive (conjugationAlgEquivOfSqOne S hS) :=
  fun X => (conjugationAlgEquivOfSqOne S hS).left_inv X

/-- Conjugation Lie automorphism `X ↦ S * X * S` for any `S` with `S * S = 1`. -/
def conjugationLieEquivOfSqOne {B : Type*} [Ring B] [Algebra ℝ B]
    (S : B) (hS : S * S = 1) : B ≃ₗ⁅ℝ⁆ B where
  toFun := conjugationAlgEquivOfSqOne S hS
  invFun := conjugationAlgEquivOfSqOne S hS
  left_inv := (conjugationAlgEquivOfSqOne S hS).left_inv
  right_inv := (conjugationAlgEquivOfSqOne S hS).right_inv
  map_add' := (conjugationAlgEquivOfSqOne S hS).map_add
  map_smul' r X := _root_.map_smul (conjugationAlgEquivOfSqOne S hS) r X
  map_lie' {X Y} := by
    change conjugationAlgEquivOfSqOne S hS (X * Y - Y * X) =
      conjugationAlgEquivOfSqOne S hS X * conjugationAlgEquivOfSqOne S hS Y -
        conjugationAlgEquivOfSqOne S hS Y * conjugationAlgEquivOfSqOne S hS X
    rw [map_sub, map_mul, map_mul]

/-- `SymmetricLieAlgebra B` induced by conjugation with `S` (`S * S = 1`). -/
def symmetricLieAlgebraOfSqOne {B : Type*} [Ring B] [Algebra ℝ B]
    (S : B) (hS : S * S = 1) : SymmetricLieAlgebra B :=
  SymmetricLieAlgebra.ofInvolutiveLieAut
    ⟨conjugationLieEquivOfSqOne S hS, conjugationAlgEquivOfSqOne_involutive S hS⟩

/-- `SymmetricLieAlgebra B` induced by an idempotent `P : B` (`P * P = P`) via `invS P`. -/
def symmetricLieAlgebraOfIdempotent {B : Type*} [Ring B] [Algebra ℝ B]
    (P : B) (hP : P * P = P) : SymmetricLieAlgebra B :=
  symmetricLieAlgebraOfSqOne (invS P) (invS_sq_eq_one P hP)

@[simp] theorem symmetricLieAlgebraOfIdempotent_theta_apply
    {B : Type*} [Ring B] [Algebra ℝ B] (P : B) (hP : P * P = P) (X : B) :
    (symmetricLieAlgebraOfIdempotent P hP).θ X = invS P * X * invS P := rfl

theorem symmetricLieAlgebraOfIdempotent_theta_eq_grade_sub
    {B : Type*} [Ring B] [Algebra ℝ B] (P : B) (hP : P * P = P) (X : B) :
    (symmetricLieAlgebraOfIdempotent P hP).θ X = evenGrade P X - oddGrade P X :=
  (archetype_A2_peirce_cartan_grading_and_tangent_closure hP X X).2.2.2.2.2.2

/-- Inner derivation `X ↦ comm P X = P * X - X * P` as an `ℝ`-linear endomorphism. -/
def adMap {B : Type*} [Ring B] [Algebra ℝ B] (P : B) : Module.End ℝ B where
  toFun X := InfoGeometry.OperatorAlgebra.PeirceSpine.comm P X
  map_add' X Y := by
    simp only [InfoGeometry.OperatorAlgebra.PeirceSpine.comm, mul_add, add_mul]
    abel
  map_smul' r X := by
    simp only [InfoGeometry.OperatorAlgebra.PeirceSpine.comm, mul_smul_comm, smul_mul_assoc,
      smul_sub, RingHom.id_apply]

@[simp] theorem adMap_apply {B : Type*} [Ring B] [Algebra ℝ B] (P X : B) :
    adMap P X = P * X - X * P := rfl

theorem adMap_sq_apply {B : Type*} [Ring B] [Algebra ℝ B]
    (P : B) (hP : P * P = P) (X : B) :
    (adMap P ∘ₗ adMap P) X = oddGrade P X :=
  (archetype_A2_peirce_cartan_grading_and_tangent_closure hP X X).2.1

theorem adMap_cube_apply {B : Type*} [Ring B] [Algebra ℝ B]
    (P : B) (hP : P * P = P) (X : B) :
    adMap P (adMap P (adMap P X)) = adMap P X :=
  (archetype_A2_peirce_cartan_grading_and_tangent_closure hP X X).2.2.2.1

theorem symmetricLieAlgebraOfIdempotent_P_plus
    {B : Type*} [Ring B] [Algebra ℝ B] (P : B) (hP : P * P = P) (X : B) :
    (symmetricLieAlgebraOfIdempotent P hP).P_plus X = evenGrade P X := by
  change ((2 : ℝ)⁻¹) • (X + (symmetricLieAlgebraOfIdempotent P hP).θ X) = evenGrade P X
  rw [symmetricLieAlgebraOfIdempotent_theta_eq_grade_sub P hP X]
  have hsum : evenGrade P X + oddGrade P X = X := (grade_projection_laws hP X).2.2.2.2
  calc
    ((2 : ℝ)⁻¹) • (X + (evenGrade P X - oddGrade P X))
        = ((2 : ℝ)⁻¹) • ((evenGrade P X + oddGrade P X) + (evenGrade P X - oddGrade P X)) := by
          rw [hsum]
    _ = ((2 : ℝ)⁻¹) • (evenGrade P X + evenGrade P X) := by
          congr 1; abel
    _ = ((2 : ℝ)⁻¹) • ((2 : ℝ) • evenGrade P X) := by
          rw [two_smul]
    _ = evenGrade P X := by
          rw [smul_smul, inv_mul_cancel₀ (by norm_num), one_smul]

theorem symmetricLieAlgebraOfIdempotent_P_minus
    {B : Type*} [Ring B] [Algebra ℝ B] (P : B) (hP : P * P = P) (X : B) :
    (symmetricLieAlgebraOfIdempotent P hP).P_minus X = oddGrade P X := by
  change ((2 : ℝ)⁻¹) • (X - (symmetricLieAlgebraOfIdempotent P hP).θ X) = oddGrade P X
  rw [symmetricLieAlgebraOfIdempotent_theta_eq_grade_sub P hP X]
  have hsum : evenGrade P X + oddGrade P X = X := (grade_projection_laws hP X).2.2.2.2
  calc
    ((2 : ℝ)⁻¹) • (X - (evenGrade P X - oddGrade P X))
        = ((2 : ℝ)⁻¹) • ((evenGrade P X + oddGrade P X) - (evenGrade P X - oddGrade P X)) := by
          rw [hsum]
    _ = ((2 : ℝ)⁻¹) • (oddGrade P X + oddGrade P X) := by
          congr 1; abel
    _ = ((2 : ℝ)⁻¹) • ((2 : ℝ) • oddGrade P X) := by
          rw [two_smul]
    _ = oddGrade P X := by
          rw [smul_smul, inv_mul_cancel₀ (by norm_num), one_smul]

theorem adMap_sq_eq_P_minus {B : Type*} [Ring B] [Algebra ℝ B]
    (P : B) (hP : P * P = P) :
    adMap P ∘ₗ adMap P = (symmetricLieAlgebraOfIdempotent P hP).P_minus := by
  ext X
  rw [adMap_sq_apply P hP X, symmetricLieAlgebraOfIdempotent_P_minus P hP X]

theorem adMap_ker_eq_k {B : Type*} [Ring B] [Algebra ℝ B]
    (P : B) (hP : P * P = P) :
    LinearMap.ker (adMap P) = (symmetricLieAlgebraOfIdempotent P hP).𝔨 := by
  ext X
  dsimp only [SymmetricLieAlgebra.𝔨]
  rw [LinearMap.mem_ker, SymmetricLieAlgebra.mem_evenSubmodule_iff]
  change P * X - X * P = 0 ↔ invS P * X * invS P = X
  have hinvSq : invS P * invS P = 1 := invS_sq_eq_one P hP
  constructor
  · intro hcomm
    have hPX : P * X = X * P := sub_eq_zero.mp hcomm
    have hinvComm : invS P * X = X * invS P := by
      rw [invS_eq_two_smul_sub_one P, sub_mul, mul_sub, one_mul, mul_one,
        smul_mul_assoc, mul_smul_comm, hPX]
    calc
      invS P * X * invS P = X * (invS P * invS P) := by rw [hinvComm, mul_assoc]
      _ = X := by rw [hinvSq, mul_one]
  · intro hθ
    have hinvComm : invS P * X = X * invS P := by
      calc
        invS P * X = (invS P * X * invS P) * invS P := by
          rw [mul_assoc, mul_assoc, hinvSq, mul_one]
        _ = X * invS P := by rw [hθ]
    have htwo : (2 : ℝ) • (P * X - X * P) = 0 := by
      have hsub : invS P * X - X * invS P = 0 := sub_eq_zero.mpr hinvComm
      rw [invS_eq_two_smul_sub_one P, sub_mul, mul_sub, one_mul, mul_one,
        smul_mul_assoc, mul_smul_comm] at hsub
      have hEq : (2 : ℝ) • (P * X) - X - ((2 : ℝ) • (X * P) - X) =
          (2 : ℝ) • (P * X - X * P) := by
        rw [smul_sub]
        abel
      rw [hEq] at hsub
      exact hsub
    have hhalf := congrArg (fun Y : B => ((2 : ℝ)⁻¹) • Y) htwo
    simpa [smul_smul] using hhalf

theorem adMap_sq_ker_eq_ker {B : Type*} [Ring B] [Algebra ℝ B]
    (P : B) (hP : P * P = P) :
    LinearMap.ker (adMap P ∘ₗ adMap P) = LinearMap.ker (adMap P) := by
  ext X
  simp only [LinearMap.mem_ker, LinearMap.comp_apply]
  constructor
  · intro h2
    have h3 : adMap P (adMap P (adMap P X)) = 0 := by
      rw [h2, map_zero]
    rwa [adMap_cube_apply P hP X] at h3
  · intro h1
    rw [h1, map_zero]

theorem adMap_range_eq_p {B : Type*} [Ring B] [Algebra ℝ B]
    (P : B) (hP : P * P = P) :
    LinearMap.range (adMap P) = (symmetricLieAlgebraOfIdempotent P hP).𝔭 := by
  ext Y
  dsimp only [SymmetricLieAlgebra.𝔭]
  rw [LinearMap.mem_range, SymmetricLieAlgebra.mem_oddSubmodule_iff]
  have hsum : evenGrade P Y + oddGrade P Y = Y := (grade_projection_laws hP Y).2.2.2.2
  have hθ : (symmetricLieAlgebraOfIdempotent P hP).θ Y = evenGrade P Y - oddGrade P Y :=
    symmetricLieAlgebraOfIdempotent_theta_eq_grade_sub P hP Y
  constructor
  · rintro ⟨X, rfl⟩
    have hOdd : oddGrade P (adMap P X) = adMap P X := by
      rw [← adMap_sq_apply P hP]
      exact adMap_cube_apply P hP X
    have hsum' : evenGrade P (adMap P X) + oddGrade P (adMap P X) = adMap P X :=
      (grade_projection_laws hP (adMap P X)).2.2.2.2
    have hEven : evenGrade P (adMap P X) = 0 := by
      have h1 : evenGrade P (adMap P X) + adMap P X = adMap P X := by
        calc
          evenGrade P (adMap P X) + adMap P X =
              evenGrade P (adMap P X) + oddGrade P (adMap P X) := by rw [hOdd]
          _ = adMap P X := hsum'
      exact add_eq_right.mp h1
    rw [symmetricLieAlgebraOfIdempotent_theta_eq_grade_sub P hP (adMap P X), hEven, hOdd, zero_sub]
  · intro hneg
    rw [hθ] at hneg
    have htwoEven : (2 : ℝ) • evenGrade P Y = 0 := by
      calc
        (2 : ℝ) • evenGrade P Y = evenGrade P Y + evenGrade P Y := two_smul _ _
        _ = (evenGrade P Y + oddGrade P Y) + (evenGrade P Y - oddGrade P Y) := by abel
        _ = Y + (-Y) := by rw [hsum, hneg]
        _ = 0 := add_neg_cancel Y
    have hEven : evenGrade P Y = 0 := by
      have hhalf := congrArg (fun Z : B => ((2 : ℝ)⁻¹) • Z) htwoEven
      simpa [smul_smul] using hhalf
    have hOdd : oddGrade P Y = Y := by
      simpa [hEven] using hsum
    refine ⟨adMap P Y, ?_⟩
    change (adMap P ∘ₗ adMap P) Y = Y
    rw [adMap_sq_apply P hP Y, hOdd]

end GenericIdempotentSymmetricLie

/-! ## Part 2: Specialization to `P : PeirceCut n` on `FiniteOperatorAlgebra n` -/

section PeirceCutCartanSpecialization

attribute [local instance 100] LieRing.ofAssociativeRing LieAlgebra.ofAssociativeAlgebra

/-- `SymmetricLieAlgebra` on `FiniteOperatorAlgebra n` generated by `invS P`. -/
def peirceSymmetricLieAlgebra {n : ℕ} (P : PeirceCut n) :
    SymmetricLieAlgebra (FiniteOperatorAlgebra n) :=
  symmetricLieAlgebraOfIdempotent (P : FiniteOperatorAlgebra n) P.property

/-- `cutDerivation P` viewed as an `ℝ`-linear endomorphism of `FiniteOperatorAlgebra n`. -/
def peirceAdMap {n : ℕ} (P : PeirceCut n) :
    Module.End ℝ (FiniteOperatorAlgebra n) :=
  (cutDerivation P).toContinuousLinearMap.toLinearMap

theorem peirceAdMap_eq_adMap {n : ℕ} (P : PeirceCut n) :
    peirceAdMap P = adMap (P : FiniteOperatorAlgebra n) :=
  LinearMap.ext fun X => by
    change (cutDerivation P) X = P.1 * X - X * P.1
    rw [cutDerivation_apply]
    rfl

theorem peirceAdSq_ker_eq_k {n : ℕ} (P : PeirceCut n) :
    LinearMap.ker (peirceAdMap P ∘ₗ peirceAdMap P) =
      (peirceSymmetricLieAlgebra P).𝔨 := by
  rw [peirceAdMap_eq_adMap, adMap_sq_ker_eq_ker _ P.property, adMap_ker_eq_k _ P.property]
  rfl

theorem peirceAd_ker_eq_k {n : ℕ} (P : PeirceCut n) :
    LinearMap.ker (peirceAdMap P) = (peirceSymmetricLieAlgebra P).𝔨 := by
  rw [peirceAdMap_eq_adMap, adMap_ker_eq_k _ P.property]
  rfl

theorem peirceAdSq_ker_eq_ker_ad {n : ℕ} (P : PeirceCut n) :
    LinearMap.ker (peirceAdMap P ∘ₗ peirceAdMap P) = LinearMap.ker (peirceAdMap P) := by
  rw [peirceAdMap_eq_adMap, adMap_sq_ker_eq_ker _ P.property]

theorem peirceAd_range_eq_p {n : ℕ} (P : PeirceCut n) :
    LinearMap.range (peirceAdMap P) = (peirceSymmetricLieAlgebra P).𝔭 := by
  rw [peirceAdMap_eq_adMap, adMap_range_eq_p _ P.property]
  rfl

theorem peirceAdSq_eq_P_minus {n : ℕ} (P : PeirceCut n) :
    peirceAdMap P ∘ₗ peirceAdMap P = (peirceSymmetricLieAlgebra P).P_minus := by
  rw [peirceAdMap_eq_adMap, adMap_sq_eq_P_minus _ P.property]
  rfl

/-- `CartanOnsagerSplit (FiniteOperatorAlgebra n)` realized by `peirceAdMap P ∘ₗ peirceAdMap P`. -/
def peirceCartanOnsagerSplit {n : ℕ} (P : PeirceCut n) :
    CartanOnsagerSplit (FiniteOperatorAlgebra n) where
  S := peirceSymmetricLieAlgebra P
  onsager := peirceAdMap P ∘ₗ peirceAdMap P
  drazinCore := LinearMap.ker (peirceAdMap P ∘ₗ peirceAdMap P)
  dissipativeRange := LinearMap.range (peirceAdMap P)
  drazinCore_eq_k := peirceAdSq_ker_eq_k P
  dissipativeRange_eq_p := peirceAd_range_eq_p P

theorem peirceCartanOnsagerSplit_onsager_eq_P_minus {n : ℕ} (P : PeirceCut n) :
    (peirceCartanOnsagerSplit P).onsager = (peirceSymmetricLieAlgebra P).P_minus :=
  peirceAdSq_eq_P_minus P

theorem peirceCartanOnsagerSplit_onsager_apply {n : ℕ} (P : PeirceCut n)
    (X : FiniteOperatorAlgebra n) :
    (peirceCartanOnsagerSplit P).onsager X =
      oddGrade (P : FiniteOperatorAlgebra n) X := by
  change (peirceAdMap P ∘ₗ peirceAdMap P) X = _
  rw [peirceAdMap_eq_adMap, adMap_sq_apply _ P.property X]

/-- Unconditional Hilbert–Schmidt real bilinear form `(A, B) ↦ Re Tr(A* B)` on
`FiniteOperatorAlgebra n`. -/
def hsRealBilinForm (n : ℕ) :
    LinearMap.BilinForm ℝ (FiniteOperatorAlgebra n) :=
  LinearMap.mk₂ ℝ
    (fun A B => (finiteOperatorTrace (star A * B)).re)
    (fun A₁ A₂ B => by
      change (finiteOperatorTrace (ContinuousLinearMap.adjoint (A₁ + A₂) * B)).re =
        (finiteOperatorTrace (ContinuousLinearMap.adjoint A₁ * B)).re +
          (finiteOperatorTrace (ContinuousLinearMap.adjoint A₂ * B)).re
      rw [_root_.map_add ContinuousLinearMap.adjoint A₁ A₂, add_mul]
      simpa only [finiteOperatorTraceLinear_apply, Complex.add_re] using
        congrArg Complex.re
          ((finiteOperatorTraceLinear n).map_add
            (ContinuousLinearMap.adjoint A₁ * B) (ContinuousLinearMap.adjoint A₂ * B)))
    (fun r A B => by
      change (finiteOperatorTrace (ContinuousLinearMap.adjoint ((r : ℂ) • A) * B)).re =
        r * (finiteOperatorTrace (ContinuousLinearMap.adjoint A * B)).re
      have hadj : ContinuousLinearMap.adjoint ((r : ℂ) • A) =
          (r : ℂ) • ContinuousLinearMap.adjoint A := by
        rw [map_smulₛₗ, Complex.conj_ofReal]
      rw [hadj, smul_mul_assoc]
      have htr := (finiteOperatorTraceLinear n).map_smul (r : ℂ)
        (ContinuousLinearMap.adjoint A * B)
      simp only [finiteOperatorTraceLinear_apply, smul_eq_mul] at htr
      rw [htr, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero])
    (fun A B₁ B₂ => by
      rw [mul_add]
      simpa only [finiteOperatorTraceLinear_apply, Complex.add_re] using
        congrArg Complex.re
          ((finiteOperatorTraceLinear n).map_add (star A * B₁) (star A * B₂)))
    (fun r A B => by
      change (finiteOperatorTrace (star A * ((r : ℂ) • B))).re =
        r * (finiteOperatorTrace (star A * B)).re
      rw [mul_smul_comm]
      have htr := (finiteOperatorTraceLinear n).map_smul (r : ℂ) (star A * B)
      simp only [finiteOperatorTraceLinear_apply, smul_eq_mul] at htr
      rw [htr, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero])

@[simp] theorem hsRealBilinForm_apply (n : ℕ) (A B : FiniteOperatorAlgebra n) :
    hsRealBilinForm n A B = (finiteOperatorTrace (star A * B)).re := rfl

theorem hsRealBilinForm_symm (n : ℕ) (A B : FiniteOperatorAlgebra n) :
    hsRealBilinForm n A B = hsRealBilinForm n B A := by
  simp only [hsRealBilinForm_apply]
  have hstar : finiteOperatorTrace (star B * A) =
      star (finiteOperatorTrace (star A * B)) := by
    rw [← finiteOperatorTrace_star (star A * B), StarMul.star_mul, star_star]
  rw [hstar]
  simp

theorem hsRealBilinForm_nonneg (n : ℕ) (A : FiniteOperatorAlgebra n) :
    0 ≤ hsRealBilinForm n A A :=
  finiteOperatorTrace_star_mul_self_re_nonneg A

/-- Probe-twisted Hilbert–Schmidt bilinear form `(X, Y) ↦ Re Tr((A X)* Y)`. -/
def hsProbeBilinForm (n : ℕ) (A : FiniteOperatorAlgebra n) :
    LinearMap.BilinForm ℝ (FiniteOperatorAlgebra n) :=
  (hsRealBilinForm n).compl₁₂ (LinearMap.mulLeft ℝ A) LinearMap.id

@[simp] theorem hsProbeBilinForm_apply (n : ℕ) (A X Y : FiniteOperatorAlgebra n) :
    hsProbeBilinForm n A X Y = (finiteOperatorTrace (star (A * X) * Y)).re := rfl

/-- `TimeReversal` on `FiniteOperatorAlgebra n` induced by `-θ_P` (`𝔭` is `T`-even,
`𝔨` is `T`-odd). -/
def peirceCartanTimeReversal {n : ℕ} (P : PeirceCut n) :
    TimeReversal (FiniteOperatorAlgebra n) where
  op := -((peirceSymmetricLieAlgebra P).toLieAut.toLinearEquiv.toLinearMap)
  involutive X := by
    change -(peirceSymmetricLieAlgebra P).θ (-(peirceSymmetricLieAlgebra P).θ X) = X
    rw [(peirceSymmetricLieAlgebra P).θ.map_neg, neg_neg,
      (peirceSymmetricLieAlgebra P).involutive X]

@[simp] theorem peirceCartanTimeReversal_apply {n : ℕ} (P : PeirceCut n)
    (X : FiniteOperatorAlgebra n) :
    (peirceCartanTimeReversal P).op X = -(peirceSymmetricLieAlgebra P).θ X := rfl

theorem peirce_P_plus_cartanTimeReversal {n : ℕ} (P : PeirceCut n)
    (X : FiniteOperatorAlgebra n) :
    (peirceSymmetricLieAlgebra P).P_plus ((peirceCartanTimeReversal P).op X) =
      -(peirceSymmetricLieAlgebra P).P_plus X := by
  let S := peirceSymmetricLieAlgebra P
  change ((2 : ℝ)⁻¹) • (-S.θ X + S.θ (-S.θ X)) = -(((2 : ℝ)⁻¹) • (X + S.θ X))
  rw [S.θ.map_neg, S.involutive X, add_comm, ← neg_add, smul_neg]

theorem peirce_P_minus_cartanTimeReversal {n : ℕ} (P : PeirceCut n)
    (X : FiniteOperatorAlgebra n) :
    (peirceSymmetricLieAlgebra P).P_minus ((peirceCartanTimeReversal P).op X) =
      (peirceSymmetricLieAlgebra P).P_minus X := by
  let S := peirceSymmetricLieAlgebra P
  change ((2 : ℝ)⁻¹) • (-S.θ X - S.θ (-S.θ X)) = ((2 : ℝ)⁻¹) • (X - S.θ X)
  rw [S.θ.map_neg, S.involutive X, sub_neg_eq_add, add_comm, sub_eq_add_neg]

/-- Generic `ParityOnsagerSystem (FiniteOperatorAlgebra n)` induced by `P : PeirceCut n`,
any symmetric PSD form `g`, and coupling form `η`. -/
def peirceCartanParityOnsagerSystemOfForms {n : ℕ} (P : PeirceCut n)
    (g : LinearMap.BilinForm ℝ (FiniteOperatorAlgebra n))
    (hg_symm : ∀ X Y, g X Y = g Y X)
    (hg_nonneg : ∀ X, 0 ≤ g X X)
    (η : LinearMap.BilinForm ℝ (FiniteOperatorAlgebra n)) :
    ParityOnsagerSystem (FiniteOperatorAlgebra n) where
  dissipative := g.compl₁₂ (peirceAdMap P ∘ₗ peirceAdMap P) (peirceAdMap P ∘ₗ peirceAdMap P)
  reversible :=
    η.compl₁₂ (peirceSymmetricLieAlgebra P).P_plus (peirceSymmetricLieAlgebra P).P_minus -
      (η.compl₁₂ (peirceSymmetricLieAlgebra P).P_plus (peirceSymmetricLieAlgebra P).P_minus).flip
  dissipative_symm X Y := by
    simp only [LinearMap.compl₁₂_apply]
    exact hg_symm _ _
  reversible_skew X Y := by
    simp only [LinearMap.BilinForm.sub_apply, LinearMap.compl₁₂_apply, LinearMap.flip_apply]
    exact (neg_sub _ _).symm
  dissipative_nonneg X := by
    simp only [LinearMap.compl₁₂_apply]
    exact hg_nonneg _
  T := peirceCartanTimeReversal P
  dissipative_T_even X Y := by
    simp only [LinearMap.compl₁₂_apply, peirceAdSq_eq_P_minus, peirce_P_minus_cartanTimeReversal]
  reversible_T_odd X Y := by
    simp only [LinearMap.BilinForm.sub_apply, LinearMap.compl₁₂_apply, LinearMap.flip_apply,
      peirce_P_plus_cartanTimeReversal, peirce_P_minus_cartanTimeReversal,
      map_neg, LinearMap.neg_apply]
    rw [sub_neg_eq_add, add_comm, ← sub_eq_add_neg, ← neg_sub]

/-- Unconditional `ParityOnsagerSystem (FiniteOperatorAlgebra n)` using the Hilbert–Schmidt
form `hsRealBilinForm n` and skew-coupling seed `η`. -/
def peirceCartanParityOnsagerSystem {n : ℕ} (P : PeirceCut n)
    (η : LinearMap.BilinForm ℝ (FiniteOperatorAlgebra n)) :
    ParityOnsagerSystem (FiniteOperatorAlgebra n) :=
  peirceCartanParityOnsagerSystemOfForms P (hsRealBilinForm n)
    (hsRealBilinForm_symm n) (hsRealBilinForm_nonneg n) η

/-- BKM-coupled `ParityOnsagerSystem (FiniteOperatorAlgebra n)` using `D.bkmRealBilinForm hpow`. -/
def peirceCartanParityOnsagerSystemBKM {n : ℕ} (P : PeirceCut n)
    (D : FaithfulDensityOperator n) (hpow : Continuous D.rpow)
    (η : LinearMap.BilinForm ℝ (FiniteOperatorAlgebra n)) :
    ParityOnsagerSystem (FiniteOperatorAlgebra n) :=
  peirceCartanParityOnsagerSystemOfForms P (D.bkmRealBilinForm hpow)
    (fun X Y => (D.bkmRealBilinForm_symm hpow).eq X Y)
    (fun X => D.kuboMoriPairing_self_re_nonneg X hpow) η

/-- Linear equivalence between `S_P.evenLieSubalgebra` and `ker (peirceAdMap P ∘ₗ peirceAdMap P)`. -/
def peirceEvenEquivKerAdSq {n : ℕ} (P : PeirceCut n) :
    (peirceSymmetricLieAlgebra P).evenLieSubalgebra ≃ₗ[ℝ]
      LinearMap.ker (peirceAdMap P ∘ₗ peirceAdMap P) where
  toFun X := ⟨X.1, by rw [peirceAdSq_ker_eq_k P]; exact X.2⟩
  invFun X := ⟨X.1, by
    change (X : FiniteOperatorAlgebra n) ∈ (peirceSymmetricLieAlgebra P).𝔨
    rw [← peirceAdSq_ker_eq_k P]
    exact X.2⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- Linear equivalence between `S_P.oddSubmodule` and `range (peirceAdMap P)`. -/
def peirceOddEquivRangeAd {n : ℕ} (P : PeirceCut n) :
    (peirceSymmetricLieAlgebra P).oddSubmodule ≃ₗ[ℝ]
      LinearMap.range (peirceAdMap P) where
  toFun X := ⟨X.1, by rw [peirceAd_range_eq_p P]; exact X.2⟩
  invFun X := ⟨X.1, by
    change (X : FiniteOperatorAlgebra n) ∈ (peirceSymmetricLieAlgebra P).𝔭
    rw [← peirceAd_range_eq_p P]
    exact X.2⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- Explicit Cartan–Peirce splitting equivalence
`FiniteOperatorAlgebra n ≃ₗ[ℝ] ker (ad_P²) × range ad_P`. -/
def peirceCartanLinearEquiv {n : ℕ} (P : PeirceCut n) :
    FiniteOperatorAlgebra n ≃ₗ[ℝ]
      LinearMap.ker (peirceAdMap P ∘ₗ peirceAdMap P) ×
        LinearMap.range (peirceAdMap P) :=
  (peirceSymmetricLieAlgebra P).cartanLinearEquiv.trans
    (LinearEquiv.prodCongr (peirceEvenEquivKerAdSq P) (peirceOddEquivRangeAd P))

theorem peirceCartanLinearEquiv_apply {n : ℕ} (P : PeirceCut n)
    (X : FiniteOperatorAlgebra n) :
    ((peirceCartanLinearEquiv P X).1 : FiniteOperatorAlgebra n) =
        evenGrade (P : FiniteOperatorAlgebra n) X ∧
      ((peirceCartanLinearEquiv P X).2 : FiniteOperatorAlgebra n) =
        oddGrade (P : FiniteOperatorAlgebra n) X := by
  constructor
  · change (peirceSymmetricLieAlgebra P).plusPart X = evenGrade (P : FiniteOperatorAlgebra n) X
    rw [← (peirceSymmetricLieAlgebra P).P_plus_eq_plusPart X]
    exact symmetricLieAlgebraOfIdempotent_P_plus (P : FiniteOperatorAlgebra n) P.property X
  · change (peirceSymmetricLieAlgebra P).minusPart X = oddGrade (P : FiniteOperatorAlgebra n) X
    rw [← (peirceSymmetricLieAlgebra P).P_minus_eq_minusPart X]
    exact symmetricLieAlgebraOfIdempotent_P_minus (P : FiniteOperatorAlgebra n) P.property X

end PeirceCutCartanSpecialization

/-! ## Part 3: `DerivationLieLane`, `realDerivationsLane`, and `cutStabilizer` Bridge -/

section DerivationLieLaneBridge

theorem cutDerivation_toRealDerivation_apply {n : ℕ} (P : PeirceCut n)
    (X : FiniteOperatorAlgebra n) :
    (realDerivationsLane (FiniteOperatorAlgebra n)).operatorAction
        (FrechetBridge.toRealDerivation (cutDerivation P)) X =
      peirceAdMap P X := rfl

theorem cutDerivation_toRealDerivation_commutator {n : ℕ} (P Q : PeirceCut n) :
    FrechetBridge.toRealDerivation
        (FrechetOperatorDerivation.commutator (cutDerivation P) (cutDerivation Q)) =
      ⁅FrechetBridge.toRealDerivation (cutDerivation P),
        FrechetBridge.toRealDerivation (cutDerivation Q)⁆ :=
  FrechetBridge.toRealDerivation_commutator (cutDerivation P) (cutDerivation Q)

/-- Faithful `DerivationLieLane ℝ A` associated to any `LieSubalgebra` of
`NonAssocDerivation.derivations ℝ A` (constructed directly without untracked imports). -/
def peirceSubalgebraDerivationLieLane
    {A : Type*} [NonUnitalNonAssocRing A] [Module ℝ A]
    [IsScalarTower ℝ A A] [SMulCommClass ℝ A A]
    (S : LieSubalgebra ℝ (NonAssocDerivation.derivations ℝ A)) :
    DerivationLieLane ℝ A where
  L := S
  lieRing := inferInstance
  lieAlgebra := inferInstance
  act := S.incl
  faithful := Subtype.coe_injective

/-- Lie subalgebra of `NonAssocDerivation.derivations ℝ (FiniteOperatorAlgebra n)` generated
by all Peirce cut inner derivations `cutDerivation P`. -/
def peirceCutDerivationsSubalgebra (n : ℕ) :
    LieSubalgebra ℝ (NonAssocDerivation.derivations ℝ (FiniteOperatorAlgebra n)) :=
  LieSubalgebra.lieSpan ℝ (NonAssocDerivation.derivations ℝ (FiniteOperatorAlgebra n))
    (Set.range fun P : PeirceCut n => FrechetBridge.toRealDerivation (cutDerivation P))

/-- Faithful `DerivationLieLane ℝ (FiniteOperatorAlgebra n)` generated by Peirce cuts. -/
def peirceCutDerivationLieLane (n : ℕ) :
    DerivationLieLane ℝ (FiniteOperatorAlgebra n) :=
  peirceSubalgebraDerivationLieLane (peirceCutDerivationsSubalgebra n)

/-- Canonical generator corresponding to `P : PeirceCut n` inside `peirceCutDerivationLieLane n`. -/
def peirceCutGenerator {n : ℕ} (P : PeirceCut n) :
    (peirceCutDerivationLieLane n).L :=
  ⟨FrechetBridge.toRealDerivation (cutDerivation P),
    LieSubalgebra.subset_lieSpan ⟨P, rfl⟩⟩

theorem peirceCutGenerator_operatorAction {n : ℕ} (P : PeirceCut n)
    (X : FiniteOperatorAlgebra n) :
    (peirceCutDerivationLieLane n).operatorAction (peirceCutGenerator P) X =
      cutDerivation P X := rfl

theorem derivConj_isLeibniz {B : Type*} [Ring B] [Algebra ℝ B]
    (θ : B ≃ₐ[ℝ] B) (hθ : Function.Involutive θ)
    (D : NonAssocDerivation.derivations ℝ B) :
    IsLeibniz ℝ B (θ.toLinearMap ∘ₗ (D : Module.End ℝ B) ∘ₗ θ.toLinearMap) := by
  intro X Y
  simp only [LinearMap.comp_apply, AlgEquiv.toLinearMap_apply, _root_.map_mul, derivations_leibniz]
  rw [_root_.map_add, _root_.map_mul, _root_.map_mul, hθ X, hθ Y]

/-- Lift an involutive algebra automorphism `θ : B ≃ₐ[ℝ] B` by conjugation to a Lie
automorphism of `NonAssocDerivation.derivations ℝ B`. -/
def derivConjLieEquiv {B : Type*} [Ring B] [Algebra ℝ B]
    (θ : B ≃ₐ[ℝ] B) (hθ : Function.Involutive θ) :
    NonAssocDerivation.derivations ℝ B ≃ₗ⁅ℝ⁆ NonAssocDerivation.derivations ℝ B where
  toFun D := ⟨θ.toLinearMap ∘ₗ (D : Module.End ℝ B) ∘ₗ θ.toLinearMap,
    derivConj_isLeibniz θ hθ D⟩
  invFun D := ⟨θ.toLinearMap ∘ₗ (D : Module.End ℝ B) ∘ₗ θ.toLinearMap,
    derivConj_isLeibniz θ hθ D⟩
  left_inv D := by
    apply Subtype.ext
    apply LinearMap.ext
    intro X
    simp only [LinearMap.comp_apply, AlgEquiv.toLinearMap_apply]
    rw [hθ X, hθ (D.1 X)]
  right_inv D := by
    apply Subtype.ext
    apply LinearMap.ext
    intro X
    simp only [LinearMap.comp_apply, AlgEquiv.toLinearMap_apply]
    rw [hθ X, hθ (D.1 X)]
  map_add' D E := by
    apply Subtype.ext
    apply LinearMap.ext
    intro X
    simp [_root_.map_add]
  map_smul' r D := by
    apply Subtype.ext
    apply LinearMap.ext
    intro X
    simp [_root_.map_smul]
  map_lie' {D E} := by
    apply Subtype.ext
    apply LinearMap.ext
    intro X
    have hθ' : ∀ Z, θ (θ Z) = Z := hθ
    simp only [NonAssocDerivation.lie_apply, LinearMap.comp_apply,
      AlgEquiv.toLinearMap_apply, _root_.map_sub, hθ']

/-- `SymmetricLieAlgebra` structure on `NonAssocDerivation.derivations ℝ B` induced by
an involutive algebra automorphism `θ`. -/
def derivSymmetricLieAlgebra {B : Type*} [Ring B] [Algebra ℝ B]
    (θ : B ≃ₐ[ℝ] B) (hθ : Function.Involutive θ) :
    SymmetricLieAlgebra (NonAssocDerivation.derivations ℝ B) :=
  SymmetricLieAlgebra.ofInvolutiveLieAut
    ⟨derivConjLieEquiv θ hθ, fun D => (derivConjLieEquiv θ hθ).left_inv D⟩

@[simp] theorem derivSymmetricLieAlgebra_theta_apply {B : Type*} [Ring B] [Algebra ℝ B]
    (θ : B ≃ₐ[ℝ] B) (hθ : Function.Involutive θ)
    (D : NonAssocDerivation.derivations ℝ B) (X : B) :
    (((derivSymmetricLieAlgebra θ hθ).θ D : NonAssocDerivation.derivations ℝ B) :
      Module.End ℝ B) X = θ (D.1 (θ X)) := rfl

/-- `SymmetricLieAlgebra` on `NonAssocDerivation.derivations ℝ (FiniteOperatorAlgebra n)`
lifted from `P : PeirceCut n`. -/
def peirceDerivSymmetricLieAlgebra {n : ℕ} (P : PeirceCut n) :
    SymmetricLieAlgebra (NonAssocDerivation.derivations ℝ (FiniteOperatorAlgebra n)) :=
  derivSymmetricLieAlgebra
    (conjugationAlgEquivOfSqOne (invS (P : FiniteOperatorAlgebra n))
      (invS_sq_eq_one (P : FiniteOperatorAlgebra n) P.property))
    (conjugationAlgEquivOfSqOne_involutive _ _)

theorem cutDerivation_mem_cutStabilizer {n : ℕ} (P : PeirceCut n) :
    FrechetBridge.toRealDerivation (cutDerivation P) ∈
      cutStabilizer (P : FiniteOperatorAlgebra n) := by
  change cutDerivation P (P : FiniteOperatorAlgebra n) = 0
  rw [cutDerivation_apply]
  change (P : FiniteOperatorAlgebra n) * P - P * P = 0
  exact sub_self _

theorem cutStabilizer_eq_evenLieSubalgebra {n : ℕ} (P : PeirceCut n) :
    cutStabilizer (P : FiniteOperatorAlgebra n) =
      (peirceDerivSymmetricLieAlgebra P).evenLieSubalgebra := by
  let S := invS (P : FiniteOperatorAlgebra n)
  have hS : S * S = 1 := invS_sq_eq_one (P : FiniteOperatorAlgebra n) P.property
  let θ := conjugationAlgEquivOfSqOne S hS
  have hθP : θ (P : FiniteOperatorAlgebra n) = P := by
    have hm := invS_mul_idem (P : FiniteOperatorAlgebra n) P.property
    change S * (P : FiniteOperatorAlgebra n) * S = P
    rw [hm.1, hm.2]
  apply LieSubalgebra.ext
  intro D
  rw [SymmetricLieAlgebra.mem_even_iff]
  change D.1 (P : FiniteOperatorAlgebra n) = 0 ↔
    (peirceDerivSymmetricLieAlgebra P).θ D = D
  constructor
  · intro hDP
    have hD1 : D.1 (1 : FiniteOperatorAlgebra n) = 0 := by
      have hmul : D.1 ((1 : FiniteOperatorAlgebra n) * 1) =
          D.1 1 * 1 + 1 * D.1 1 := D.property 1 1
      simp only [one_mul, mul_one] at hmul
      exact left_eq_add.mp hmul
    have hDS : D.1 S = 0 := by
      change D.1 (invS (P : FiniteOperatorAlgebra n)) = 0
      rw [invS_eq_two_smul_sub_one (P : FiniteOperatorAlgebra n), _root_.map_sub,
        _root_.map_smul, hDP, hD1]
      exact ContinuousLinearMap.ext fun _ => by simp
    apply Subtype.ext
    apply LinearMap.ext
    intro X
    change (conjugationAlgEquivOfSqOne (invS (P : FiniteOperatorAlgebra n))
        (invS_sq_eq_one (P : FiniteOperatorAlgebra n) P.property))
      (D.1 ((conjugationAlgEquivOfSqOne (invS (P : FiniteOperatorAlgebra n))
        (invS_sq_eq_one (P : FiniteOperatorAlgebra n) P.property)) X)) = D.1 X
    have hDθ : D.1 (θ X) = θ (D.1 X) := by
      change D.1 (S * X * S) = S * D.1 X * S
      rw [D.property (S * X) S, D.property S X, hDS, zero_mul, zero_add, mul_zero, add_zero,
        mul_assoc]
    change θ (D.1 (θ X)) = D.1 X
    rw [hDθ]
    exact (conjugationAlgEquivOfSqOne_involutive S hS) (D.1 X)
  · intro hconj
    have hAtP : θ (D.1 (θ (P : FiniteOperatorAlgebra n))) = D.1 P := by
      have h0 := congrArg
        (fun E : NonAssocDerivation.derivations ℝ (FiniteOperatorAlgebra n) =>
          (E : Module.End ℝ (FiniteOperatorAlgebra n)) (P : FiniteOperatorAlgebra n))
        hconj
      exact h0
    rw [hθP] at hAtP
    have hDP_idem : D.1 (P : FiniteOperatorAlgebra n) = D.1 P * P + P * D.1 P := by
      have hmul := D.property (P : FiniteOperatorAlgebra n) P
      rwa [P.property] at hmul
    have hP_DP_P : (P : FiniteOperatorAlgebra n) * D.1 P * P = 0 := by
      have h1 : (P : FiniteOperatorAlgebra n) * D.1 P * P =
          (P : FiniteOperatorAlgebra n) * (D.1 P * P + P * D.1 P) * P := by
        rw [← hDP_idem]
      have h2 : (P : FiniteOperatorAlgebra n) * (D.1 P * P + P * D.1 P) * P =
          (P : FiniteOperatorAlgebra n) * D.1 P * P + P * D.1 P * P := by
        calc
          _ = (P : FiniteOperatorAlgebra n) * D.1 P * (P * P) +
                (P * P) * D.1 P * P := by noncomm_ring
          _ = _ := by rw [P.property]
      rw [h2] at h1
      exact left_eq_add.mp h1
    have hQ_DP_Q : (1 - (P : FiniteOperatorAlgebra n)) * D.1 P * (1 - P) = 0 := by
      have h1 : (1 - (P : FiniteOperatorAlgebra n)) * D.1 P * (1 - P) =
          (1 - P) * (D.1 P * P + P * D.1 P) * (1 - P) := by
        rw [← hDP_idem]
      have h2 : (1 - (P : FiniteOperatorAlgebra n)) * (D.1 P * P + P * D.1 P) * (1 - P) = 0 := by
        have hP1 : (P : FiniteOperatorAlgebra n) * (1 - P) = 0 := by
          rw [mul_sub, mul_one, P.property, sub_self]
        have h1P : (1 - (P : FiniteOperatorAlgebra n)) * P = 0 := by
          rw [sub_mul, one_mul, P.property, sub_self]
        calc
          (1 - (P : FiniteOperatorAlgebra n)) * (D.1 P * P + P * D.1 P) * (1 - P)
              = (1 - P) * (D.1 P * P) * (1 - P) + (1 - P) * (P * D.1 P) * (1 - P) := by
                rw [mul_add, add_mul]
          _ = (1 - P) * D.1 P * (P * (1 - P)) + ((1 - P) * P) * D.1 P * (1 - P) := by
                simp only [mul_assoc]
          _ = 0 := by rw [hP1, h1P, mul_zero, zero_mul, zero_mul, add_zero]
      exact h1.trans h2
    have hEvenZero : evenGrade (P : FiniteOperatorAlgebra n) (D.1 P) = 0 := by
      change (P : FiniteOperatorAlgebra n) * D.1 P * P + (1 - P) * D.1 P * (1 - P) = 0
      rw [hP_DP_P, hQ_DP_Q, add_zero]
    have hsum : evenGrade (P : FiniteOperatorAlgebra n) (D.1 P) +
        oddGrade (P : FiniteOperatorAlgebra n) (D.1 P) = D.1 P :=
      (grade_projection_laws P.property (D.1 P)).2.2.2.2
    have hOddEq : oddGrade (P : FiniteOperatorAlgebra n) (D.1 P) = D.1 P := by
      rw [hEvenZero, zero_add] at hsum
      exact hsum
    have hθNeg : θ (D.1 (P : FiniteOperatorAlgebra n)) = -D.1 P := by
      have hgrade :=
        (archetype_A2_peirce_cartan_grading_and_tangent_closure
          (P := (P : FiniteOperatorAlgebra n)) P.property
          (D.1 (P : FiniteOperatorAlgebra n)) (D.1 P)).2.2.2.2.2.2
      change invS (P : FiniteOperatorAlgebra n) * D.1 P *
          invS (P : FiniteOperatorAlgebra n) = _ at hgrade
      change S * D.1 (P : FiniteOperatorAlgebra n) * S = -D.1 P
      rw [hgrade, hEvenZero, hOddEq, zero_sub]
    have hEqNeg : D.1 (P : FiniteOperatorAlgebra n) = -D.1 P := hAtP.symm.trans hθNeg
    have htwo : (2 : ℝ) • D.1 (P : FiniteOperatorAlgebra n) = 0 := by
      calc
        (2 : ℝ) • D.1 (P : FiniteOperatorAlgebra n) =
            D.1 (P : FiniteOperatorAlgebra n) + D.1 (P : FiniteOperatorAlgebra n) :=
          two_smul ℝ (D.1 (P : FiniteOperatorAlgebra n))
        _ = D.1 P + (-D.1 P) := congrArg (fun Z => D.1 P + Z) hEqNeg
        _ = 0 := add_neg_cancel _
    have hhalf := congrArg (fun Z : FiniteOperatorAlgebra n => ((2 : ℝ)⁻¹) • Z) htwo
    rw [smul_smul, inv_mul_cancel₀ (by norm_num), one_smul] at hhalf
    exact hhalf.trans (ContinuousLinearMap.ext fun _ => by simp)

theorem cutDerivation_mem_deriv_k {n : ℕ} (P : PeirceCut n) :
    FrechetBridge.toRealDerivation (cutDerivation P) ∈
      (peirceDerivSymmetricLieAlgebra P).𝔨 := by
  change FrechetBridge.toRealDerivation (cutDerivation P) ∈
    (peirceDerivSymmetricLieAlgebra P).evenLieSubalgebra
  rw [← cutStabilizer_eq_evenLieSubalgebra P]
  exact cutDerivation_mem_cutStabilizer P

/-- `CartanOnsagerSplit` on the Lie algebra `NonAssocDerivation.derivations ℝ (FiniteOperatorAlgebra n)`
whose `drazinCore` is `cutStabilizer P` (`= S.𝔨`) and `onsager` is `P_minus`. -/
def peirceDerivCartanOnsagerSplit {n : ℕ} (P : PeirceCut n) :
    CartanOnsagerSplit (NonAssocDerivation.derivations ℝ (FiniteOperatorAlgebra n)) where
  S := peirceDerivSymmetricLieAlgebra P
  onsager := (peirceDerivSymmetricLieAlgebra P).P_minus
  drazinCore := (cutStabilizer (P : FiniteOperatorAlgebra n)).toSubmodule
  dissipativeRange := (peirceDerivSymmetricLieAlgebra P).𝔭
  drazinCore_eq_k := congrArg LieSubalgebra.toSubmodule (cutStabilizer_eq_evenLieSubalgebra P)
  dissipativeRange_eq_p := rfl

end DerivationLieLaneBridge

end InfoGeometry.SuperMetriplectic.PeirceCutCartanDerivationBridge
