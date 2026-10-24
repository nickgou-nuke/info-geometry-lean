/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import Mathlib
import InfoGeometry.Core.PeirceDecomposition
import InfoGeometry.Meta.ArchetypePipeline
import InfoGeometry.Meta.EpistemicCompilerChain
import InfoGeometry.Meta.MetaEpistemicCompiler

/-!
# Idempotent conjugation orbits, Peirce corners, and active-support polynomial laws

All results are algebraic over an associative ring. The unit orbit below is a
single conjugacy orbit, not the set of every idempotent. Its quotient description
is set-theoretic; no topological local triviality is asserted.

The historically named tangent/cotangent parts are opposite Peirce corners.
Their commutator is diagonal; no holomorphic cotangent identification or
Ehresmann connection is supplied. The trace identity is invariance of a possibly
degenerate additive pairing. The cubic for ad_P is an annihilating polynomial,
not a claim of minimality.

For square-zero reflexive pairs, Delta is the identity on their active support.
Gamma squared equals Delta: this is the t^2-1 law, NOT Phi_2(t)=t+1.
The degree-two Phi_3, Phi_4 and Phi_6 identities use Delta as their constant term.
No primitivity or exact multiplicative order is asserted in arbitrary characteristic.
The reflection swaps supports algebraically; no Spin/Pin group, star-adjoint
partial isometry, or topological orientability is inferred.
-/

namespace InfoGeometry.Canonical.GrassmannianBundleCyclotomicOrientability

section AbstractOperatorBundle

variable {A : Type*} [Ring A]

/-!
## 1. Archetype 1: Algebraic conjugation identities
-/

/-- Symmetrized Jordan anticommutator `{X, Y} = X Y + Y X`. -/
def jordanProd (X Y : A) : A := X * Y + Y * X

/-- Antisymmetric Lie commutator `[X, Y] = X Y - Y X` (adjoint action `ad_X(Y)`). -/
def lieBracket (X Y : A) : A := X * Y - Y * X

/-- Homogeneous Grassmannian projection map `π(g) = g * P₀ * g_inv`. -/
def homogeneousProj (g g_inv P₀ : A) : A :=
  g * P₀ * g_inv

/-- A left inverse is sufficient for this idempotency identity; a unit orbit
requires a two-sided unit, as in `unitOrbitMap` below. -/
lemma isIdempotentElem_homogeneousProj {P₀ g g_inv : A}
    (hP₀ : IsIdempotentElem P₀) (h_gg : g_inv * g = 1) :
    IsIdempotentElem (homogeneousProj g g_inv P₀) := by
  unfold IsIdempotentElem homogeneousProj
  calc (g * P₀ * g_inv) * (g * P₀ * g_inv)
    _ = g * P₀ * (g_inv * g) * P₀ * g_inv := by simp only [mul_assoc]
    _ = g * (P₀ * P₀) * g_inv := by rw [h_gg, mul_one]; simp only [mul_assoc]
    _ = g * P₀ * g_inv := by rw [hP₀.eq]

/-- Right gauge invariance under the isotropy subgroup `K = {k | k * P₀ = P₀ * k}`. -/
lemma homogeneousProj_right_gauge_invariant {P₀ g g_inv k k_inv : A}
    (h_kk : k * k_inv = 1) (h_stab : k * P₀ = P₀ * k) :
    homogeneousProj (g * k) (k_inv * g_inv) P₀ = homogeneousProj g g_inv P₀ := by
  unfold homogeneousProj
  calc (g * k) * P₀ * (k_inv * g_inv)
    _ = g * (k * P₀) * k_inv * g_inv := by simp only [mul_assoc]
    _ = g * P₀ * (k * k_inv) * g_inv := by rw [h_stab]; simp only [mul_assoc]
    _ = g * P₀ * g_inv := by rw [h_kk, mul_one]

/-- Left `G`-equivariance of the homogeneous Grassmannian projection. -/
lemma homogeneousProj_left_equivariant (P₀ g g_inv h h_inv : A) :
    homogeneousProj (h * g) (g_inv * h_inv) P₀ = h * homogeneousProj g g_inv P₀ * h_inv := by
  unfold homogeneousProj
  simp only [mul_assoc]

/-- Algebraic idempotency, right stabilizer invariance and left covariance.
The historical name does not assert a principal bundle or local triviality. -/
theorem principal_bundle_grassmannian_orbit
    {P₀ g g_inv k k_inv h h_inv : A}
    (hP₀ : IsIdempotentElem P₀)
    (h_gg : g_inv * g = 1)
    (h_kk : k * k_inv = 1)
    (h_stab : k * P₀ = P₀ * k) :
    let Pg := homogeneousProj g g_inv P₀
    IsIdempotentElem Pg ∧
    homogeneousProj (g * k) (k_inv * g_inv) P₀ = Pg ∧
    homogeneousProj (h * g) (g_inv * h_inv) P₀ = h * Pg * h_inv :=
  ⟨isIdempotentElem_homogeneousProj hP₀ h_gg,
   homogeneousProj_right_gauge_invariant h_kk h_stab,
   homogeneousProj_left_equivariant P₀ g g_inv h h_inv⟩

/-!
## 2. Archetype 2: Diagonal and opposite square-zero Peirce corners
-/

/-- Diagonal Peirce projection `P X P + (1 - P) X (1 - P)`. -/
def normalBundlePart (P X : A) : A :=
  P * X * P + (1 - P) * X * (1 - P)

/-- Lower square-zero Peirce corner `(1 - P) * X * P`. -/
def tangentNilpotent (P X : A) : A :=
  (1 - P) * X * P

/-- Upper square-zero Peirce corner `P * Y * (1 - P)`. -/
def cotangentNilpotent (P Y : A) : A :=
  P * Y * (1 - P)

/-- Cartan grading expression `Γ_P = 2 P - 1`, involutive when P is idempotent. -/
def orientationInvolution (P : A) : A := 2 • P - 1

lemma normal_tangent_cotangent_decomp (P X : A) :
    normalBundlePart P X + tangentNilpotent P X + cotangentNilpotent P X = X := by
  have h := InfoGeometry.Core.PeirceDecomposition.peirce_decomposition P X
  dsimp [InfoGeometry.Core.PeirceDecomposition.component11,
    InfoGeometry.Core.PeirceDecomposition.component10,
    InfoGeometry.Core.PeirceDecomposition.component01,
    InfoGeometry.Core.PeirceDecomposition.component00,
    InfoGeometry.Core.PeirceDecomposition.complementIdempotent] at h
  unfold normalBundlePart tangentNilpotent cotangentNilpotent
  calc
    _ = P * X * P + P * X * (1 - P) + (1 - P) * X * P +
        (1 - P) * X * (1 - P) := by abel
    _ = X := h.symm

lemma tangentNilpotent_sq_zero {P : A} (hP : IsIdempotentElem P) (X : A) :
    tangentNilpotent P X * tangentNilpotent P X = 0 := by
  unfold tangentNilpotent
  calc ((1 - P) * X * P) * ((1 - P) * X * P)
    _ = (1 - P) * X * (P - P * P) * X * P := by noncomm_ring
    _ = 0 := by rw [hP.eq, sub_self, mul_zero, zero_mul, zero_mul]

lemma cotangentNilpotent_sq_zero {P : A} (hP : IsIdempotentElem P) (Y : A) :
    cotangentNilpotent P Y * cotangentNilpotent P Y = 0 := by
  unfold cotangentNilpotent
  calc (P * Y * (1 - P)) * (P * Y * (1 - P))
    _ = P * Y * (P - P * P) * Y * (1 - P) := by noncomm_ring
    _ = 0 := by rw [hP.eq, sub_self, mul_zero, zero_mul, zero_mul]

lemma mul_tangentNilpotent_left {P : A} (hP : IsIdempotentElem P) (X : A) :
    P * tangentNilpotent P X = 0 := by
  unfold tangentNilpotent
  calc P * ((1 - P) * X * P) = (P - P * P) * X * P := by noncomm_ring
    _ = 0 := by rw [hP.eq, sub_self, zero_mul, zero_mul]

lemma mul_tangentNilpotent_right {P : A} (hP : IsIdempotentElem P) (X : A) :
    tangentNilpotent P X * P = tangentNilpotent P X := by
  unfold tangentNilpotent
  rw [mul_assoc, hP.eq]

lemma mul_cotangentNilpotent_left {P : A} (hP : IsIdempotentElem P) (Y : A) :
    P * cotangentNilpotent P Y = cotangentNilpotent P Y := by
  unfold cotangentNilpotent
  rw [← mul_assoc, ← mul_assoc, hP.eq]

lemma mul_cotangentNilpotent_right {P : A} (hP : IsIdempotentElem P) (Y : A) :
    cotangentNilpotent P Y * P = 0 := by
  unfold cotangentNilpotent
  calc (P * Y * (1 - P)) * P = P * Y * (P - P * P) := by noncomm_ring
    _ = 0 := by rw [hP.eq, sub_self, mul_zero]

lemma orientationInvolution_mul_tangentNilpotent {P : A}
    (hP : IsIdempotentElem P) (X : A) :
    orientationInvolution P * tangentNilpotent P X = -tangentNilpotent P X := by
  unfold orientationInvolution
  rw [two_nsmul, sub_mul, add_mul, one_mul, mul_tangentNilpotent_left hP X, add_zero, zero_sub]

lemma tangentNilpotent_mul_orientationInvolution {P : A}
    (hP : IsIdempotentElem P) (X : A) :
    tangentNilpotent P X * orientationInvolution P = tangentNilpotent P X := by
  unfold orientationInvolution
  rw [two_nsmul, mul_sub, mul_add, mul_one, mul_tangentNilpotent_right hP X]
  abel

lemma orientationInvolution_mul_cotangentNilpotent {P : A}
    (hP : IsIdempotentElem P) (Y : A) :
    orientationInvolution P * cotangentNilpotent P Y = cotangentNilpotent P Y := by
  unfold orientationInvolution
  rw [two_nsmul, sub_mul, add_mul, one_mul, mul_cotangentNilpotent_left hP Y]
  abel

lemma cotangentNilpotent_mul_orientationInvolution {P : A}
    (hP : IsIdempotentElem P) (Y : A) :
    cotangentNilpotent P Y * orientationInvolution P = -cotangentNilpotent P Y := by
  unfold orientationInvolution
  rw [two_nsmul, mul_sub, mul_add, mul_one, mul_cotangentNilpotent_right hP Y, add_zero, zero_sub]

lemma jordanProd_tangentNilpotent {P : A} (hP : IsIdempotentElem P) (X : A) :
    jordanProd P (tangentNilpotent P X) = tangentNilpotent P X := by
  unfold jordanProd
  rw [mul_tangentNilpotent_left hP X, mul_tangentNilpotent_right hP X, zero_add]

lemma jordanProd_cotangentNilpotent {P : A} (hP : IsIdempotentElem P) (Y : A) :
    jordanProd P (cotangentNilpotent P Y) = cotangentNilpotent P Y := by
  unfold jordanProd
  rw [mul_cotangentNilpotent_left hP Y, mul_cotangentNilpotent_right hP Y, add_zero]

lemma lieBracket_cotangent_tangent_commutes {P : A}
    (hP : IsIdempotentElem P) (X Y : A) :
    lieBracket P (lieBracket (cotangentNilpotent P Y) (tangentNilpotent P X)) = 0 := by
  let d := tangentNilpotent P X
  let B := cotangentNilpotent P Y
  have h_P_Bd : P * (B * d) = B * d := by rw [← mul_assoc, mul_cotangentNilpotent_left hP Y]
  have h_Bd_P : (B * d) * P = B * d := by rw [mul_assoc, mul_tangentNilpotent_right hP X]
  have h_P_dB : P * (d * B) = 0 := by rw [← mul_assoc, mul_tangentNilpotent_left hP X, zero_mul]
  have h_dB_P : (d * B) * P = 0 := by rw [mul_assoc, mul_cotangentNilpotent_right hP Y, mul_zero]
  unfold lieBracket
  change P * (B * d - d * B) - (B * d - d * B) * P = 0
  rw [mul_sub, sub_mul, h_P_Bd, h_P_dB, h_Bd_P, h_dB_P, sub_self]

lemma normalBundlePart_lieBracket_cotangent_tangent {P : A}
    (hP : IsIdempotentElem P) (X Y : A) :
    normalBundlePart P (lieBracket (cotangentNilpotent P Y) (tangentNilpotent P X)) =
      lieBracket (cotangentNilpotent P Y) (tangentNilpotent P X) := by
  let d := tangentNilpotent P X
  let B := cotangentNilpotent P Y
  have h_P_Bd : P * (B * d) = B * d := by rw [← mul_assoc, mul_cotangentNilpotent_left hP Y]
  have h_Bd_P : (B * d) * P = B * d := by rw [mul_assoc, mul_tangentNilpotent_right hP X]
  have h_P_dB : P * (d * B) = 0 := by rw [← mul_assoc, mul_tangentNilpotent_left hP X, zero_mul]
  have h_dB_P : (d * B) * P = 0 := by rw [mul_assoc, mul_cotangentNilpotent_right hP Y, mul_zero]
  unfold normalBundlePart lieBracket
  change P * (B * d - d * B) * P + (1 - P) * (B * d - d * B) * (1 - P) = B * d - d * B
  calc P * (B * d - d * B) * P + (1 - P) * (B * d - d * B) * (1 - P)
    _ = P * (B * d) * P - P * (d * B) * P +
        (B * d - P * (B * d) - (B * d) * P + P * (B * d) * P) -
        (d * B - P * (d * B) - (d * B) * P + P * (d * B) * P) := by noncomm_ring
    _ = B * d - d * B := by
        rw [h_P_Bd, h_Bd_P, h_P_dB, h_dB_P, zero_mul]
        abel

/-- Peirce decomposition, corner nilpotency, grading signs and diagonality of
the mixed commutator. No cotangent duality or Ehresmann connection is constructed. -/
theorem normal_tangent_cotangent_bundle_split {P : A}
    (hP : IsIdempotentElem P) (X Y : A) :
    let Γ := orientationInvolution P
    let N_X := normalBundlePart P X
    let d := tangentNilpotent P X
    let d_X := cotangentNilpotent P X
    let B := cotangentNilpotent P Y
    (N_X + d + d_X = X) ∧
    (d * d = 0 ∧ B * B = 0 ∧
     Γ * d = -d ∧ d * Γ = d ∧
     Γ * B = B ∧ B * Γ = -B ∧
     jordanProd P d = d ∧ jordanProd P B = B) ∧
    (lieBracket P (lieBracket B d) = 0 ∧
     normalBundlePart P (lieBracket B d) = lieBracket B d) :=
  ⟨normal_tangent_cotangent_decomp P X,
   ⟨tangentNilpotent_sq_zero hP X,
    cotangentNilpotent_sq_zero hP Y,
    orientationInvolution_mul_tangentNilpotent hP X,
    tangentNilpotent_mul_orientationInvolution hP X,
    orientationInvolution_mul_cotangentNilpotent hP Y,
    cotangentNilpotent_mul_orientationInvolution hP Y,
    jordanProd_tangentNilpotent hP X,
    jordanProd_cotangentNilpotent hP Y⟩,
   ⟨lieBracket_cotangent_tangent_commutes hP X Y,
    normalBundlePart_lieBracket_cotangent_tangent hP X Y⟩⟩

/-!
## 3. Archetype 3: Tracial pairing invariance and cubic annihilation of `ad_P`
-/

/-- Tracial invariance of the Lie bracket pairing `τ(ξ [L, X]) + τ([L, ξ] X) = 0`. -/
theorem trace_coadjoint_invariance
    {G : Type*} [AddCommGroup G] {τ : A →+ G}
    (hτ : ∀ U V : A, τ (U * V) = τ (V * U)) (L ξ X : A) :
    τ (ξ * lieBracket L X) + τ (lieBracket L ξ * X) = 0 := by
  unfold lieBracket
  calc τ (ξ * (L * X - X * L)) + τ ((L * ξ - ξ * L) * X)
    _ = τ ((ξ * L) * X - (ξ * X) * L) + τ (L * (ξ * X) - (ξ * L) * X) := by
        rw [← map_add, ← map_add]
        congr 1
        noncomm_ring
    _ = (τ ((ξ * L) * X) - τ ((ξ * X) * L)) + (τ (L * (ξ * X)) - τ ((ξ * L) * X)) := by
        rw [map_sub, map_sub]
    _ = 0 := by
        rw [hτ L (ξ * X)]
        abel

/-- The cubic is stated only as an annihilating identity `ad_P³(X) = ad_P(X)`. -/
theorem adjoint_idempotent_cubic {P : A} (hP : IsIdempotentElem P) (X : A) :
    lieBracket P (lieBracket P (lieBracket P X)) = lieBracket P X := by
  have hP_eq : P * P = P := hP.eq
  unfold lieBracket
  calc P * (P * (P * X - X * P) - (P * X - X * P) * P) -
       (P * (P * X - X * P) - (P * X - X * P) * P) * P
    _ = (P * P * P) * X - 3 • ((P * P) * X * P) +
        3 • (P * X * (P * P)) - X * (P * P * P) := by noncomm_ring
    _ = P * X - X * P := by rw [hP_eq, hP_eq]; abel

theorem lieBracket_normalBundlePart_eq_zero {P : A} (hP : IsIdempotentElem P) (X : A) :
    lieBracket P (normalBundlePart P X) = 0 := by
  have hP_eq : P * P = P := hP.eq
  unfold lieBracket normalBundlePart
  calc P * (P * X * P + (1 - P) * X * (1 - P)) -
       (P * X * P + (1 - P) * X * (1 - P)) * P
    _ = (P * P - P) * X * P + P * X * (P - P * P) +
        (P - P * P) * X * (1 - P) - (1 - P) * X * (P - P * P) := by noncomm_ring
    _ = 0 := by rw [hP_eq, sub_self]; noncomm_ring

theorem lieBracket_tangentNilpotent {P : A} (hP : IsIdempotentElem P) (X : A) :
    lieBracket P (tangentNilpotent P X) = -tangentNilpotent P X := by
  have hP_eq : P * P = P := hP.eq
  unfold lieBracket tangentNilpotent
  calc P * ((1 - P) * X * P) - ((1 - P) * X * P) * P
    _ = (P - P * P) * X * P - (1 - P) * X * (P * P) := by noncomm_ring
    _ = -((1 - P) * X * P) := by rw [hP_eq, sub_self, zero_mul, zero_mul, zero_sub]

theorem lieBracket_cotangentNilpotent {P : A} (hP : IsIdempotentElem P) (Y : A) :
    lieBracket P (cotangentNilpotent P Y) = cotangentNilpotent P Y := by
  have hP_eq : P * P = P := hP.eq
  unfold lieBracket cotangentNilpotent
  calc P * (P * Y * (1 - P)) - (P * Y * (1 - P)) * P
    _ = (P * P) * Y * (1 - P) - P * Y * (P - P * P) := by noncomm_ring
    _ = P * Y * (1 - P) := by rw [hP_eq, sub_self, mul_zero, sub_zero]

/-- **Tracial pairing invariance and cubic annihilation of `ad_P` (`adjoint_coadjoint_cubic_law`)**. -/
theorem adjoint_coadjoint_cubic_law
    {G : Type*} [AddCommGroup G] {τ : A →+ G}
    (hτ : ∀ U V : A, τ (U * V) = τ (V * U))
    {P : A} (hP : IsIdempotentElem P) (L ξ X Y : A) :
    (τ (ξ * lieBracket L X) + τ (lieBracket L ξ * X) = 0) ∧
    (lieBracket P (lieBracket P (lieBracket P X)) = lieBracket P X ∧
     lieBracket P (normalBundlePart P X) = 0 ∧
     lieBracket P (tangentNilpotent P X) = -tangentNilpotent P X ∧
     lieBracket P (cotangentNilpotent P Y) = cotangentNilpotent P Y) :=
  ⟨trace_coadjoint_invariance hτ L ξ X,
   ⟨adjoint_idempotent_cubic hP X,
    lieBracket_normalBundlePart_eq_zero hP X,
    lieBracket_tangentNilpotent hP X,
    lieBracket_cotangentNilpotent hP Y⟩⟩

/-!
## 4. Active-support involution, Φ₃/Φ₄/Φ₆ laws and algebraic support exchange
-/

/-- Active-support fourth-order operator `J₄ = d - B` (`Φ₄(J₄) = J₄^2 + Δ = 0`). -/
def cyclotomic4Op (d B : A) : A := d - B

/-- Active-support third-order operator `ω₃ = -(B * d) + d - B` (`Φ₃(ω₃) = ω₃^2 + ω₃ + Δ = 0`). -/
def cyclotomic3Op (d B : A) : A := -(B * d) + d - B

/-- Active-support sixth-order operator `η₆ = (B * d) - d + B` (`Φ₆(η₆) = η₆^2 - η₆ + Δ = 0`). -/
def cyclotomic6Op (d B : A) : A := (B * d) - d + B

lemma active_pos_idempotent {d B : A} (h_dBd : d * B * d = d) :
    (d * B) * (d * B) = d * B := by
  calc (d * B) * (d * B) = (d * B * d) * B := by noncomm_ring
    _ = d * B := by rw [h_dBd]

lemma active_neg_idempotent {d B : A} (h_BdB : B * d * B = B) :
    (B * d) * (B * d) = B * d := by
  calc (B * d) * (B * d) = (B * d * B) * d := by noncomm_ring
    _ = B * d := by rw [h_BdB]

lemma active_pos_mul_neg {d B : A} (hB : B * B = 0) :
    (d * B) * (B * d) = 0 := by
  calc (d * B) * (B * d) = d * (B * B) * d := by noncomm_ring
    _ = 0 := by rw [hB, mul_zero, zero_mul]

lemma active_neg_mul_pos {d B : A} (hd : d * d = 0) :
    (B * d) * (d * B) = 0 := by
  calc (B * d) * (d * B) = B * (d * d) * B := by noncomm_ring
    _ = 0 := by rw [hd, mul_zero, zero_mul]

lemma active_support_sq {d B : A}
    (hd : d * d = 0) (hB : B * B = 0)
    (h_dBd : d * B * d = d) (h_BdB : B * d * B = B) :
    (d * B + B * d) * (d * B + B * d) = d * B + B * d := by
  rw [add_mul, mul_add, mul_add, active_pos_idempotent h_dBd,
      active_pos_mul_neg hB, active_neg_mul_pos hd, active_neg_idempotent h_BdB,
      add_zero, zero_add]

lemma active_grading_sq {d B : A}
    (hd : d * d = 0) (hB : B * B = 0)
    (h_dBd : d * B * d = d) (h_BdB : B * d * B = B) :
    (d * B - B * d) * (d * B - B * d) = d * B + B * d := by
  rw [sub_mul, mul_sub, mul_sub, active_pos_idempotent h_dBd,
      active_pos_mul_neg hB, active_neg_mul_pos hd, active_neg_idempotent h_BdB]
  abel

lemma active_grading_sq_sub_support {d B : A}
    (hd : d * d = 0) (hB : B * B = 0)
    (h_dBd : d * B * d = d) (h_BdB : B * d * B = B) :
    (d * B - B * d) * (d * B - B * d) - (d * B + B * d) = 0 :=
  sub_eq_zero.mpr (active_grading_sq hd hB h_dBd h_BdB)

lemma cyclotomic4Op_sq {d B : A} (hd : d * d = 0) (hB : B * B = 0) :
    cyclotomic4Op d B * cyclotomic4Op d B = -(d * B + B * d) := by
  unfold cyclotomic4Op
  calc (d - B) * (d - B) = d * d - (d * B + B * d) + B * B := by noncomm_ring
    _ = -(d * B + B * d) := by rw [hd, hB]; abel

lemma cyclotomic4Op_sq_add_support {d B : A} (hd : d * d = 0) (hB : B * B = 0) :
    cyclotomic4Op d B * cyclotomic4Op d B + (d * B + B * d) = 0 := by
  rw [cyclotomic4Op_sq hd hB, neg_add_cancel]

lemma cyclotomic4Op_pow_four {d B : A}
    (hd : d * d = 0) (hB : B * B = 0)
    (h_dBd : d * B * d = d) (h_BdB : B * d * B = B) :
    cyclotomic4Op d B ^ 4 = d * B + B * d := by
  calc cyclotomic4Op d B ^ 4
    _ = (cyclotomic4Op d B * cyclotomic4Op d B) *
        (cyclotomic4Op d B * cyclotomic4Op d B) := by noncomm_ring
    _ = -(d * B + B * d) * -(d * B + B * d) := by rw [cyclotomic4Op_sq hd hB]
    _ = (d * B + B * d) * (d * B + B * d) := neg_mul_neg _ _
    _ = d * B + B * d := active_support_sq hd hB h_dBd h_BdB

lemma cyclotomic3Op_sq {d B : A}
    (hd : d * d = 0) (hB : B * B = 0)
    (h_dBd : d * B * d = d) (h_BdB : B * d * B = B) :
    cyclotomic3Op d B * cyclotomic3Op d B = -(d * B) - d + B := by
  have h_Pm_d : (B * d) * d = 0 := by rw [mul_assoc, hd, mul_zero]
  have h_d_Pm : d * (B * d) = d := by rw [← mul_assoc, h_dBd]
  have h_B_Pm : B * (B * d) = 0 := by rw [← mul_assoc, hB, zero_mul]
  unfold cyclotomic3Op
  calc (-(B * d) + d - B) * (-(B * d) + d - B)
    _ = (B * d) * (B * d) - (B * d) * d + (B * d * B) - d * (B * d) + d * d - d * B +
        B * (B * d) - B * d + B * B := by noncomm_ring
    _ = B * d - 0 + B - d + 0 - d * B + 0 - B * d + 0 := by
        rw [active_neg_idempotent h_BdB, h_Pm_d, h_BdB, h_d_Pm, hd, h_B_Pm, hB]
    _ = -(d * B) - d + B := by abel

lemma cyclotomic3Op_quad_add_support {d B : A}
    (hd : d * d = 0) (hB : B * B = 0)
    (h_dBd : d * B * d = d) (h_BdB : B * d * B = B) :
    cyclotomic3Op d B * cyclotomic3Op d B + cyclotomic3Op d B + (d * B + B * d) = 0 := by
  rw [cyclotomic3Op_sq hd hB h_dBd h_BdB]
  unfold cyclotomic3Op
  abel

lemma cyclotomic3Op_pow_three {d B : A}
    (hd : d * d = 0) (hB : B * B = 0)
    (h_dBd : d * B * d = d) (h_BdB : B * d * B = B) :
    cyclotomic3Op d B ^ 3 = d * B + B * d := by
  have h_d_Pm : d * (B * d) = d := by rw [← mul_assoc, h_dBd]
  have h_Pp_B : (d * B) * B = 0 := by rw [mul_assoc, hB, mul_zero]
  have h_B_Pm : B * (B * d) = 0 := by rw [← mul_assoc, hB, zero_mul]
  calc cyclotomic3Op d B ^ 3
    _ = (cyclotomic3Op d B * cyclotomic3Op d B) * cyclotomic3Op d B := by noncomm_ring
    _ = (-(d * B) - d + B) * (-(B * d) + d - B) := by
        rw [cyclotomic3Op_sq hd hB h_dBd h_BdB]; rfl
    _ = (d * B) * (B * d) - (d * B * d) + (d * B) * B + d * (B * d) - d * d + d * B -
        B * (B * d) + B * d - B * B := by noncomm_ring
    _ = 0 - d + 0 + d - 0 + d * B - 0 + B * d - 0 := by
        rw [active_pos_mul_neg hB, h_dBd, h_Pp_B, h_d_Pm, hd, h_B_Pm, hB]
    _ = d * B + B * d := by abel

lemma cyclotomic6Op_eq_neg_cyclotomic3Op (d B : A) :
    cyclotomic6Op d B = -cyclotomic3Op d B := by
  unfold cyclotomic6Op cyclotomic3Op
  abel

lemma cyclotomic6Op_quad_sub_support {d B : A}
    (hd : d * d = 0) (hB : B * B = 0)
    (h_dBd : d * B * d = d) (h_BdB : B * d * B = B) :
    cyclotomic6Op d B * cyclotomic6Op d B - cyclotomic6Op d B + (d * B + B * d) = 0 := by
  rw [cyclotomic6Op_eq_neg_cyclotomic3Op d B, neg_mul_neg, sub_neg_eq_add]
  exact cyclotomic3Op_quad_add_support hd hB h_dBd h_BdB

lemma cyclotomic6Op_pow_three {d B : A}
    (hd : d * d = 0) (hB : B * B = 0)
    (h_dBd : d * B * d = d) (h_BdB : B * d * B = B) :
    cyclotomic6Op d B ^ 3 = -(d * B + B * d) := by
  rw [cyclotomic6Op_eq_neg_cyclotomic3Op d B]
  calc (-cyclotomic3Op d B) ^ 3 = -(cyclotomic3Op d B ^ 3) := by noncomm_ring
    _ = -(d * B + B * d) := by rw [cyclotomic3Op_pow_three hd hB h_dBd h_BdB]

lemma cyclotomic6Op_pow_six {d B : A}
    (hd : d * d = 0) (hB : B * B = 0)
    (h_dBd : d * B * d = d) (h_BdB : B * d * B = B) :
    cyclotomic6Op d B ^ 6 = d * B + B * d := by
  calc cyclotomic6Op d B ^ 6
    _ = (cyclotomic6Op d B ^ 3) * (cyclotomic6Op d B ^ 3) := by noncomm_ring
    _ = -(d * B + B * d) * -(d * B + B * d) := by rw [cyclotomic6Op_pow_three hd hB h_dBd h_BdB]
    _ = (d * B + B * d) * (d * B + B * d) := neg_mul_neg _ _
    _ = d * B + B * d := active_support_sq hd hB h_dBd h_BdB

lemma reflection_conjugates_grading {d B : A}
    (hd : d * d = 0) (hB : B * B = 0)
    (h_dBd : d * B * d = d) (h_BdB : B * d * B = B) :
    (d + B) * (d * B - B * d) * (d + B) = -(d * B - B * d) := by
  have h_d_Pp : d * (d * B) = 0 := by rw [← mul_assoc, hd, zero_mul]
  have h_d_Pm : d * (B * d) = d := by rw [← mul_assoc, h_dBd]
  have h_B_Pp : B * (d * B) = B := by rw [← mul_assoc, h_BdB]
  have h_B_Pm : B * (B * d) = 0 := by rw [← mul_assoc, hB, zero_mul]
  have h_left : (d + B) * (d * B - B * d) = B - d := by
    calc (d + B) * (d * B - B * d)
      _ = d * (d * B) - d * (B * d) + B * (d * B) - B * (B * d) := by noncomm_ring
      _ = B - d := by rw [h_d_Pp, h_d_Pm, h_B_Pp, h_B_Pm]; abel
  rw [h_left]
  calc (B - d) * (d + B) = B * d + B * B - d * d - d * B := by noncomm_ring
    _ = -(d * B - B * d) := by rw [hB, hd]; abel

lemma reflection_swaps_positive_support {d B : A}
    (hd : d * d = 0) (hB : B * B = 0) (h_BdB : B * d * B = B) :
    (d + B) * (d * B) * (d + B) = B * d := by
  have h_d_Pp : d * (d * B) = 0 := by rw [← mul_assoc, hd, zero_mul]
  have h_B_Pp : B * (d * B) = B := by rw [← mul_assoc, h_BdB]
  calc (d + B) * (d * B) * (d + B)
    _ = (d * (d * B) + B * (d * B)) * (d + B) := by noncomm_ring
    _ = B * d + B * B := by rw [h_d_Pp, h_B_Pp, zero_add, mul_add]
    _ = B * d := by rw [hB, add_zero]

lemma reflection_swaps_generators {d B : A}
    (hd : d * d = 0) (h_BdB : B * d * B = B) :
    (d + B) * d * (d + B) = B := by
  have h_Pm_d : (B * d) * d = 0 := by rw [mul_assoc, hd, mul_zero]
  calc (d + B) * d * (d + B)
    _ = (d * d + B * d) * (d + B) := by noncomm_ring
    _ = (B * d) * d + (B * d * B) := by rw [hd, zero_add, mul_add]
    _ = B := by rw [h_Pm_d, h_BdB, zero_add]

lemma active_grading_cube {d B : A}
    (hd : d * d = 0) (hB : B * B = 0)
    (h_dBd : d * B * d = d) (h_BdB : B * d * B = B) :
    (d * B - B * d) * (d * B - B * d) * (d * B - B * d) = d * B - B * d := by
  rw [active_grading_sq hd hB h_dBd h_BdB]
  rw [add_mul, mul_sub, mul_sub, active_pos_idempotent h_dBd,
      active_pos_mul_neg hB, active_neg_mul_pos hd, active_neg_idempotent h_BdB]
  abel

lemma active_grading_preserves_positive_support {d B : A}
    (hd : d * d = 0) (hB : B * B = 0) (h_dBd : d * B * d = d) :
    (d * B - B * d) * (d * B) * (d * B - B * d) = d * B := by
  rw [sub_mul, active_pos_idempotent h_dBd, active_neg_mul_pos hd, sub_zero,
      mul_sub, active_pos_idempotent h_dBd, active_pos_mul_neg hB, sub_zero]

lemma active_grading_preserves_negative_support {d B : A}
    (hd : d * d = 0) (hB : B * B = 0) (h_BdB : B * d * B = B) :
    (d * B - B * d) * (B * d) * (d * B - B * d) = B * d := by
  rw [sub_mul, active_pos_mul_neg hB, active_neg_idempotent h_BdB, zero_sub,
      neg_mul, mul_sub, active_neg_mul_pos hd, active_neg_idempotent h_BdB, zero_sub, neg_neg]

/-- Active-support polynomial identities and support exchange for a square-zero
reflexive pair. These do not assert Spin/Pin membership or topological orientability. -/
theorem cyclotomic_and_orientability_master {d B : A}
    (hd : d * d = 0) (hB : B * B = 0)
    (h_dBd : d * B * d = d) (h_BdB : B * d * B = B) :
    let P_pos := d * B
    let P_neg := B * d
    let Δ := P_pos + P_neg
    let Γ := P_pos - P_neg
    let Q₁ := d + B
    let J₄ := cyclotomic4Op d B
    let ω₃ := cyclotomic3Op d B
    let η₆ := cyclotomic6Op d B
    (Γ * Γ - Δ = 0 ∧
     J₄ * J₄ + Δ = 0 ∧ J₄ ^ 4 = Δ ∧
     ω₃ * ω₃ + ω₃ + Δ = 0 ∧ ω₃ ^ 3 = Δ ∧
     η₆ * η₆ - η₆ + Δ = 0 ∧ η₆ ^ 3 = -Δ ∧ η₆ ^ 6 = Δ) ∧
    (Q₁ * Γ * Q₁ = -Γ ∧
     Q₁ * P_pos * Q₁ = P_neg ∧
     Q₁ * d * Q₁ = B) ∧
    (Γ * Γ * Γ = Γ ∧
     Γ * P_pos * Γ = P_pos ∧
     Γ * P_neg * Γ = P_neg) :=
  ⟨⟨active_grading_sq_sub_support hd hB h_dBd h_BdB,
    cyclotomic4Op_sq_add_support hd hB,
    cyclotomic4Op_pow_four hd hB h_dBd h_BdB,
    cyclotomic3Op_quad_add_support hd hB h_dBd h_BdB,
    cyclotomic3Op_pow_three hd hB h_dBd h_BdB,
    cyclotomic6Op_quad_sub_support hd hB h_dBd h_BdB,
    cyclotomic6Op_pow_three hd hB h_dBd h_BdB,
    cyclotomic6Op_pow_six hd hB h_dBd h_BdB⟩,
   ⟨reflection_conjugates_grading hd hB h_dBd h_BdB,
    reflection_swaps_positive_support hd hB h_BdB,
    reflection_swaps_generators hd h_BdB⟩,
   ⟨active_grading_cube hd hB h_dBd h_BdB,
    active_grading_preserves_positive_support hd hB h_dBd,
    active_grading_preserves_negative_support hd hB h_BdB⟩⟩

/-! ## Unit orbits and their exact fibers -/

/-- Conjugation by an actual two-sided unit. -/
def unitOrbitMap (P : A) (g : Aˣ) : A :=
  homogeneousProj (g : A) (↑(g⁻¹) : A) P

/-- The quotient identifies exactly equal orbit points. -/
def unitOrbitSetoid (P : A) : Setoid Aˣ := Setoid.ker (unitOrbitMap P)

/-- Set-theoretic orbit quotient, not a locally trivial topological bundle. -/
noncomputable def unitOrbitQuotientEquiv (P : A) :
    Quotient (unitOrbitSetoid P) ≃ Set.range (unitOrbitMap P) :=
  Setoid.quotientKerEquivRange (unitOrbitMap P)

theorem unitOrbitMap_idempotent {P : A} (hP : IsIdempotentElem P) (g : Aˣ) :
    IsIdempotentElem (unitOrbitMap P g) :=
  isIdempotentElem_homogeneousProj hP (Units.inv_mul g)

/-- Stabilizing the orbit point is exactly commuting with the idempotent. -/
theorem unitOrbitMap_eq_self_iff (P : A) (g : Aˣ) :
    unitOrbitMap P g = P ↔ (g : A) * P = P * g := by
  unfold unitOrbitMap homogeneousProj
  constructor
  · intro h
    have hh := congrArg (fun x : A => x * g) h
    simpa only [mul_assoc, Units.inv_mul, mul_one] using hh
  · intro h
    rw [h, mul_assoc, Units.mul_inv, mul_one]

/-- Two points have the same image exactly when their relative unit stabilizes P. -/
theorem unitOrbitMap_fiber_iff (P : A) (g h : Aˣ) :
    unitOrbitMap P g = unitOrbitMap P h ↔
      unitOrbitMap P (h⁻¹ * g) = P := by
  unfold unitOrbitMap homogeneousProj
  simp only [Units.val_mul, mul_inv_rev, inv_inv]
  constructor
  · intro he
    have hh := congrArg (fun x : A => (↑(h⁻¹) : A) * x * h) he
    simpa only [mul_assoc, Units.inv_mul, Units.inv_mul_cancel_left, one_mul, mul_one] using hh
  · intro he
    have hh := congrArg (fun x : A => (h : A) * x * ↑(h⁻¹)) he
    simpa only [mul_assoc, Units.mul_inv_cancel_left, Units.mul_inv, mul_one] using hh

/-! ## Characterization of the normal Peirce summand -/

theorem normalBundlePart_commutes {P : A} (hP : IsIdempotentElem P) (X : A) :
    P * normalBundlePart P X = normalBundlePart P X * P :=
  sub_eq_zero.mp (lieBracket_normalBundlePart_eq_zero hP X)

theorem normalBundlePart_eq_self_iff {P : A} (hP : IsIdempotentElem P) (X : A) :
    normalBundlePart P X = X ↔ P * X = X * P := by
  constructor
  · intro h
    simpa only [h] using normalBundlePart_commutes hP X
  · intro h
    have hd : tangentNilpotent P X = 0 := by
      unfold tangentNilpotent
      rw [mul_assoc, ← h, sub_mul, one_mul, ← mul_assoc, hP.eq, sub_self]
    have hB : cotangentNilpotent P X = 0 := by
      unfold cotangentNilpotent
      rw [h, mul_assoc, mul_sub, mul_one, hP.eq, sub_self, mul_zero]
    simpa only [hd, hB, add_zero] using normal_tangent_cotangent_decomp P X

theorem normalBundlePart_idempotent {P : A} (hP : IsIdempotentElem P) (X : A) :
    normalBundlePart P (normalBundlePart P X) = normalBundlePart P X :=
  (normalBundlePart_eq_self_iff hP _).2 (normalBundlePart_commutes hP X)

/-! ## Active support and ambient reflection unit -/

/-- The active support acts as a two-sided identity on both generators. -/
theorem active_support_absorbs {d B : A}
    (hd : d * d = 0) (hB : B * B = 0)
    (hdBd : d * B * d = d) (hBdB : B * d * B = B) :
    (d * B + B * d) * d = d ∧ d * (d * B + B * d) = d ∧
    (d * B + B * d) * B = B ∧ B * (d * B + B * d) = B := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [add_mul, hdBd, mul_assoc B d d, hd, mul_zero, add_zero]
  · rw [mul_add, ← mul_assoc d d B, hd, zero_mul, ← mul_assoc, hdBd, zero_add]
  · rw [add_mul, mul_assoc d B B, hB, mul_zero, hBdB, zero_add]
  · rw [mul_add, ← mul_assoc B d B, hBdB, ← mul_assoc B B d, hB, zero_mul, add_zero]

theorem active_support_idempotent {d B : A}
    (hd : d * d = 0) (hB : B * B = 0)
    (hdBd : d * B * d = d) (hBdB : B * d * B = B) :
    IsIdempotentElem (d * B + B * d) := by
  obtain ⟨hdL, _, hBL, _⟩ := active_support_absorbs hd hB hdBd hBdB
  change (d * B + B * d) * (d * B + B * d) = _
  rw [mul_add, ← mul_assoc, hdL, ← mul_assoc, hBL]

/-- Extending the corner reflection by the complementary identity yields an
actual involution in the ambient ring, even when the active support is not 1. -/
theorem ambient_reflection_square {d B : A}
    (hd : d * d = 0) (hB : B * B = 0)
    (hdBd : d * B * d = d) (hBdB : B * d * B = B) :
    (d + B + (1 - (d * B + B * d))) *
      (d + B + (1 - (d * B + B * d))) = 1 := by
  let S := d * B + B * d
  let Q := d + B
  have hS : S * S = S := (active_support_idempotent hd hB hdBd hBdB).eq
  obtain ⟨hdL, hdR, hBL, hBR⟩ := active_support_absorbs hd hB hdBd hBdB
  have hSQ : S * Q = Q := by dsimp [S, Q]; rw [mul_add, hdL, hBL]
  have hQS : Q * S = Q := by dsimp [S, Q]; rw [add_mul, hdR, hBR]
  have hQ : Q * Q = S := by
    dsimp [Q, S]
    rw [add_mul, mul_add, mul_add, hd, hB, zero_add, add_zero]
  change (Q + (1 - S)) * (Q + (1 - S)) = 1
  noncomm_ring [hS, hSQ, hQS, hQ]

/-- A concrete ambient unit, not merely a formal inverse symbol. -/
def ambientReflectionUnit {d B : A}
    (hd : d * d = 0) (hB : B * B = 0)
    (hdBd : d * B * d = d) (hBdB : B * d * B = B) : Aˣ where
  val := d + B + (1 - (d * B + B * d))
  inv := d + B + (1 - (d * B + B * d))
  val_inv := ambient_reflection_square hd hB hdBd hBdB
  inv_val := ambient_reflection_square hd hB hdBd hBdB

/-- Phi_2(t)=t+1 has this residual in the active corner. Involutivity alone
therefore does not establish the second cyclotomic equation. -/
theorem phi2_active_residual (d B : A) :
    (d * B - B * d) + (d * B + B * d) = 2 • (d * B) := by
  rw [two_nsmul]
  abel

/-- Exact criterion for the degree-one Phi_2 equation, including characteristic two. -/
theorem phi2_active_eq_zero_iff (d B : A) :
    (d * B - B * d) + (d * B + B * d) = 0 ↔ 2 • (d * B) = 0 := by
  rw [phi2_active_residual]

end AbstractOperatorBundle

/-!
## 5. Noncommutative Matrix Operator Realization (`Matrix (Fin 2) (Fin 2) ℤ`)

We exhibit concrete non-commuting square-zero reflexive matrices `matD, matB : Matrix (Fin 2) (Fin 2) ℤ`
whose commutator `[matB, matD]` is non-zero. The witness realizes the stated
algebraic identities over `ℤ`, not principal bundles or Spin/Pin geometry.
-/

section NoncommutativeMatrixRealization

open Matrix

abbrev Mat2Z := Matrix (Fin 2) (Fin 2) ℤ

/-- Reference Grassmannian idempotent `P₀ = E₁₁` in `Matrix (Fin 2) (Fin 2) ℤ`. -/
def matP0 : Mat2Z := !![0, 0; 0, 1]

/-- Off-diagonal tangent nilpotent `d = E₀₁` (`d^2 = 0`, `d = (1 - P₀) d P₀`). -/
def matD : Mat2Z := !![0, 1; 0, 0]

/-- Off-diagonal cotangent nilpotent `B = E₁₀` (`B^2 = 0`, `B = P₀ B (1 - P₀)`). -/
def matB : Mat2Z := !![0, 0; 1, 0]

/-- Non-commuting shear matrix `g = I + E₀₁`, with inverse `matGInv`. -/
def matG : Mat2Z := !![1, 1; 0, 1]

/-- Inverse `g⁻¹ = I - E₀₁` of `matG` in `GL₂(ℤ)`. -/
def matGInv : Mat2Z := !![1, -1; 0, 1]

/-- Non-trivial isotropy stabilizer element `k = diag(-1, 1)` (`k * P₀ = P₀ * k`, `k² = I`). -/
def matK : Mat2Z := !![-1, 0; 0, 1]

/-- Both inverse equations are explicit, rather than inferred from a name. -/
theorem matG_inverse_laws :
    matG * matGInv = (1 : Mat2Z) ∧ matGInv * matG = (1 : Mat2Z) := by
  decide

/-- The shear as an actual element of the group of units. -/
def matGUnit : Mat2Zˣ where
  val := matG
  inv := matGInv
  val_inv := matG_inverse_laws.1
  inv_val := matG_inverse_laws.2

/-- The stabilizer is an involution and commutes with the reference idempotent. -/
theorem matK_stabilizer_laws :
    matK * matK = (1 : Mat2Z) ∧ matK * matP0 = matP0 * matK := by
  decide

def matKUnit : Mat2Zˣ where
  val := matK
  inv := matK
  val_inv := matK_stabilizer_laws.1
  inv_val := matK_stabilizer_laws.1

/-- The concrete stabilizer inhabits the previously constructed unit orbit fiber. -/
theorem matKUnit_fixes_reference : unitOrbitMap matP0 matKUnit = matP0 :=
  (unitOrbitMap_eq_self_iff matP0 matKUnit).2 matK_stabilizer_laws.2

/-- The old unbundled matrix formula is exactly the genuine unit action. -/
theorem matGUnit_orbit_readout :
    unitOrbitMap matP0 matGUnit = homogeneousProj matG matGInv matP0 := rfl

/-- Noncommuting square-zero reflexive matrices, a nontrivial conjugated
idempotent, stabilizer invariance, the Φ₃/Φ₄/Φ₆ equations and grading reversal.
The displayed conjunction is algebraic; it does not assert the Φ₂ equation. -/
theorem mat2Z_noncommutative_cyclotomic_witness :
    matD * matB ≠ matB * matD ∧
    matG * matP0 ≠ matP0 * matG ∧
    IsIdempotentElem matP0 ∧
    IsIdempotentElem (homogeneousProj matG matGInv matP0) ∧
    homogeneousProj (matG * matK) (matK * matGInv) matP0 = homogeneousProj matG matGInv matP0 ∧
    matD * matD = 0 ∧ matB * matB = 0 ∧
    matD * matB * matD = matD ∧ matB * matD * matB = matB ∧
    matD * matB + matB * matD = (1 : Mat2Z) ∧
    (cyclotomic3Op matD matB) ^ 2 + cyclotomic3Op matD matB + 1 = 0 ∧
    (cyclotomic4Op matD matB) ^ 2 + 1 = 0 ∧
    (cyclotomic6Op matD matB) ^ 2 - cyclotomic6Op matD matB + 1 = 0 ∧
    (matD + matB) * (matD * matB - matB * matD) * (matD + matB) = -(matD * matB - matB * matD) := by
  refine ⟨by decide, by decide,
          by change matP0 * matP0 = matP0; decide,
          by change (homogeneousProj matG matGInv matP0) * (homogeneousProj matG matGInv matP0) =
               homogeneousProj matG matGInv matP0; decide,
          by decide, by decide, by decide, by decide, by decide, by decide,
          by decide, by decide, by decide, by decide⟩

/-- Specialization of `adjoint_coadjoint_cubic_law` to `Matrix.trace` on `Matrix (Fin n) (Fin n) R`
    for any commutative ring `R`, proving coadjoint trace equivariance and the cubic law of `ad_P`
    on `n × n` matrices. -/
theorem matrix_trace_coadjoint_and_cubic_law
    {n : Type*} [Fintype n] [DecidableEq n]
    {R : Type*} [CommRing R]
    {P : Matrix n n R} (hP : IsIdempotentElem P)
    (L ξ X Y : Matrix n n R) :
    (Matrix.trace (ξ * lieBracket L X) + Matrix.trace (lieBracket L ξ * X) = 0) ∧
    (lieBracket P (lieBracket P (lieBracket P X)) = lieBracket P X ∧
     lieBracket P (normalBundlePart P X) = 0 ∧
     lieBracket P (tangentNilpotent P X) = -tangentNilpotent P X ∧
     lieBracket P (cotangentNilpotent P Y) = cotangentNilpotent P Y) := by
  let τ : Matrix n n R →+ R := (Matrix.traceLinearMap n R R).toAddMonoidHom
  exact adjoint_coadjoint_cubic_law (τ := τ) (fun U V => Matrix.trace_mul_comm U V) hP L ξ X Y

/-- Kernel-checked counterexample to confusing t²-1 with Phi_2(t)=t+1. -/
theorem mat2Z_involution_not_phi2 :
    let Γ := matD * matB - matB * matD
    Γ * Γ = (1 : Mat2Z) ∧ Γ + 1 ≠ 0 := by
  decide

/-- A fixed zero idempotent cannot generate all idempotents by unit conjugation. -/
theorem mat2Z_zero_orbit_not_all_idempotents :
    IsIdempotentElem (1 : Mat2Z) ∧
      (1 : Mat2Z) ∉ Set.range (unitOrbitMap (0 : Mat2Z)) := by
  constructor
  · change (1 : Mat2Z) * 1 = 1
    exact one_mul 1
  · rintro ⟨g, hg⟩
    simp [unitOrbitMap, homogeneousProj] at hg

end NoncommutativeMatrixRealization

/-!
## 6. Lean 4 Meta Epistemic Compiler Schedule & Certified Archetype Registration

We register and audit the 5 causal archetypes of this module in the Lean 4 Meta
Epistemic Compiler (`InfoGeometry.MetaCompiler.TypedArchetype`, `#register_archetype`,
`#audit_archetype`, and `InfoGeometry.MetaCompiler.executable_certified_compilation`).
-/

section MetaEpistemicCompilerCertification

open InfoGeometry.MetaCompiler
open InfoGeometry.Causal.FiniteDependencySchedule
open InfoGeometry.Causal.FiniteDependencyCompiler
open InfoGeometry.Causal.ProofCarryingSchedule

/-- Causal poset of the 5 mathematical archetypes in Stream 1. -/
inductive GrassmannianCyclotomicArchetype where
  | homogeneousBundleOrbit
  | peirceNilpotentTangentSplit
  | adjointCoadjointCubicLaw
  | cyclotomicActiveSupport
  | diracOrientabilityReversal
  deriving DecidableEq, Repr, Inhabited

namespace GrassmannianCyclotomicArchetype

private def equivFin : GrassmannianCyclotomicArchetype ≃ Fin 5 where
  toFun
    | .homogeneousBundleOrbit => 0
    | .peirceNilpotentTangentSplit => 1
    | .adjointCoadjointCubicLaw => 2
    | .cyclotomicActiveSupport => 3
    | .diracOrientabilityReversal => 4
  invFun
    | 0 => .homogeneousBundleOrbit
    | 1 => .peirceNilpotentTangentSplit
    | 2 => .adjointCoadjointCubicLaw
    | 3 => .cyclotomicActiveSupport
    | _ => .diracOrientabilityReversal
  left_inv x := by cases x <;> rfl
  right_inv i := by fin_cases i <;> rfl

instance instFintype : Fintype GrassmannianCyclotomicArchetype :=
  Fintype.ofEquiv (Fin 5) equivFin.symm

def prerequisites : GrassmannianCyclotomicArchetype → Finset GrassmannianCyclotomicArchetype
  | .homogeneousBundleOrbit => {.homogeneousBundleOrbit}
  | .peirceNilpotentTangentSplit =>
      {.homogeneousBundleOrbit, .peirceNilpotentTangentSplit}
  | .adjointCoadjointCubicLaw =>
      {.homogeneousBundleOrbit, .peirceNilpotentTangentSplit, .adjointCoadjointCubicLaw}
  | .cyclotomicActiveSupport =>
      {.homogeneousBundleOrbit, .peirceNilpotentTangentSplit, .cyclotomicActiveSupport}
  | .diracOrientabilityReversal =>
      {.homogeneousBundleOrbit, .peirceNilpotentTangentSplit,
       .adjointCoadjointCubicLaw, .cyclotomicActiveSupport, .diracOrientabilityReversal}

instance instPartialOrder : PartialOrder GrassmannianCyclotomicArchetype where
  le a b := prerequisites a ⊆ prerequisites b
  le_refl _ := Finset.Subset.refl _
  le_trans _ _ _ := Finset.Subset.trans
  le_antisymm := by
    intro a b
    cases a <;> cases b <;> decide

instance instDecidableLE : DecidableLE GrassmannianCyclotomicArchetype := fun a b =>
  inferInstanceAs (Decidable (prerequisites a ⊆ prerequisites b))

instance instDecidableLT : DecidableLT GrassmannianCyclotomicArchetype := fun a b =>
  decidable_of_iff (a ≤ b ∧ ¬ b ≤ a) lt_iff_le_not_ge.symm

def canonicalPending : List GrassmannianCyclotomicArchetype :=
  [.diracOrientabilityReversal, .cyclotomicActiveSupport,
   .adjointCoadjointCubicLaw, .peirceNilpotentTangentSplit, .homogeneousBundleOrbit]

def canonicalSchedule : List GrassmannianCyclotomicArchetype :=
  [.homogeneousBundleOrbit, .peirceNilpotentTangentSplit,
   .cyclotomicActiveSupport, .adjointCoadjointCubicLaw, .diracOrientabilityReversal]

theorem canonicalPending_nodup : canonicalPending.Nodup := by decide

theorem canonicalPending_univ : canonicalPending.toFinset = Finset.univ := by decide

theorem compile_canonicalPending :
    compile (∅ : Finset GrassmannianCyclotomicArchetype) canonicalPending =
      some canonicalSchedule := by
  decide

end GrassmannianCyclotomicArchetype

/-- Proved `TypedArchetype` for Archetype 1: Homogeneous Conjugation Orbit & Stabilizer. -/
def arch1HomogeneousBundleOrbit : TypedArchetype Mat2Zˣ .proved where
  name := `InfoGeometry.Canonical.GrassmannianBundleCyclotomicOrientability.arch1HomogeneousBundleOrbit
  phase := Phase.kernelCertifiedPromotion.toNat
  claim := fun g =>
    IsIdempotentElem (unitOrbitMap matP0 g) ∧
    unitOrbitMap matP0 (g * matKUnit) = unitOrbitMap matP0 g
  evidence := fun g =>
    ⟨unitOrbitMap_idempotent mat2Z_noncommutative_cyclotomic_witness.2.2.1 g,
     homogeneousProj_right_gauge_invariant matK_stabilizer_laws.1 matK_stabilizer_laws.2⟩

/-- Proved `TypedArchetype` for Archetype 2: Peirce Normal/Tangent/Cotangent Nilpotent Split. -/
def arch2PeirceNilpotentTangentSplit : TypedArchetype Mat2Z .proved where
  name := `InfoGeometry.Canonical.GrassmannianBundleCyclotomicOrientability.arch2PeirceNilpotentTangentSplit
  phase := Phase.kernelCertifiedPromotion.toNat
  claim := fun X =>
    normalBundlePart matP0 X + tangentNilpotent matP0 X + cotangentNilpotent matP0 X = X ∧
    tangentNilpotent matP0 X * tangentNilpotent matP0 X = 0 ∧
    cotangentNilpotent matP0 X * cotangentNilpotent matP0 X = 0
  evidence := fun X =>
    ⟨normal_tangent_cotangent_decomp matP0 X,
     tangentNilpotent_sq_zero mat2Z_noncommutative_cyclotomic_witness.2.2.1 X,
     cotangentNilpotent_sq_zero mat2Z_noncommutative_cyclotomic_witness.2.2.1 X⟩

/-- Proved `TypedArchetype` for Archetype 3: Tracial Coadjoint Pairing & Cubic `ad_P³ = ad_P`. -/
def arch3AdjointCoadjointCubicLaw : TypedArchetype Mat2Z .proved where
  name := `InfoGeometry.Canonical.GrassmannianBundleCyclotomicOrientability.arch3AdjointCoadjointCubicLaw
  phase := Phase.kernelCertifiedPromotion.toNat
  claim := fun X =>
    lieBracket matP0 (lieBracket matP0 (lieBracket matP0 X)) = lieBracket matP0 X ∧
    lieBracket matP0 (normalBundlePart matP0 X) = 0
  evidence := fun X =>
    ⟨adjoint_idempotent_cubic mat2Z_noncommutative_cyclotomic_witness.2.2.1 X,
     lieBracket_normalBundlePart_eq_zero mat2Z_noncommutative_cyclotomic_witness.2.2.1 X⟩

/-- Proved `TypedArchetype` for Archetype 4: Active-Support `Φ₃/Φ₄/Φ₆` Operator Laws. -/
def arch4CyclotomicActiveSupport : TypedArchetype Unit .proved where
  name := `InfoGeometry.Canonical.GrassmannianBundleCyclotomicOrientability.arch4CyclotomicActiveSupport
  phase := Phase.kernelCertifiedPromotion.toNat
  claim := fun _ =>
    (cyclotomic3Op matD matB) ^ 2 + cyclotomic3Op matD matB + 1 = 0 ∧
    (cyclotomic4Op matD matB) ^ 2 + 1 = 0 ∧
    (cyclotomic6Op matD matB) ^ 2 - cyclotomic6Op matD matB + 1 = 0
  evidence := fun _ =>
    ⟨mat2Z_noncommutative_cyclotomic_witness.2.2.2.2.2.2.2.2.2.2.1,
     mat2Z_noncommutative_cyclotomic_witness.2.2.2.2.2.2.2.2.2.2.2.1,
     mat2Z_noncommutative_cyclotomic_witness.2.2.2.2.2.2.2.2.2.2.2.2.1⟩

/-- Proved `TypedArchetype` for Archetype 5: Odd Reflection Grading Reversal & Support Exchange. -/
def arch5DiracOrientabilityReversal : TypedArchetype Unit .proved where
  name := `InfoGeometry.Canonical.GrassmannianBundleCyclotomicOrientability.arch5DiracOrientabilityReversal
  phase := Phase.kernelCertifiedPromotion.toNat
  claim := fun _ =>
    (matD + matB) * (matD * matB - matB * matD) * (matD + matB) = -(matD * matB - matB * matD) ∧
    (matD + matB) * (matD * matB) * (matD + matB) = matB * matD
  evidence := fun _ =>
    ⟨mat2Z_noncommutative_cyclotomic_witness.2.2.2.2.2.2.2.2.2.2.2.2.2,
     reflection_swaps_positive_support
       mat2Z_noncommutative_cyclotomic_witness.2.2.2.2.2.1
       mat2Z_noncommutative_cyclotomic_witness.2.2.2.2.2.2.1
       mat2Z_noncommutative_cyclotomic_witness.2.2.2.2.2.2.2.2.1⟩

#register_archetype arch1HomogeneousBundleOrbit
#register_archetype arch2PeirceNilpotentTangentSplit
#register_archetype arch3AdjointCoadjointCubicLaw
#register_archetype arch4CyclotomicActiveSupport
#register_archetype arch5DiracOrientabilityReversal

#audit_archetype arch1HomogeneousBundleOrbit
#audit_archetype arch2PeirceNilpotentTangentSplit
#audit_archetype arch3AdjointCoadjointCubicLaw
#audit_archetype arch4CyclotomicActiveSupport
#audit_archetype arch5DiracOrientabilityReversal

/-- Target statement map on `GrassmannianCyclotomicArchetype` discharged via `TypedArchetype.discharge`. -/
def grassmannianArchetypeStatement : GrassmannianCyclotomicArchetype → Prop
  | .homogeneousBundleOrbit => ∀ g : Mat2Zˣ, arch1HomogeneousBundleOrbit.claim g
  | .peirceNilpotentTangentSplit => ∀ X : Mat2Z, arch2PeirceNilpotentTangentSplit.claim X
  | .adjointCoadjointCubicLaw => ∀ X : Mat2Z, arch3AdjointCoadjointCubicLaw.claim X
  | .cyclotomicActiveSupport => arch4CyclotomicActiveSupport.claim ()
  | .diracOrientabilityReversal => arch5DiracOrientabilityReversal.claim ()

lemma grassmannianArchetypeRules : ProofRules grassmannianArchetypeStatement := by
  intro target _
  cases target with
  | homogeneousBundleOrbit => exact fun g => arch1HomogeneousBundleOrbit.discharge g
  | peirceNilpotentTangentSplit => exact fun X => arch2PeirceNilpotentTangentSplit.discharge X
  | adjointCoadjointCubicLaw => exact fun X => arch3AdjointCoadjointCubicLaw.discharge X
  | cyclotomicActiveSupport => exact arch4CyclotomicActiveSupport.discharge ()
  | diracOrientabilityReversal => exact arch5DiracOrientabilityReversal.discharge ()

/-- Certified execution of the Meta Epistemic Compiler on the `GrassmannianCyclotomicArchetype` causal poset. -/
theorem grassmannian_cyclotomic_executable_certified_compilation :
    ∃ schedule : List GrassmannianCyclotomicArchetype,
      compile ∅ GrassmannianCyclotomicArchetype.canonicalPending = some schedule ∧
      ValidSchedule ∅ schedule ∧
      schedule.Pairwise (fun earlier later => ¬ later ≤ earlier) ∧
      schedule.Nodup ∧
      schedule.length = Fintype.card GrassmannianCyclotomicArchetype ∧
      schedule.toFinset = Finset.univ ∧
      ∀ target, grassmannianArchetypeStatement target :=
  executable_certified_compilation
    grassmannianArchetypeStatement
    grassmannianArchetypeRules
    GrassmannianCyclotomicArchetype.canonicalPending
    GrassmannianCyclotomicArchetype.canonicalPending_nodup
    GrassmannianCyclotomicArchetype.canonicalPending_univ

end MetaEpistemicCompilerCertification

end InfoGeometry.Canonical.GrassmannianBundleCyclotomicOrientability
