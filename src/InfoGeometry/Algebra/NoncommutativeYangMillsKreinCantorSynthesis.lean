/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/

import InfoGeometry.Algebra.NoncommutativeCliffordPrimitives
import InfoGeometry.Algebra.NoncommutativeCovariantDiracZornSynthesis
import InfoGeometry.Algebra.TwoSheetDiracMassEntropy
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.Tactic

/-!
# Noncommutative Krein–Zorn Gauge Algebra and Positive-Sector Projections

Finite-stage algebraic identities over an associative star ring `B`.
This module separates what is algebraically proved from analytic/measure-theoretic
continuum claims:
- `KC₁` (`kreinAdjoint_involution_and_antimul`): `kreinAdjoint` on `ClTower B n`
  is defined via `kroneckerGamma γ₀ n` and proved to be an anti-multiplicative
  involutive ring star.
- `KC₂` (`zorn_vecOp_krein_signature_and_twisted_positivity`): on `M₂(B)`,
  `vecOp u₁ u₂ u₃` has split-Lorentzian Krein trace
  `2 • (star u₁ * u₁ - star u₂ * u₂ - star u₃ * u₃)`, whereas the Krein-twisted
  Hilbert-Schmidt trace `Tr₂((Γ₁ V)ᴴ (Γ₁ V))` yields
  `2 • (star u₁ * u₁ + star u₂ * u₂ + star u₃ * u₃)`.
- `KC₃` (`positive_sector_ghost_excision`): on any self-adjoint projection `P` in
  the `+1`-eigenspace of `kroneckerGamma γ₀ n` (`Γₙ * P = P`), the Krein pairing
  `star (P * X) * Γₙ * (P * Y)` equals the Hilbert pairing `star (P * X) * (P * Y)`,
  and the Krein adjoint on compressed operators `P * X * P` equals `star (P * X * P)`.
- `KC₄` (`kreinDirac_wick_rotation_and_subspace_coincidence`): `kreinDiracOp Dp Dm U`
  is Krein-self-adjoint, its algebraic Wick rotation `gamma1Op * kreinDiracOp Dp Dm U`
  is Hilbert-self-adjoint, and both coincide on any `+1`-sector projection `P`
  (`Γ₁ * P = P`).
- `KC₅` (`diagEmbed_kreinAdjoint_and_trace_bott_scaling`): `diagEmbed` commutes
  with `kreinAdjoint` and scales the Krein trace pairing by `2 •`, while
  `positiveSectorProj` maintains `+1`-sector self-adjoint projections at all depths.
-/

open Matrix
open InfoGeometry.Algebra.NoncommutativeCliffordPrimitives
open InfoGeometry.Algebra.NoncommutativeCovariantDiracZornSynthesis
open InfoGeometry.Algebra.TwoSheetDiracMassEntropy

namespace InfoGeometry.Algebra.NoncommutativeYangMillsKreinCantorSynthesis

universe u

section ScaleKreinAdjoint

variable {B : Type u} [Ring B] [StarRing B]

/-- Scale-`n` Krein adjoint `X^[†] = Γ⁽ⁿ⁾ X⋆ Γ⁽ⁿ⁾` in `ClTower B n`. -/
def kreinAdjoint (γ₀ : B) (n : ℕ) (X : ClTower B n) : ClTower B n :=
  kroneckerGamma γ₀ n * star X * kroneckerGamma γ₀ n

lemma kroneckerGamma_star {γ₀ : B} (hγ₀_star : star γ₀ = γ₀) :
    ∀ (n : ℕ), star (kroneckerGamma γ₀ n) = kroneckerGamma γ₀ n
  | 0 => hγ₀_star
  | n + 1 => by
      apply ext_fin2
      · simp [kroneckerGamma, kroneckerGamma_star hγ₀_star n]
      · simp [kroneckerGamma]
      · simp [kroneckerGamma]
      · simp [kroneckerGamma, kroneckerGamma_star hγ₀_star n]

/-- `KC₁`: `kreinAdjoint` is an anti-multiplicative involutive star on `ClTower B n`. -/
theorem kreinAdjoint_involution_and_antimul
    {γ₀ : B} (hγ₀_sq : γ₀ * γ₀ = 1) (hγ₀_star : star γ₀ = γ₀)
    (n : ℕ) (X Y : ClTower B n) :
    kreinAdjoint γ₀ n (kreinAdjoint γ₀ n X) = X ∧
      kreinAdjoint γ₀ n (X + Y) = kreinAdjoint γ₀ n X + kreinAdjoint γ₀ n Y ∧
      kreinAdjoint γ₀ n (X * Y) = kreinAdjoint γ₀ n Y * kreinAdjoint γ₀ n X ∧
      kreinAdjoint γ₀ n (1 : ClTower B n) = 1 := by
  have hΓ_sq := kroneckerGamma_sq hγ₀_sq n
  have hΓ_star := kroneckerGamma_star hγ₀_star n
  refine ⟨?_, ?_, ?_, ?_⟩
  · dsimp [kreinAdjoint]
    rw [star_mul, star_mul, star_star, hΓ_star]
    simp only [mul_assoc]
    rw [hΓ_sq, mul_one]
    simp only [← mul_assoc]
    rw [hΓ_sq, one_mul]
  · dsimp [kreinAdjoint]
    rw [star_add, mul_add, add_mul]
  · dsimp [kreinAdjoint]
    rw [star_mul]
    calc
      kroneckerGamma γ₀ n * (star Y * star X) * kroneckerGamma γ₀ n
        = kroneckerGamma γ₀ n * star Y * 1 * star X * kroneckerGamma γ₀ n := by noncomm_ring
      _ = kroneckerGamma γ₀ n * star Y *
            (kroneckerGamma γ₀ n * kroneckerGamma γ₀ n) * star X *
            kroneckerGamma γ₀ n := by rw [hΓ_sq]
      _ = (kroneckerGamma γ₀ n * star Y * kroneckerGamma γ₀ n) *
            (kroneckerGamma γ₀ n * star X * kroneckerGamma γ₀ n) := by noncomm_ring
  · dsimp [kreinAdjoint]
    rw [star_one, mul_one, hΓ_sq]

end ScaleKreinAdjoint

section ZornSplitLorentzianVsTwisted

variable {B : Type u} [Ring B] [StarRing B]

/-- Base `M₂(B)` Krein adjoint `Γ₁ Xᴴ Γ₁`. -/
def mat2KreinAdjoint (X : Matrix (Fin 2) (Fin 2) B) : Matrix (Fin 2) (Fin 2) B :=
  gamma1Op * Xᴴ * gamma1Op

/-- `KC₂`: Split-Lorentzian Krein signature vs. Krein-twisted Hilbert-Schmidt positivity
for the Zorn 3-vector operator `vecOp u₁ u₂ u₃`. -/
theorem zorn_vecOp_krein_signature_and_twisted_positivity (u₁ u₂ u₃ : B) :
    let V : Matrix (Fin 2) (Fin 2) B := vecOp u₁ u₂ u₃
    mat2KreinAdjoint (gamma1Op : Matrix (Fin 2) (Fin 2) B) = gamma1Op ∧
      mat2KreinAdjoint (sigmaOp : Matrix (Fin 2) (Fin 2) B) = -sigmaOp ∧
      mat2KreinAdjoint (omegaOp : Matrix (Fin 2) (Fin 2) B) = omegaOp ∧
      mat2KreinAdjoint V =
        fiberEmbed (star u₁) * gamma1Op -
          fiberEmbed (star u₂) * sigmaOp +
          fiberEmbed (star u₃) * omegaOp ∧
      Matrix.trace (mat2KreinAdjoint V * V) =
        2 • (star u₁ * u₁ - star u₂ * u₂ - star u₃ * u₃) ∧
      Matrix.trace ((gamma1Op * V)ᴴ * (gamma1Op * V)) =
        2 • (star u₁ * u₁ + star u₂ * u₂ + star u₃ * u₃) := by
  intro V
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · apply ext_fin2 <;> simp [mat2KreinAdjoint, gamma1Op]
  · apply ext_fin2 <;> simp [mat2KreinAdjoint, gamma1Op, sigmaOp]
  · apply ext_fin2 <;> simp [mat2KreinAdjoint, gamma1Op, omegaOp]
  · apply ext_fin2 <;> simp [mat2KreinAdjoint, V, vecOp, fiberEmbed, gamma1Op, sigmaOp, omegaOp] <;> abel
  · simp [mat2KreinAdjoint, V, vecOp, fiberEmbed, gamma1Op, sigmaOp, omegaOp, two_smul]
    noncomm_ring
  · simp [V, vecOp, fiberEmbed, gamma1Op, sigmaOp, omegaOp, two_smul]
    noncomm_ring

end ZornSplitLorentzianVsTwisted

section PositiveSectorProjection

variable {B : Type u} [Ring B] [StarRing B]

/-- Top-sheet embedding `X ↦ diag(X, 0)` into `ClTower B (n + 1)`. -/
def topSheetEmbed {n : ℕ} (X : ClTower B n) : ClTower B (n + 1) :=
  mat2 X 0 0 0

/-- Canonical `+1`-sector projection tower built from a base projection `π₀`
satisfying `γ₀ * π₀ = π₀`. -/
def positiveSectorProj (π₀ : B) : ∀ (n : ℕ), ClTower B n
  | 0 => π₀
  | n + 1 => topSheetEmbed (positiveSectorProj π₀ n)

theorem positiveSectorProj_props
    {γ₀ π₀ : B} (hγ₀_star : star γ₀ = γ₀)
    (hπ_sq : π₀ * π₀ = π₀) (hπ_star : star π₀ = π₀) (hπ_pos : γ₀ * π₀ = π₀) :
    ∀ (n : ℕ),
      kroneckerGamma γ₀ n * positiveSectorProj π₀ n = positiveSectorProj π₀ n ∧
      positiveSectorProj π₀ n * positiveSectorProj π₀ n = positiveSectorProj π₀ n ∧
      star (positiveSectorProj π₀ n) = positiveSectorProj π₀ n
  | 0 => ⟨hπ_pos, hπ_sq, hπ_star⟩
  | n + 1 => by
      obtain ⟨ih_pos, ih_sq, ih_star⟩ := positiveSectorProj_props hγ₀_star hπ_sq hπ_star hπ_pos n
      refine ⟨?_, ?_, ?_⟩
      · apply ext_fin2 <;> simp [kroneckerGamma, positiveSectorProj, topSheetEmbed, ih_pos]
      · apply ext_fin2 <;> simp [positiveSectorProj, topSheetEmbed, ih_sq]
      · apply ext_fin2 <;> simp [positiveSectorProj, topSheetEmbed, ih_star]

/-- `KC₃`: On any self-adjoint projection `P` in the `+1`-eigenspace of `kroneckerGamma γ₀ n`,
the Krein adjoint on `P`-compressed operators equals the Hilbert star, and the Krein
pairing on `P`-projected states equals the Hilbert pairing. -/
theorem positive_sector_ghost_excision
    {γ₀ : B} (hγ₀_star : star γ₀ = γ₀)
    (n : ℕ) (P X Y : ClTower B n)
    (hP_star : star P = P)
    (hP_pos : kroneckerGamma γ₀ n * P = P) :
    P * kreinAdjoint γ₀ n X * P = P * star X * P ∧
      kreinAdjoint γ₀ n (P * X * P) = star (P * X * P) ∧
      star (P * X) * kroneckerGamma γ₀ n * (P * Y) = star (P * X) * (P * Y) ∧
      towerTrace (kreinAdjoint γ₀ n (P * X * P) * (P * Y * P)) =
        towerTrace (star (P * X * P) * (P * Y * P)) := by
  have hP_right : P * kroneckerGamma γ₀ n = P := by
    have h := congr_arg star hP_pos
    rwa [star_mul, hP_star, kroneckerGamma_star hγ₀_star n] at h
  have h_comp : P * kreinAdjoint γ₀ n X * P = P * star X * P := by
    dsimp [kreinAdjoint]
    calc
      P * (kroneckerGamma γ₀ n * star X * kroneckerGamma γ₀ n) * P
        = (P * kroneckerGamma γ₀ n) * star X * (kroneckerGamma γ₀ n * P) := by noncomm_ring
      _ = P * star X * P := by rw [hP_right, hP_pos]
  have h_adj : kreinAdjoint γ₀ n (P * X * P) = star (P * X * P) := by
    dsimp [kreinAdjoint]
    rw [star_mul, star_mul, hP_star]
    calc
      kroneckerGamma γ₀ n * (P * (star X * P)) * kroneckerGamma γ₀ n
        = (kroneckerGamma γ₀ n * P) * star X * (P * kroneckerGamma γ₀ n) := by noncomm_ring
      _ = P * (star X * P) := by rw [hP_pos, hP_right]; noncomm_ring
  refine ⟨h_comp, h_adj, ?_, ?_⟩
  · rw [star_mul, hP_star]
    calc
      star X * P * kroneckerGamma γ₀ n * (P * Y)
        = star X * (P * kroneckerGamma γ₀ n) * (P * Y) := by noncomm_ring
      _ = star X * P * (P * Y) := by rw [hP_right]
  · rw [h_adj]

end PositiveSectorProjection

section AlgebraicWickRotation

variable {B : Type u} [Ring B] [StarRing B]

/-- Two-sheeted Krein-self-adjoint Dirac operator `[[Dp, U], [-U⋆, Dm]]`. -/
def kreinDiracOp (Dp Dm U : B) : Matrix (Fin 2) (Fin 2) B :=
  mat2 Dp U (-star U) Dm

/-- `KC₄`: `kreinDiracOp Dp Dm U` is Krein-self-adjoint when `Dp, Dm` are self-adjoint;
its algebraic Wick rotation `Γ₁ * kreinDiracOp Dp Dm U` is Hilbert-self-adjoint; and both
coincide on any `+1`-eigenspace projection `P` of `Γ₁`. -/
theorem kreinDirac_wick_rotation_and_subspace_coincidence
    (Dp Dm U : B) (hDp : star Dp = Dp) (hDm : star Dm = Dm)
    (P : Matrix (Fin 2) (Fin 2) B)
    (hP_star : Pᴴ = P) (hP_pos : gamma1Op * P = P) :
    let D_K := kreinDiracOp Dp Dm U
    let D_E := gamma1Op * D_K
    mat2KreinAdjoint D_K = D_K ∧
      D_Eᴴ = D_E ∧
      D_Eᴴ * D_E = D_E * D_E ∧
      P * D_E = P * D_K ∧
      P * D_E * P = P * D_K * P := by
  intro D_K D_E
  have hP_right : P * gamma1Op = P := by
    have h := congr_arg conjTranspose hP_pos
    have hΓ : (gamma1Op : Matrix (Fin 2) (Fin 2) B)ᴴ = gamma1Op := by
      apply ext_fin2 <;> simp [gamma1Op]
    rwa [conjTranspose_mul, hP_star, hΓ] at h
  have h_left : P * D_E = P * D_K := by
    calc
      P * (gamma1Op * D_K) = (P * gamma1Op) * D_K := by rw [mul_assoc]
      _ = P * D_K := by rw [hP_right]
  refine ⟨?_, ?_, ?_, h_left, ?_⟩
  · apply ext_fin2 <;> simp [mat2KreinAdjoint, D_K, kreinDiracOp, gamma1Op, hDp, hDm]
  · apply ext_fin2 <;> simp [D_E, D_K, kreinDiracOp, gamma1Op, hDp, hDm]
  · have hE : D_Eᴴ = D_E := by
      apply ext_fin2 <;> simp [D_E, D_K, kreinDiracOp, gamma1Op, hDp, hDm]
    rw [hE]
  · rw [h_left]

end AlgebraicWickRotation

section BottTowerCompatibility

variable {B : Type u} [Ring B] [StarRing B]

/-- `KC₅`: `diagEmbed` commutes with `kreinAdjoint` and doubles the Krein trace pairing. -/
theorem diagEmbed_kreinAdjoint_and_trace_bott_scaling
    (γ₀ : B) (n : ℕ) (X Y : ClTower B n) :
    kreinAdjoint γ₀ (n + 1) (diagEmbed X) = diagEmbed (kreinAdjoint γ₀ n X) ∧
      towerTrace (n := n + 1) (kreinAdjoint γ₀ (n + 1) (diagEmbed X) * diagEmbed Y) =
        2 • towerTrace (n := n) (kreinAdjoint γ₀ n X * Y) := by
  have h_comm : kreinAdjoint γ₀ (n + 1) (diagEmbed X) = diagEmbed (kreinAdjoint γ₀ n X) := by
    apply ext_fin2 <;> simp [kreinAdjoint, kroneckerGamma, diagEmbed]
  refine ⟨h_comm, ?_⟩
  rw [h_comm]
  dsimp [diagEmbed, towerTrace]
  simp only [mul2_00, mul2_11, mat2_00, mat2_01, mat2_10, mat2_11,
    mul_zero, add_zero, zero_add]
  rw [two_smul]

end BottTowerCompatibility

end InfoGeometry.Algebra.NoncommutativeYangMillsKreinCantorSynthesis
