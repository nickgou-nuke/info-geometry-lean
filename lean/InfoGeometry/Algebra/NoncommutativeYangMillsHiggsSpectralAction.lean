/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/

import InfoGeometry.Algebra.NoncommutativeCliffordPrimitives
import InfoGeometry.Algebra.NoncommutativeCovariantDiracZornSynthesis
import InfoGeometry.Algebra.NoncommutativeInherentZornGaugeSynthesis
import InfoGeometry.Algebra.TwoSheetDiracMassEntropy
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.Algebra.Lie.OfAssociative
import Mathlib.Tactic

/-!
# Noncommutative Yang–Mills–Higgs Matrix Identities

Finite-stage algebraic identities over an associative star ring. The spectral
action is a B-valued matrix trace decomposition. No order structure is assumed,
so the sums of Hermitian squares are not promoted to an order-theoretic bound.
The BPS result below is a square-completion identity plus a conditional
Bianchi consequence, not an integrated monopole energy theorem. The non-central
Dirac–Higgs tower is reused from `TwoSheetDiracMassEntropy`.
-/

open Matrix
open InfoGeometry.Algebra.NoncommutativeCliffordPrimitives
open InfoGeometry.Algebra.NoncommutativeCovariantDiracZornSynthesis
open InfoGeometry.Algebra.NoncommutativeInherentZornGaugeSynthesis

namespace InfoGeometry.Algebra.NoncommutativeYangMillsHiggsSpectralAction

/-! ## SA₁: noncommutative four-channel Hilbert–Schmidt identity -/

theorem zorn_tetraktys_hilbert_schmidt_pythagoras
    {B : Type*} [Ring B] [StarRing B] (s v₁ v₂ v₃ : B) :
    Matrix.trace ((fiberEmbed s + vecOp v₁ v₂ v₃)ᴴ *
      (fiberEmbed s + vecOp v₁ v₂ v₃)) =
      2 • (star s * s + star v₁ * v₁ + star v₂ * v₂ + star v₃ * v₃) := by
  simp [fiberEmbed, vecOp, gamma1Op, sigmaOp, omegaOp, mat2, two_smul]
  noncomm_ring

/-! ## SA₂: quartic B-valued trace action in M₂(M₂(B)) -/

variable {B : Type*} [Ring B]

def trace4 (M : NestedMat B) : B := Matrix.trace (M 0 0) + Matrix.trace (M 1 1)

private lemma fieldStrength_as_covariant_commutator
    (dᵢ dⱼ Aᵢ Aⱼ : B) (h : ⁅dᵢ, dⱼ⁆ = 0) :
    ymFieldStrength dᵢ dⱼ Aᵢ Aⱼ = ⁅dᵢ + Aᵢ, dⱼ + Aⱼ⁆ := by
  rw [covariant_commutator_eq_background_add_ymFieldStrength, h, zero_add]

private lemma comm_fiberEmbed_vecOp (m D₁ D₂ D₃ : B) :
    ⁅fiberEmbed m, vecOp D₁ D₂ D₃⁆ =
      vecOp ⁅m, D₁⁆ ⁅m, D₂⁆ ⁅m, D₃⁆ := by
  simp only [Ring.lie_def]
  apply ext_fin2 <;> simp [fiberEmbed] <;> noncomm_ring

private lemma covariant_zorn_square
    (m d₁ d₂ d₃ A₁ A₂ A₃ : B)
    (h23 : ⁅d₂, d₃⁆ = 0) (h31 : ⁅d₃, d₁⁆ = 0) (h12 : ⁅d₁, d₂⁆ = 0) :
    let D₁ := d₁ + A₁
    let D₂ := d₂ + A₂
    let D₃ := d₃ + A₃
    let Δ := m * m + (D₁ * D₁ + D₂ * D₂ - D₃ * D₃)
    let F₂₃ := ymFieldStrength d₂ d₃ A₂ A₃
    let F₃₁ := ymFieldStrength d₃ d₁ A₃ A₁
    let F₁₂ := ymFieldStrength d₁ d₂ A₁ A₂
    (diracZornOp m (-m) D₁ D₂ D₃ D₁ D₂ D₃ : NestedMat B) ^ 2 =
      mat2 (fiberEmbed Δ + vecOp F₂₃ F₃₁ (-F₁₂))
        (vecOp ⁅m, D₁⁆ ⁅m, D₂⁆ ⁅m, D₃⁆)
        (-vecOp ⁅m, D₁⁆ ⁅m, D₂⁆ ⁅m, D₃⁆)
        (fiberEmbed Δ + vecOp F₂₃ F₃₁ (-F₁₂)) := by
  intro D₁ D₂ D₃ Δ F₂₃ F₃₁ F₁₂
  have hsq := (covariant_dirac_zorn_multiplication_and_pauli_square
    (α₁ := (0 : B)) (β₁ := 0) (u₁ := 0) (u₂ := 0) (u₃ := 0)
    (v₁ := 0) (v₂ := 0) (v₃ := 0) (α₂ := 0) (β₂ := 0)
    (x₁ := 0) (x₂ := 0) (x₃ := 0) (y₁ := 0) (y₂ := 0) (y₃ := 0)
    m D₁ D₂ D₃).2
  have hF23 := fieldStrength_as_covariant_commutator d₂ d₃ A₂ A₃ h23
  have hF31 := fieldStrength_as_covariant_commutator d₃ d₁ A₃ A₁ h31
  have hF12 := fieldStrength_as_covariant_commutator d₁ d₂ A₁ A₂ h12
  have hcomm := comm_fiberEmbed_vecOp m D₁ D₂ D₃
  rw [hcomm] at hsq
  rw [← hF23, ← hF31, ← hF12] at hsq
  simpa [pow_two, diracZornOp, D₁, D₂, D₃, Δ, fiberEmbed, vecOp,
    zornDot, zornCross1, zornCross2, zornCross3] using hsq

theorem unified_yang_mills_higgs_dirac_spectral_action [StarRing B]
    (m d₁ d₂ d₃ A₁ A₂ A₃ : B)
    (h23 : ⁅d₂, d₃⁆ = 0) (h31 : ⁅d₃, d₁⁆ = 0) (h12 : ⁅d₁, d₂⁆ = 0) :
    let D₁ := d₁ + A₁
    let D₂ := d₂ + A₂
    let D₃ := d₃ + A₃
    let Δ := m * m + (D₁ * D₁ + D₂ * D₂ - D₃ * D₃)
    let F₂₃ := ymFieldStrength d₂ d₃ A₂ A₃
    let F₃₁ := ymFieldStrength d₃ d₁ A₃ A₁
    let F₁₂ := ymFieldStrength d₁ d₂ A₁ A₂
    let D := (diracZornOp m (-m) D₁ D₂ D₃ D₁ D₂ D₃ : NestedMat B)
    trace4 ((D ^ 2)ᴴ * D ^ 2) =
      4 • (star Δ * Δ +
        (star F₂₃ * F₂₃ + star F₃₁ * F₃₁ + star F₁₂ * F₁₂) +
        (star ⁅m, D₁⁆ * ⁅m, D₁⁆ + star ⁅m, D₂⁆ * ⁅m, D₂⁆ +
          star ⁅m, D₃⁆ * ⁅m, D₃⁆)) := by
  intro D₁ D₂ D₃ Δ F₂₃ F₃₁ F₁₂ D
  rw [covariant_zorn_square m d₁ d₂ d₃ A₁ A₂ A₃ h23 h31 h12]
  dsimp [trace4]
  simp only [mul2_00, mul2_11, ct2_00, ct2_01, ct2_10, ct2_11,
    mat2_00, mat2_01, mat2_10, mat2_11, star_neg, neg_mul_neg]
  have hW := zorn_tetraktys_hilbert_schmidt_pythagoras Δ F₂₃ F₃₁ (-F₁₂)
  have hY := zorn_tetraktys_hilbert_schmidt_pythagoras (0 : B)
    ⁅m, D₁⁆ ⁅m, D₂⁆ ⁅m, D₃⁆
  have h0 : fiberEmbed (0 : B) + vecOp ⁅m, D₁⁆ ⁅m, D₂⁆ ⁅m, D₃⁆ =
      vecOp ⁅m, D₁⁆ ⁅m, D₂⁆ ⁅m, D₃⁆ := by
    apply ext_fin2 <;> simp [fiberEmbed]
  rw [h0] at hY
  have h_trace_add (X Y : Matrix (Fin 2) (Fin 2) B) :
      Matrix.trace (X + Y) = Matrix.trace X + Matrix.trace Y := by
    simp [Matrix.trace, Matrix.diag, Fin.sum_univ_two]
    abel
  rw [h_trace_add, h_trace_add]
  change Matrix.trace ((fiberEmbed Δ + vecOp F₂₃ F₃₁ (-F₁₂))ᴴ *
      (fiberEmbed Δ + vecOp F₂₃ F₃₁ (-F₁₂))) +
    Matrix.trace ((vecOp ⁅m, D₁⁆ ⁅m, D₂⁆ ⁅m, D₃⁆)ᴴ *
      vecOp ⁅m, D₁⁆ ⁅m, D₂⁆ ⁅m, D₃⁆) +
    (Matrix.trace ((vecOp ⁅m, D₁⁆ ⁅m, D₂⁆ ⁅m, D₃⁆)ᴴ *
      vecOp ⁅m, D₁⁆ ⁅m, D₂⁆ ⁅m, D₃⁆) +
    Matrix.trace ((fiberEmbed Δ + vecOp F₂₃ F₃₁ (-F₁₂))ᴴ *
      (fiberEmbed Δ + vecOp F₂₃ F₃₁ (-F₁₂)))) = _
  rw [hW, hY]
  simp only [star_zero, zero_mul, zero_add, star_neg, neg_mul_neg,
    nsmul_eq_mul, Nat.cast_ofNat]
  noncomm_ring

/-! ## SA₃: BPS square completion and conditional Bianchi consequence -/

variable [StarRing B]

def bpsFlux (F₂₃ F₃₁ F₁₂ G₁ G₂ G₃ : B) : B :=
  (star F₂₃ * G₁ + star G₁ * F₂₃) +
  (star F₃₁ * G₂ + star G₂ * F₃₁) +
  (star F₁₂ * G₃ + star G₃ * F₁₂)

theorem bps_square_completion_and_bianchi_harmonicity
    (F₂₃ F₃₁ F₁₂ G₁ G₂ G₃ m d₁ d₂ d₃ A₁ A₂ A₃ : B)
    (h23 : ⁅d₂, d₃⁆ = 0) (h31 : ⁅d₃, d₁⁆ = 0) (h12 : ⁅d₁, d₂⁆ = 0)
    (hB23 : ymFieldStrength d₂ d₃ A₂ A₃ = ⁅d₁ + A₁, m⁆)
    (hB31 : ymFieldStrength d₃ d₁ A₃ A₁ = ⁅d₂ + A₂, m⁆)
    (hB12 : ymFieldStrength d₁ d₂ A₁ A₂ = ⁅d₃ + A₃, m⁆) :
    let D₁ := d₁ + A₁
    let D₂ := d₂ + A₂
    let D₃ := d₃ + A₃
    (star F₂₃ * F₂₃ + star F₃₁ * F₃₁ + star F₁₂ * F₁₂) +
      (star G₁ * G₁ + star G₂ * G₂ + star G₃ * G₃) =
      star (F₂₃ - G₁) * (F₂₃ - G₁) +
      star (F₃₁ - G₂) * (F₃₁ - G₂) +
      star (F₁₂ - G₃) * (F₁₂ - G₃) + bpsFlux F₂₃ F₃₁ F₁₂ G₁ G₂ G₃ ∧
    ⁅D₁, ⁅D₁, m⁆⁆ + ⁅D₂, ⁅D₂, m⁆⁆ + ⁅D₃, ⁅D₃, m⁆⁆ = 0 := by
  intro D₁ D₂ D₃
  refine ⟨?_, ?_⟩
  · dsimp [bpsFlux]
    simp only [star_sub]
    noncomm_ring
  · change ⁅d₁ + A₁, ⁅d₁ + A₁, m⁆⁆ +
      ⁅d₂ + A₂, ⁅d₂ + A₂, m⁆⁆ + ⁅d₃ + A₃, ⁅d₃ + A₃, m⁆⁆ = 0
    have hcomm23 : ⁅D₂, D₃⁆ = ⁅D₁, m⁆ :=
      (fieldStrength_as_covariant_commutator d₂ d₃ A₂ A₃ h23).symm.trans hB23
    have hcomm31 : ⁅D₃, D₁⁆ = ⁅D₂, m⁆ :=
      (fieldStrength_as_covariant_commutator d₃ d₁ A₃ A₁ h31).symm.trans hB31
    have hcomm12 : ⁅D₁, D₂⁆ = ⁅D₃, m⁆ :=
      (fieldStrength_as_covariant_commutator d₁ d₂ A₁ A₂ h12).symm.trans hB12
    have hjacobi : ⁅D₁, ⁅D₂, D₃⁆⁆ + ⁅D₂, ⁅D₃, D₁⁆⁆ + ⁅D₃, ⁅D₁, D₂⁆⁆ = 0 := by
      simp only [Ring.lie_def]
      noncomm_ring
    rw [← hcomm23, ← hcomm31, ← hcomm12]
    exact hjacobi

end InfoGeometry.Algebra.NoncommutativeYangMillsHiggsSpectralAction
