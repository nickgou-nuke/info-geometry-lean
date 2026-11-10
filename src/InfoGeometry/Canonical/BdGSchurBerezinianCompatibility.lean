/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/

import Mathlib.Algebra.Field.Basic
import InfoGeometry.Algebra.FiniteSpinAlgebra
import Mathlib.Data.Matrix.Basic
import Mathlib.Tactic

/-!
# Scalar BdG Schur/Berezinian compatibility

This owner records the finite scalar `1 | 1` statement.  It deliberately
does not identify a non-associative Zorn algebra with an associative matrix
algebra.
-/

namespace InfoGeometry.Canonical.BdGSchurBerezinianCompatibility

variable {F : Type*} [Field F]

def blockMatrix {F : Type*} [Ring F] (α β u v : F) : Matrix (Fin 2) (Fin 2) F :=
  !![α, u; v, β]

def schurComplement {F : Type*} [DivisionRing F] (α β u v : F) : F :=
  α - u * β⁻¹ * v

def berezinianScalar {F : Type*} [DivisionRing F] (α β u v : F) : F :=
  schurComplement α β u v / β

def zornNorm {F : Type*} [Ring F] (α β u v : F) : F :=
  α * β - u * v

def bdgBlock {F : Type*} [Ring F] (h Δ : F) : Matrix (Fin 2) (Fin 2) F :=
  blockMatrix h (-h) Δ Δ

theorem zorn_norm_from_schur_of_commute {F : Type*} [DivisionRing F]
    (α β u v : F) (hβ : β ≠ 0) (hcomm : Commute v β) :
    zornNorm α β u v = schurComplement α β u v * β := by
  dsimp [zornNorm, schurComplement]
  rw [sub_mul]
  congr 1
  have h1 : β⁻¹ * v * β = v := by
    calc
      β⁻¹ * v * β = β⁻¹ * (v * β) := by rw [mul_assoc]
      _ = β⁻¹ * (β * v) := by rw [hcomm.eq]
      _ = (β⁻¹ * β) * v := by rw [← mul_assoc]
      _ = 1 * v := by rw [inv_mul_cancel₀ hβ]
      _ = v := one_mul v
  calc
    u * v = u * (β⁻¹ * v * β) := by rw [h1]
    _ = u * β⁻¹ * v * β := by simp only [mul_assoc]

theorem schur_scalar_eq_zorn_norm_div_beta_of_commute {F : Type*} [DivisionRing F]
    (α β u v : F) (hβ : β ≠ 0) (hcomm : Commute v β) :
    schurComplement α β u v = zornNorm α β u v / β := by
  rw [zorn_norm_from_schur_of_commute α β u v hβ hcomm, mul_div_cancel_right₀ _ hβ]

theorem berezinian_scalar_eq_zorn_norm_div_sq_of_commute {F : Type*} [DivisionRing F]
    (α β u v : F) (hβ : β ≠ 0) (hcomm : Commute v β) :
    berezinianScalar α β u v = zornNorm α β u v / β ^ 2 := by
  dsimp [berezinianScalar]
  rw [schur_scalar_eq_zorn_norm_div_beta_of_commute α β u v hβ hcomm]
  rw [div_eq_mul_inv, div_eq_mul_inv, div_eq_mul_inv, mul_assoc, ← mul_inv_rev, ← sq]

@[simp] theorem det_blockMatrix {R : Type*} [CommRing R] (α β u v : R) :
    Matrix.det (blockMatrix α β u v) = zornNorm α β u v := by
  simp [blockMatrix, zornNorm, Matrix.det_fin_two]

theorem schur_scalar_eq_zorn_norm_div_beta
    (α β u v : F) (hβ : β ≠ 0) :
    schurComplement α β u v = zornNorm α β u v / β := by
  unfold schurComplement zornNorm
  field_simp [hβ]

theorem zorn_norm_from_schur
    (α β u v : F) (hβ : β ≠ 0) :
    zornNorm α β u v = schurComplement α β u v * β := by
  rw [schur_scalar_eq_zorn_norm_div_beta α β u v hβ]
  exact (div_mul_cancel₀ (zornNorm α β u v) hβ).symm

theorem berezinian_scalar_eq_zorn_norm_div_sq
    (α β u v : F) (hβ : β ≠ 0) :
    berezinianScalar α β u v = zornNorm α β u v / β ^ 2 := by
  unfold berezinianScalar
  rw [schur_scalar_eq_zorn_norm_div_beta α β u v hβ]
  field_simp [hβ]

theorem berezinian_scalar_eq_det_div_sq
    (α β u v : F) (hβ : β ≠ 0) :
    berezinianScalar α β u v =
      Matrix.det (blockMatrix α β u v) / β ^ 2 := by
  rw [det_blockMatrix]
  exact berezinian_scalar_eq_zorn_norm_div_sq α β u v hβ

theorem zorn_norm_from_berezinian
    (α β u v : F) (hβ : β ≠ 0) :
    zornNorm α β u v = β ^ 2 * berezinianScalar α β u v := by
  rw [berezinian_scalar_eq_zorn_norm_div_sq α β u v hβ]
  field_simp [hβ]

/- The determinant is recovered directly from the scalar Schur complement. -/
theorem det_from_schur
    (α β u v : F) (hβ : β ≠ 0) :
    Matrix.det (blockMatrix α β u v) =
      schurComplement α β u v * β := by
  rw [det_blockMatrix]
  exact zorn_norm_from_schur α β u v hβ

/- The determinant is recovered directly from the scalar Berezinian. -/
theorem det_from_berezinian
    (α β u v : F) (hβ : β ≠ 0) :
    Matrix.det (blockMatrix α β u v) =
      β ^ 2 * berezinianScalar α β u v := by
  rw [det_blockMatrix]
  exact zorn_norm_from_berezinian α β u v hβ

@[simp] theorem det_bdgBlock {R : Type*} [CommRing R] (h Δ : R) :
    Matrix.det (bdgBlock h Δ) = -(h ^ 2 + Δ ^ 2) := by
  rw [bdgBlock, det_blockMatrix]
  unfold zornNorm
  ring

theorem schur_bdgBlock (h Δ : F) (hh : h ≠ 0) :
    schurComplement h (-h) Δ Δ = (h ^ 2 + Δ ^ 2) / h := by
  rw [schur_scalar_eq_zorn_norm_div_beta h (-h) Δ Δ (neg_ne_zero.mpr hh)]
  unfold zornNorm
  field_simp [hh]
  ring

theorem berezinian_bdgBlock (h Δ : F) (hh : h ≠ 0) :
    berezinianScalar h (-h) Δ Δ = -(h ^ 2 + Δ ^ 2) / h ^ 2 := by
  rw [berezinian_scalar_eq_zorn_norm_div_sq h (-h) Δ Δ (neg_ne_zero.mpr hh)]
  unfold zornNorm
  field_simp [hh]
  ring

theorem scalar_schur_berezinian_packet
    (α β u v : F) (hβ : β ≠ 0) :
    Matrix.det (blockMatrix α β u v) = zornNorm α β u v ∧
      schurComplement α β u v = zornNorm α β u v / β ∧
      zornNorm α β u v = schurComplement α β u v * β ∧
      berezinianScalar α β u v = zornNorm α β u v / β ^ 2 ∧
      berezinianScalar α β u v =
        Matrix.det (blockMatrix α β u v) / β ^ 2 := by
  exact ⟨det_blockMatrix α β u v,
    schur_scalar_eq_zorn_norm_div_beta α β u v hβ,
    zorn_norm_from_schur α β u v hβ,
    berezinian_scalar_eq_zorn_norm_div_sq α β u v hβ,
    berezinian_scalar_eq_det_div_sq α β u v hβ⟩

open InfoGeometry.Algebra.FiniteSpin in
/-- Non-commutativity witness for the finite spin operator carrier. -/
theorem canonical_bdg_schur_spin_carrier_noncomm : J_plus * J_minus ≠ J_minus * J_plus :=
  j_plus_j_minus_ne

end InfoGeometry.Canonical.BdGSchurBerezinianCompatibility
