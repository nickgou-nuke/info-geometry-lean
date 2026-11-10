/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/

import Mathlib.Algebra.Field.Basic
import InfoGeometry.Algebra.FiniteSpinAlgebra
import Mathlib.Data.Matrix.Basic
import Mathlib.Tactic

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace InfoGeometry.Algebra.BdGSchurBerezinianCompatibility

def blockMatrix {F : Type*} [Ring F] (α β u v : F) : Matrix (Fin 2) (Fin 2) F :=
  !![α, u; v, β]

def schurComplement {F : Type*} [DivisionRing F] (α β u v : F) : F :=
  α - u * β⁻¹ * v

def berezinianScalar {F : Type*} [DivisionRing F] (α β u v : F) : F :=
  schurComplement α β u v / β

def zornNorm {F : Type*} [Ring F] (α β u v : F) : F :=
  α * β - u * v

/-- Over any non-commutative `[DivisionRing F]`, the Zorn norm factors as
`schurComplement α β u v * β` whenever `v` commutes with `β`. -/
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

/-- Over any non-commutative `[DivisionRing F]`, `schurComplement α β u v = zornNorm α β u v / β`
whenever `v` commutes with `β`. -/
theorem schur_scalar_eq_zorn_norm_div_beta_of_commute {F : Type*} [DivisionRing F]
    (α β u v : F) (hβ : β ≠ 0) (hcomm : Commute v β) :
    schurComplement α β u v = zornNorm α β u v / β := by
  rw [zorn_norm_from_schur_of_commute α β u v hβ hcomm, mul_div_cancel_right₀ _ hβ]

/-- Over any non-commutative `[DivisionRing F]`, `berezinianScalar α β u v = zornNorm α β u v / β ^ 2`
whenever `v` commutes with `β`. -/
theorem berezinian_scalar_eq_zorn_norm_div_sq_of_commute {F : Type*} [DivisionRing F]
    (α β u v : F) (hβ : β ≠ 0) (hcomm : Commute v β) :
    berezinianScalar α β u v = zornNorm α β u v / β ^ 2 := by
  dsimp [berezinianScalar]
  rw [schur_scalar_eq_zorn_norm_div_beta_of_commute α β u v hβ hcomm]
  rw [div_eq_mul_inv, div_eq_mul_inv, div_eq_mul_inv, mul_assoc, ← mul_inv_rev, ← sq]

variable {F : Type*} [Field F]

@[simp] theorem det_blockMatrix {R : Type*} [CommRing R] (α β u v : R) :
    Matrix.det (blockMatrix α β u v) = zornNorm α β u v := by
  simp [blockMatrix, zornNorm, Matrix.det_fin_two]

theorem schur_scalar_eq_zorn_norm_div_beta
    (α β u v : F) (hβ : β ≠ 0) :
    schurComplement α β u v = zornNorm α β u v / β :=
  schur_scalar_eq_zorn_norm_div_beta_of_commute α β u v hβ (Commute.all v β)

theorem berezinian_scalar_eq_zorn_norm_div_sq
    (α β u v : F) (hβ : β ≠ 0) :
    berezinianScalar α β u v = zornNorm α β u v / β ^ 2 :=
  berezinian_scalar_eq_zorn_norm_div_sq_of_commute α β u v hβ (Commute.all v β)

theorem zorn_norm_from_schur
    (α β u v : F) (hβ : β ≠ 0) :
    zornNorm α β u v = schurComplement α β u v * β :=
  zorn_norm_from_schur_of_commute α β u v hβ (Commute.all v β)

open InfoGeometry.Algebra.FiniteSpin in
/-- Non-commutativity witness for the finite spin operator carrier. -/
theorem bdg_schur_spin_carrier_noncomm : J_plus * J_minus ≠ J_minus * J_plus :=
  j_plus_j_minus_ne

end InfoGeometry.Algebra.BdGSchurBerezinianCompatibility
