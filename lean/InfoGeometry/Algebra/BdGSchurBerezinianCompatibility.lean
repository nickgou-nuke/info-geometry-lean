/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/

import Mathlib.Algebra.Field.Basic
import Mathlib.LinearAlgebra.Matrix.SchurComplement
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Physics.NuclearFeshbachReduction
import InfoGeometry.Supergeometry.BerezinianDecomposition
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

section FeshbachBerezinianBridge

open InfoGeometry.Physics
open InfoGeometry.Supergeometry

/-- The 2×2 Berezinian in `BerezinianDecomposition` coincides on `blockMatrix α β u v`
with `berezinianScalar α β u v`. -/
theorem berezinian_blockMatrix_eq_berezinianScalar {F : Type*} [DivisionRing F]
    (α β u v : F) :
    Berezinian.berezinian (blockMatrix α β u v) β⁻¹ = berezinianScalar α β u v := by
  dsimp [Berezinian.berezinian, blockMatrix, berezinianScalar, schurComplement]
  rw [div_eq_mul_inv]

/-- The `(0, 0)` entry of the Super-LU diagonal factor `factorH` is `schurComplement`. -/
theorem factorH_blockMatrix_00 {F : Type*} [DivisionRing F] (α β u v : F) :
    Berezinian.factorH (blockMatrix α β u v) β⁻¹ 0 0 = schurComplement α β u v := by
  dsimp [Berezinian.factorH, blockMatrix, schurComplement]

/-- The determinant of `blockMatrix α β u v` equals the determinant of its Super-LU
diagonal factor `factorH (blockMatrix α β u v) β⁻¹` whenever `β ≠ 0`. -/
theorem det_blockMatrix_eq_det_factorH {F : Type*} [Field F] (α β u v : F) (hβ : β ≠ 0) :
    Matrix.det (blockMatrix α β u v) =
      Matrix.det (Berezinian.factorH (blockMatrix α β u v) β⁻¹) := by
  have hlu := Berezinian.super_lu_factorization (blockMatrix α β u v) β⁻¹ (by
    dsimp [blockMatrix]
    simp [mul_inv_cancel₀ hβ])
  have hdet := congrArg Matrix.det hlu
  rw [Matrix.det_mul, Matrix.det_mul] at hdet
  have hL : Matrix.det (Berezinian.factorL (blockMatrix α β u v) β⁻¹) = 1 := by
    simp [Berezinian.factorL, Matrix.det_fin_two]
  have hR : Matrix.det (Berezinian.factorR (blockMatrix α β u v) β⁻¹) = 1 := by
    simp [Berezinian.factorR, Matrix.det_fin_two]
  rw [hL, hR, one_mul, mul_one] at hdet
  exact hdet.symm

/-- Model-space projector `P` onto the first coordinate of `Fin 2 → R`. -/
noncomputable def feshbachModelProj (R : Type*) [CommRing R] : Module.End R (Fin 2 → R) :=
  Matrix.toLinAlgEquiv' !![(1 : R), 0; 0, 0]

/-- Idempotence of the 2-level model-space projector `P * P = P`. -/
theorem feshbachModelProj_idem (R : Type*) [CommRing R] :
    feshbachModelProj R * feshbachModelProj R = feshbachModelProj R := by
  dsimp [feshbachModelProj]
  rw [← map_mul]
  congr 1
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]

/-- Complementary Feshbach resolvent at spectral parameter `E = 0` for `blockMatrix α β u v`. -/
noncomputable def feshbachResolventAt0 (F : Type*) [Field F] (β : F) :
    Module.End F (Fin 2 → F) :=
  Matrix.toLinAlgEquiv' !![0, 0; 0, -β⁻¹]

/-- Complementary Feshbach resolvent at arbitrary spectral parameter `E`. -/
noncomputable def feshbachResolventAt (F : Type*) [Field F] (β E : F) :
    Module.End F (Fin 2 → F) :=
  Matrix.toLinAlgEquiv' !![0, 0; 0, (E - β)⁻¹]

/-- Verification of all four `NuclearFeshbachReduction` complementary resolvent conditions
for `feshbachResolventAt0 F β` on `blockMatrix α β u v` at `E = 0` when `β ≠ 0`. -/
theorem feshbachResolventAt0_complement_inv {F : Type*} [Field F]
    (α β u v : F) (hβ : β ≠ 0) :
    (1 - feshbachModelProj F) * feshbachResolventAt0 F β = feshbachResolventAt0 F β ∧
    feshbachResolventAt0 F β * (1 - feshbachModelProj F) = feshbachResolventAt0 F β ∧
    NuclearFeshbachReduction.denominator (feshbachModelProj F)
      (Matrix.toLinAlgEquiv' (blockMatrix α β u v)) 0 * feshbachResolventAt0 F β =
        1 - feshbachModelProj F ∧
    feshbachResolventAt0 F β * NuclearFeshbachReduction.denominator (feshbachModelProj F)
      (Matrix.toLinAlgEquiv' (blockMatrix α β u v)) 0 =
        1 - feshbachModelProj F := by
  have h1P : (1 - feshbachModelProj F : Module.End F (Fin 2 → F)) =
      Matrix.toLinAlgEquiv' !![0, 0; 0, (1 : F)] := by
    rw [feshbachModelProj, ← map_one (Matrix.toLinAlgEquiv' (R := F) (n := Fin 2)), ← map_sub]
    congr 1
    ext i j
    fin_cases i <;> fin_cases j <;> simp
  have hden : NuclearFeshbachReduction.denominator (feshbachModelProj F)
      (Matrix.toLinAlgEquiv' (blockMatrix α β u v)) 0 =
      Matrix.toLinAlgEquiv' !![0, 0; 0, -β] := by
    dsimp [NuclearFeshbachReduction.denominator]
    rw [zero_smul, zero_sub, h1P, ← map_mul, ← map_mul, ← map_neg]
    congr 1
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [blockMatrix, Matrix.mul_apply, Fin.sum_univ_two]
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [h1P, feshbachResolventAt0, ← map_mul]
    congr 1
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]
  · rw [h1P, feshbachResolventAt0, ← map_mul]
    congr 1
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]
  · rw [hden, feshbachResolventAt0, h1P, ← map_mul]
    congr 1
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.mul_apply, Fin.sum_univ_two, mul_inv_cancel₀ hβ]
  · rw [hden, feshbachResolventAt0, h1P, ← map_mul]
    congr 1
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.mul_apply, Fin.sum_univ_two, inv_mul_cancel₀ hβ]

/-- At `E = 0`, the Feshbach effective Hamiltonian of `blockMatrix α β u v` equals the
projection onto the model corner of `schurComplement α β u v`. -/
theorem feshbach_effectiveHamiltonian_blockMatrix {F : Type*} [Field F]
    (α β u v : F) :
    NuclearFeshbachReduction.effectiveHamiltonian (feshbachModelProj F)
      (Matrix.toLinAlgEquiv' (blockMatrix α β u v)) (feshbachResolventAt0 F β) =
      Matrix.toLinAlgEquiv' !![schurComplement α β u v, 0; 0, 0] := by
  dsimp [NuclearFeshbachReduction.effectiveHamiltonian, feshbachModelProj, feshbachResolventAt0]
  simp only [← map_mul, ← map_add]
  congr 1
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [blockMatrix, schurComplement, Matrix.mul_apply, Fin.sum_univ_two]
  ring

/-- Applying the `E = 0` Feshbach effective Hamiltonian to `e₀ = ![1, 0]` recovers
`schurComplement α β u v`. -/
theorem feshbach_effectiveHamiltonian_apply_e0 {F : Type*} [Field F]
    (α β u v : F) :
    NuclearFeshbachReduction.effectiveHamiltonian (feshbachModelProj F)
      (Matrix.toLinAlgEquiv' (blockMatrix α β u v)) (feshbachResolventAt0 F β) ![1, 0] 0 =
      schurComplement α β u v := by
  rw [feshbach_effectiveHamiltonian_blockMatrix]
  simp [Matrix.toLinAlgEquiv'_apply, Matrix.mulVec, Fin.sum_univ_two]

/-- The scalar Berezinian equals the `(0, 0)` Feshbach effective-Hamiltonian value divided
by `β`, matching `Berezinian.berezinian (blockMatrix α β u v) β⁻¹`. -/
theorem berezinianScalar_eq_feshbach_div_beta {F : Type*} [Field F]
    (α β u v : F) :
    berezinianScalar α β u v =
      NuclearFeshbachReduction.effectiveHamiltonian (feshbachModelProj F)
        (Matrix.toLinAlgEquiv' (blockMatrix α β u v)) (feshbachResolventAt0 F β) ![1, 0] 0 / β := by
  rw [feshbach_effectiveHamiltonian_apply_e0]
  dsimp [berezinianScalar]

/-- Complementary resolvent conditions at arbitrary spectral parameter `E` when `E - β ≠ 0`. -/
theorem feshbachResolventAt_complement_inv {F : Type*} [Field F]
    (α β u v E : F) (hEβ : E - β ≠ 0) :
    (1 - feshbachModelProj F) * feshbachResolventAt F β E = feshbachResolventAt F β E ∧
    feshbachResolventAt F β E * (1 - feshbachModelProj F) = feshbachResolventAt F β E ∧
    NuclearFeshbachReduction.denominator (feshbachModelProj F)
      (Matrix.toLinAlgEquiv' (blockMatrix α β u v)) E * feshbachResolventAt F β E =
        1 - feshbachModelProj F ∧
    feshbachResolventAt F β E * NuclearFeshbachReduction.denominator (feshbachModelProj F)
      (Matrix.toLinAlgEquiv' (blockMatrix α β u v)) E =
        1 - feshbachModelProj F := by
  have h1P : (1 - feshbachModelProj F : Module.End F (Fin 2 → F)) =
      Matrix.toLinAlgEquiv' !![0, 0; 0, (1 : F)] := by
    rw [feshbachModelProj, ← map_one (Matrix.toLinAlgEquiv' (R := F) (n := Fin 2)), ← map_sub]
    congr 1
    ext i j
    fin_cases i <;> fin_cases j <;> simp
  have hden : NuclearFeshbachReduction.denominator (feshbachModelProj F)
      (Matrix.toLinAlgEquiv' (blockMatrix α β u v)) E =
      Matrix.toLinAlgEquiv' !![0, 0; 0, E - β] := by
    dsimp [NuclearFeshbachReduction.denominator]
    rw [h1P, ← map_mul, ← map_mul, ← map_smul, ← map_sub]
    congr 1
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [blockMatrix, Matrix.mul_apply, Fin.sum_univ_two]
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [h1P, feshbachResolventAt, ← map_mul]
    congr 1
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]
  · rw [h1P, feshbachResolventAt, ← map_mul]
    congr 1
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]
  · rw [hden, feshbachResolventAt, h1P, ← map_mul]
    congr 1
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.mul_apply, Fin.sum_univ_two, mul_inv_cancel₀ hEβ]
  · rw [hden, feshbachResolventAt, h1P, ← map_mul]
    congr 1
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.mul_apply, Fin.sum_univ_two, inv_mul_cancel₀ hEβ]

/-- At arbitrary spectral parameter `E`, the Feshbach effective Hamiltonian equals the
shifted Schur complement `schurComplement α (β - E) u v` on the model corner. -/
theorem feshbach_effectiveHamiltonian_blockMatrix_at {F : Type*} [Field F]
    (α β u v E : F) :
    NuclearFeshbachReduction.effectiveHamiltonian (feshbachModelProj F)
      (Matrix.toLinAlgEquiv' (blockMatrix α β u v)) (feshbachResolventAt F β E) =
      Matrix.toLinAlgEquiv' !![schurComplement α (β - E) u v, 0; 0, 0] := by
  dsimp [NuclearFeshbachReduction.effectiveHamiltonian, feshbachModelProj, feshbachResolventAt]
  simp only [← map_mul, ← map_add]
  congr 1
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [blockMatrix, schurComplement, Matrix.mul_apply, Fin.sum_univ_two]
  have hneg : (E - β)⁻¹ = -(β - E)⁻¹ := by
    rw [← inv_neg, neg_sub]
  rw [hneg]
  ring

/-! ### Generalized Block-Matrix Schur–Feshbach–Berezinian Compatibility -/

section GeneralBlockSchurFeshbach

variable {ι₀ ι₁ : Type*} [DecidableEq ι₀] [Fintype ι₀] [DecidableEq ι₁] [Fintype ι₁]

/-- General block Schur complement `A - B * D_inv * C` over an arbitrary ring `R`. -/
def blockSchurComplement {R : Type*} [Ring R]
    (A : Matrix ι₀ ι₀ R) (B : Matrix ι₀ ι₁ R) (C : Matrix ι₁ ι₀ R)
    (D_inv : Matrix ι₁ ι₁ R) : Matrix ι₀ ι₀ R :=
  A - B * D_inv * C

/-- General block Super-LU trifactor decomposition over an arbitrary (possibly noncommutative)
ring `R` when `D * D_inv = 1` and `D_inv * D = 1`. -/
theorem blockSuperLU_factorization {R : Type*} [Ring R]
    (A : Matrix ι₀ ι₀ R) (B : Matrix ι₀ ι₁ R) (C : Matrix ι₁ ι₀ R)
    (D D_inv : Matrix ι₁ ι₁ R) (hDR : D * D_inv = 1) (hDL : D_inv * D = 1) :
    Matrix.fromBlocks (1 : Matrix ι₀ ι₀ R) (B * D_inv) 0 (1 : Matrix ι₁ ι₁ R) *
      Matrix.fromBlocks (blockSchurComplement A B C D_inv) 0 0 D *
      Matrix.fromBlocks (1 : Matrix ι₀ ι₀ R) 0 (D_inv * C) (1 : Matrix ι₁ ι₁ R) =
      Matrix.fromBlocks A B C D := by
  dsimp [blockSchurComplement]
  rw [Matrix.fromBlocks_multiply, Matrix.fromBlocks_multiply]
  simp only [Matrix.mul_one, Matrix.one_mul, Matrix.zero_mul, Matrix.mul_zero,
    add_zero, zero_add]
  congr 1
  · calc
      A - B * D_inv * C + B * D_inv * D * (D_inv * C)
          = A - B * D_inv * C + B * (D_inv * D) * D_inv * C := by
              simp only [Matrix.mul_assoc]
      _ = A - B * D_inv * C + B * (1 : Matrix ι₁ ι₁ R) * D_inv * C := by rw [hDL]
      _ = A - B * D_inv * C + B * D_inv * C := by rw [Matrix.mul_one]
      _ = A := sub_add_cancel A (B * D_inv * C)
  · calc
      B * D_inv * D = B * (D_inv * D) := Matrix.mul_assoc B D_inv D
      _ = B * (1 : Matrix ι₁ ι₁ R) := by rw [hDL]
      _ = B := Matrix.mul_one B
  · calc
      D * (D_inv * C) = (D * D_inv) * C := (Matrix.mul_assoc D D_inv C).symm
      _ = (1 : Matrix ι₁ ι₁ R) * C := by rw [hDR]
      _ = C := Matrix.one_mul C

/-- Noncommutative matrix-level Feshbach elimination of the complementary block `(1 - P)`
equals the block Schur complement `A - B * D_inv * C` over any `[Ring R]`. -/
theorem blockFeshbach_matrix_effectiveHamiltonian {R : Type*} [Ring R]
    (A : Matrix ι₀ ι₀ R) (B : Matrix ι₀ ι₁ R) (C : Matrix ι₁ ι₀ R)
    (D D_inv : Matrix ι₁ ι₁ R) :
    let P : Matrix (ι₀ ⊕ ι₁) (ι₀ ⊕ ι₁) R := Matrix.fromBlocks 1 0 0 0
    let H : Matrix (ι₀ ⊕ ι₁) (ι₀ ⊕ ι₁) R := Matrix.fromBlocks A B C D
    let R_op : Matrix (ι₀ ⊕ ι₁) (ι₀ ⊕ ι₁) R := Matrix.fromBlocks 0 0 0 (-D_inv)
    P * H * P + P * H * R_op * H * P =
      Matrix.fromBlocks (blockSchurComplement A B C D_inv) 0 0 0 := by
  intro P H R_op
  dsimp [P, H, R_op, blockSchurComplement]
  simp only [Matrix.fromBlocks_multiply, Matrix.mul_one, Matrix.one_mul,
    Matrix.zero_mul, Matrix.mul_zero, add_zero, zero_add, Matrix.neg_mul,
    Matrix.mul_neg, Matrix.fromBlocks_add, neg_zero]
  congr 1
  rw [← sub_eq_add_neg]

/-- Determinant factorization of a block matrix around an invertible `D` block via
`blockSchurComplement` and `Matrix.det_fromBlocks₂₂`. -/
theorem det_fromBlocks_eq_det_schur_mul_det_D {R : Type*} [CommRing R]
    (A : Matrix ι₀ ι₀ R) (B : Matrix ι₀ ι₁ R) (C : Matrix ι₁ ι₀ R)
    (D D_inv : Matrix ι₁ ι₁ R) (hDR : D * D_inv = 1) (hDL : D_inv * D = 1) :
    (Matrix.fromBlocks A B C D).det =
      (blockSchurComplement A B C D_inv).det * D.det := by
  let : Invertible D := ⟨D_inv, hDL, hDR⟩
  rw [Matrix.det_fromBlocks₂₂ A B C D, mul_comm]
  rfl

/-- Canonical model-space projector `P` onto the even/model block `ι₀` in `ι₀ ⊕ ι₁ → R`. -/
noncomputable def blockProjectorP (ι₀ ι₁ R : Type*)
    [DecidableEq ι₀] [Fintype ι₀] [DecidableEq ι₁] [Fintype ι₁] [CommRing R] :
    Module.End R ((ι₀ ⊕ ι₁) → R) :=
  Matrix.toLinAlgEquiv' (Matrix.fromBlocks (1 : Matrix ι₀ ι₀ R) 0 0 0)

/-- Idempotence of `blockProjectorP`: `P * P = P`. -/
theorem blockProjectorP_idem (ι₀ ι₁ R : Type*)
    [DecidableEq ι₀] [Fintype ι₀] [DecidableEq ι₁] [Fintype ι₁] [CommRing R] :
    blockProjectorP ι₀ ι₁ R * blockProjectorP ι₀ ι₁ R = blockProjectorP ι₀ ι₁ R := by
  dsimp [blockProjectorP]
  rw [← map_mul, Matrix.fromBlocks_multiply]
  simp

/-- General Feshbach effective Hamiltonian of `Matrix.fromBlocks A B C D` with complementary
resolvent `-D_inv` equals the block Schur complement `blockSchurComplement A B C D_inv`. -/
theorem blockFeshbach_effectiveHamiltonian_eq_schurComplement {R : Type*} [CommRing R]
    (A : Matrix ι₀ ι₀ R) (B : Matrix ι₀ ι₁ R) (C : Matrix ι₁ ι₀ R)
    (D D_inv : Matrix ι₁ ι₁ R) :
    NuclearFeshbachReduction.effectiveHamiltonian (blockProjectorP ι₀ ι₁ R)
      (Matrix.toLinAlgEquiv' (Matrix.fromBlocks A B C D))
      (Matrix.toLinAlgEquiv' (Matrix.fromBlocks 0 0 0 (-D_inv))) =
      Matrix.toLinAlgEquiv' (Matrix.fromBlocks (blockSchurComplement A B C D_inv) 0 0 0) := by
  dsimp [NuclearFeshbachReduction.effectiveHamiltonian, blockProjectorP]
  simp only [← map_mul, ← map_add]
  congr 1
  exact blockFeshbach_matrix_effectiveHamiltonian A B C D D_inv

/-- At `E = 0` over a field `K`, `-D_inv` satisfies all four `NuclearFeshbachReduction`
complementary resolvent conditions for `denominator (blockProjectorP ι₀ ι₁ K) H 0`. -/
theorem blockFeshbach_denominator_zero_inv {K : Type*} [Field K]
    (A : Matrix ι₀ ι₀ K) (B : Matrix ι₀ ι₁ K) (C : Matrix ι₁ ι₀ K)
    (D D_inv : Matrix ι₁ ι₁ K) (hDR : D * D_inv = 1) (hDL : D_inv * D = 1) :
    let P := blockProjectorP ι₀ ι₁ K
    let H := Matrix.toLinAlgEquiv' (Matrix.fromBlocks A B C D)
    let R_op := Matrix.toLinAlgEquiv' (Matrix.fromBlocks (0 : Matrix ι₀ ι₀ K) 0 0 (-D_inv))
    (1 - P) * R_op = R_op ∧
    R_op * (1 - P) = R_op ∧
    NuclearFeshbachReduction.denominator P H 0 * R_op = 1 - P ∧
    R_op * NuclearFeshbachReduction.denominator P H 0 = 1 - P := by
  intro P H R_op
  have h1P : 1 - P =
      Matrix.toLinAlgEquiv' (Matrix.fromBlocks (0 : Matrix ι₀ ι₀ K) 0 0 (1 : Matrix ι₁ ι₁ K)) := by
    dsimp [P, blockProjectorP]
    rw [← map_one (Matrix.toLinAlgEquiv' (R := K) (n := ι₀ ⊕ ι₁)), ← map_sub]
    congr 1
    rw [← Matrix.fromBlocks_one, sub_eq_add_neg, Matrix.fromBlocks_neg,
      Matrix.fromBlocks_add]
    simp
  have hden : NuclearFeshbachReduction.denominator P H 0 =
      Matrix.toLinAlgEquiv' (Matrix.fromBlocks (0 : Matrix ι₀ ι₀ K) 0 0 (-D)) := by
    dsimp [NuclearFeshbachReduction.denominator, H]
    rw [zero_smul, zero_sub, h1P, ← map_mul, ← map_mul, ← map_neg]
    congr 1
    rw [Matrix.fromBlocks_multiply, Matrix.fromBlocks_multiply, Matrix.fromBlocks_neg]
    simp
  refine ⟨?_, ?_, ?_, ?_⟩
  · dsimp [R_op]
    rw [h1P, ← map_mul, Matrix.fromBlocks_multiply]
    simp
  · dsimp [R_op]
    rw [h1P, ← map_mul, Matrix.fromBlocks_multiply]
    simp
  · dsimp [R_op]
    rw [hden, h1P, ← map_mul, Matrix.fromBlocks_multiply]
    simp [hDR]
  · dsimp [R_op]
    rw [hden, h1P, ← map_mul, Matrix.fromBlocks_multiply]
    simp [hDL]

/-- **Projection-Noncommutativity Obstruction Theorem** over an arbitrary ring `K`:
for any idempotent `P * P = P` and complementary resolvent `(1 - P) * R = R`, `R * (1 - P) = R`,
the Feshbach self-energy shift `effectiveHamiltonian P H R - P * H * P` equals the negative
conjugated commutator square `-(P * [P, H] * R * [P, H] * P)`. -/
theorem feshbach_shift_eq_neg_commutator_sq {K V : Type*} [Ring K]
    [AddCommGroup V] [Module K V]
    (P H R : Module.End K V)
    (hP : P * P = P)
    (hQR : (1 - P) * R = R)
    (hRQ : R * (1 - P) = R) :
    NuclearFeshbachReduction.effectiveHamiltonian P H R - P * H * P =
      -(P * (P * H - H * P) * R * (P * H - H * P) * P) := by
  have hPR : P * R = 0 :=
    NuclearFeshbachReduction.projection_mul_resolvent_eq_zero P R hQR
  have hRP : R * P = 0 :=
    NuclearFeshbachReduction.resolvent_mul_projection_eq_zero P R hRQ
  have hLHS : NuclearFeshbachReduction.effectiveHamiltonian P H R - P * H * P =
      P * H * R * H * P := by
    dsimp [NuclearFeshbachReduction.effectiveHamiltonian]
    abel
  have hRHS : -(P * (P * H - H * P) * R * (P * H - H * P) * P) =
      P * H * R * H * P := by
    calc
      -(P * (P * H - H * P) * R * (P * H - H * P) * P)
          = -((P * P * H - P * H * P) * R * (P * H * P - H * (P * P))) := by
              noncomm_ring
      _ = -((P * H - P * H * P) * R * (P * H * P - H * P)) := by
              rw [hP]
      _ = -(P * H * R * (P * H * P) - P * H * R * (H * P) -
            P * H * (P * R) * (P * H * P) + P * H * (P * R) * (H * P)) := by
              noncomm_ring
      _ = -(P * H * (R * P) * H * P - P * H * R * H * P) := by
              rw [hPR]
              noncomm_ring
      _ = P * H * R * H * P := by
              rw [hRP]
              noncomm_ring
  exact hLHS.trans hRHS.symm

/-- When the projection commutes with the Hamiltonian (`[P, H] = 0`), the Feshbach self-energy
shift collapses identically (`effectiveHamiltonian P H R = P * H * P`). -/
theorem feshbach_effectiveHamiltonian_eq_projected_of_commute {K V : Type*} [Ring K]
    [AddCommGroup V] [Module K V]
    (P H R : Module.End K V)
    (hcomm : P * H - H * P = 0)
    (hP : P * P = P)
    (hQR : (1 - P) * R = R)
    (hRQ : R * (1 - P) = R) :
    NuclearFeshbachReduction.effectiveHamiltonian P H R = P * H * P := by
  have hshift := feshbach_shift_eq_neg_commutator_sq P H R hP hQR hRQ
  simp [hcomm] at hshift
  exact sub_eq_zero.mp hshift

/-- When the block projector `P = fromBlocks 1 0 0 0` commutes with `H = fromBlocks A B C D`,
both off-diagonal couplings `B, C` vanish and `blockSchurComplement A B C D_inv = A`. -/
theorem blockSchurComplement_of_commute {R : Type*} [Ring R]
    (A : Matrix ι₀ ι₀ R) (B : Matrix ι₀ ι₁ R) (C : Matrix ι₁ ι₀ R)
    (D : Matrix ι₁ ι₁ R) (D_inv : Matrix ι₁ ι₁ R)
    (hcomm : Matrix.fromBlocks (1 : Matrix ι₀ ι₀ R) 0 0 0 * Matrix.fromBlocks A B C D -
      Matrix.fromBlocks A B C D * Matrix.fromBlocks (1 : Matrix ι₀ ι₀ R) 0 0 0 = 0) :
    B = 0 ∧ C = 0 ∧ blockSchurComplement A B C D_inv = A := by
  have hM : Matrix.fromBlocks (0 : Matrix ι₀ ι₀ R) B (-C) 0 = 0 := by
    rw [Matrix.fromBlocks_multiply, Matrix.fromBlocks_multiply] at hcomm
    simp only [Matrix.one_mul, Matrix.mul_one, Matrix.zero_mul, Matrix.mul_zero,
      add_zero, zero_add] at hcomm
    rw [sub_eq_add_neg, Matrix.fromBlocks_neg, Matrix.fromBlocks_add] at hcomm
    simpa using hcomm
  have hB : B = 0 := by
    have h12 := congrArg Matrix.toBlocks₁₂ hM
    change B = 0 at h12
    exact h12
  have hC : C = 0 := by
    have h21 := congrArg Matrix.toBlocks₂₁ hM
    change -C = 0 at h21
    exact neg_eq_zero.mp h21
  refine ⟨hB, hC, ?_⟩
  dsimp [blockSchurComplement]
  rw [hB, hC]
  simp

/-- When `[P, H] = 0`, the block determinant factors completely as `A.det * D.det` without
any Schur correction. -/
theorem det_fromBlocks_eq_det_mul_of_commute {R : Type*} [CommRing R]
    (A : Matrix ι₀ ι₀ R) (B : Matrix ι₀ ι₁ R) (C : Matrix ι₁ ι₀ R)
    (D D_inv : Matrix ι₁ ι₁ R) (hDR : D * D_inv = 1) (hDL : D_inv * D = 1)
    (hcomm : Matrix.fromBlocks (1 : Matrix ι₀ ι₀ R) 0 0 0 * Matrix.fromBlocks A B C D -
      Matrix.fromBlocks A B C D * Matrix.fromBlocks (1 : Matrix ι₀ ι₀ R) 0 0 0 = 0) :
    (Matrix.fromBlocks A B C D).det = A.det * D.det := by
  obtain ⟨_, _, hS⟩ := blockSchurComplement_of_commute A B C D D_inv hcomm
  rw [det_fromBlocks_eq_det_schur_mul_det_D A B C D D_inv hDR hDL, hS]

end GeneralBlockSchurFeshbach

end FeshbachBerezinianBridge

end InfoGeometry.Algebra.BdGSchurBerezinianCompatibility
