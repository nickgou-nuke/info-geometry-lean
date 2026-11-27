/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import Mathlib.Data.Matrix.Basic
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic
import InfoGeometry.Modular.TomitaCommutantDuality
import InfoGeometry.Modular.TomitaChiralJ

/-!
# Complex Matrix Tomita Polar Decomposition & Regular-Representation Commutant Duality (`F1`/`F2`, Finite Carrier)

This module constructs the finite-dimensional **complex** Hilbert–Schmidt Tomita–Takesaki
polar decomposition and proves the **full regular-representation commutant duality theorem**
on `Matrix (Fin n) (Fin n) ℂ` (`HSMat n`), keeping the complex `conjTranspose` (`ᴴ`) carrier
strictly distinct from the real transpose carrier in `FiniteMatrixTomitaPolar`.

## Main Results
1. **Complex Hilbert–Schmidt Inner Product** `hsInnerC X Y = (Xᴴ * Y).trace`:
   conjugate-symmetric, nonnegative on diagonal, and faithful (`hsInnerC X X = 0 ↔ X = 0`).
2. **Complex Tomita Polar Decomposition** for any Hermitian invertible `F : PositiveComplexDensityFactor n`:
   `S X = r⁻¹ Xᴴ r`, `J X = Xᴴ`, `Δ X = ρ X ρ⁻¹`, `Δ^{1/2} X = r X r⁻¹`,
   proving `S² = id`, `S = J ∘ Δ^{1/2}`, `J` antiunitary, `J Δ J = Δ⁻¹`, and the exact KMS identity
   `(F.rho * (A * modularOpC F B)).trace = (F.rho * (B * A)).trace`.
3. **Full Regular-Representation Commutant Duality (`F2`, Stage 3a)**:
   For the **full** left regular representation `leftRegSet n := { L_A | A ∈ M_n(ℂ) }` and
   **full** right regular representation `rightRegSet n := { R_B | B ∈ M_n(ℂ) }`, proves
   unconditionally:
   - `commutant (leftRegSet n) = rightRegSet n` (via evaluation at `1`)
   - `J (leftRegSet n) J = rightRegSet n`
   - `complexMatrixTomitaDualityData n : TomitaDualityData (modularConjInvolution n) (leftRegSet n)`
   - `complexMatrix_commutant_eq_J_conj` and `complexMatrix_bicommutant`.
-/

noncomputable section

namespace InfoGeometry.Canonical.ComplexMatrixTomitaCommutantDuality

open Matrix Complex
open scoped BigOperators Matrix
open InfoGeometry.Modular.TomitaCommutantDuality
open InfoGeometry.Modular.TomitaChiralJ

abbrev HSMat (n : ℕ) : Type := Matrix (Fin n) (Fin n) ℂ

section HilbertSchmidtC

variable {n : ℕ}

/-- Complex Hilbert–Schmidt inner product `⟨X, Y⟩_HS = Tr(Xᴴ Y)` on `M_n(ℂ)`. -/
def hsInnerC (X Y : HSMat n) : ℂ :=
  (Xᴴ * Y).trace

/-- Conjugate symmetry of `hsInnerC`. -/
theorem hsInnerC_conj_symm (X Y : HSMat n) :
    star (hsInnerC X Y) = hsInnerC Y X := by
  unfold hsInnerC
  rw [← Matrix.trace_conjTranspose, Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose]

/-- Explicit coordinate sum-of-squares formula for `hsInnerC X X`. -/
theorem hsInnerC_self_eq_sum_normSq (X : HSMat n) :
    (hsInnerC X X).re = ∑ i : Fin n, ∑ j : Fin n, ‖X j i‖ ^ 2 := by
  unfold hsInnerC
  simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.conjTranspose_apply,
    Complex.re_sum, RCLike.star_def, Complex.conj_mul']
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  rw [← Complex.ofReal_pow, Complex.ofReal_re]

/-- Real nonnegativity of `hsInnerC X X`. -/
theorem hsInnerC_self_re_nonneg (X : HSMat n) :
    0 ≤ (hsInnerC X X).re := by
  rw [hsInnerC_self_eq_sum_normSq]
  exact Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => sq_nonneg _

private lemma real_eq_zero_of_neg_eq {x : ℝ} (h : -x = x) : x = 0 := by linarith

/-- Imaginary part of `hsInnerC X X` vanishes. -/
theorem hsInnerC_self_im_zero (X : HSMat n) :
    (hsInnerC X X).im = 0 := by
  have h := hsInnerC_conj_symm X X
  have him := congrArg Complex.im h
  simp only [Complex.star_def, Complex.conj_im] at him
  exact real_eq_zero_of_neg_eq him

/-- Strict positivity / faithfulness of `hsInnerC`. -/
theorem hsInnerC_self_eq_zero_iff (X : HSMat n) :
    hsInnerC X X = 0 ↔ X = 0 := by
  constructor
  · intro h
    have hre : (hsInnerC X X).re = 0 := by rw [h]; simp
    rw [hsInnerC_self_eq_sum_normSq] at hre
    rw [Finset.sum_eq_zero_iff_of_nonneg (fun _ _ =>
      Finset.sum_nonneg fun _ _ => sq_nonneg _)] at hre
    ext j i
    have hi := hre i (Finset.mem_univ i)
    rw [Finset.sum_eq_zero_iff_of_nonneg (fun _ _ => sq_nonneg _)] at hi
    exact norm_eq_zero.mp (sq_eq_zero_iff.mp (hi j (Finset.mem_univ j)))
  · rintro rfl
    simp [hsInnerC]

end HilbertSchmidtC

section ComplexTomitaPolar

variable {n : ℕ}

/-- Hermitian invertible density square-root factor `r = ρ^{1/2}` on `M_n(ℂ)`. -/
structure PositiveComplexDensityFactor (n : ℕ) where
  r : HSMat n
  rInv : HSMat n
  r_herm : rᴴ = r
  rInv_herm : rInvᴴ = rInv
  r_mul_rInv : r * rInv = 1
  rInv_mul_r : rInv * r = 1

namespace PositiveComplexDensityFactor

/-- Density matrix `ρ = r * r`. -/
def rho (F : PositiveComplexDensityFactor n) : HSMat n := F.r * F.r

/-- Inverse density matrix `ρ⁻¹ = r⁻¹ * r⁻¹`. -/
def rhoInv (F : PositiveComplexDensityFactor n) : HSMat n := F.rInv * F.rInv

theorem rho_herm (F : PositiveComplexDensityFactor n) : F.rhoᴴ = F.rho := by
  simp [rho, Matrix.conjTranspose_mul, F.r_herm]

theorem rhoInv_herm (F : PositiveComplexDensityFactor n) : F.rhoInvᴴ = F.rhoInv := by
  simp [rhoInv, Matrix.conjTranspose_mul, F.rInv_herm]

theorem rho_mul_rhoInv (F : PositiveComplexDensityFactor n) : F.rho * F.rhoInv = 1 := by
  calc F.rho * F.rhoInv = F.r * (F.r * F.rInv) * F.rInv := by simp only [rho, rhoInv, Matrix.mul_assoc]
    _ = F.r * 1 * F.rInv := by rw [F.r_mul_rInv]
    _ = F.r * F.rInv := by rw [Matrix.mul_one]
    _ = 1 := F.r_mul_rInv

theorem rhoInv_mul_rho (F : PositiveComplexDensityFactor n) : F.rhoInv * F.rho = 1 := by
  calc F.rhoInv * F.rho = F.rInv * (F.rInv * F.r) * F.r := by simp only [rho, rhoInv, Matrix.mul_assoc]
    _ = F.rInv * 1 * F.r := by rw [F.rInv_mul_r]
    _ = F.rInv * F.r := by rw [Matrix.mul_one]
    _ = 1 := F.rInv_mul_r

end PositiveComplexDensityFactor

/-- Complex modular conjugation `J X = Xᴴ` on `M_n(ℂ)`. -/
def modularConjC (X : HSMat n) : HSMat n := Xᴴ

/-- Complex Tomita operator `S X = r⁻¹ Xᴴ r` on `M_n(ℂ)`. -/
def tomitaOpC (F : PositiveComplexDensityFactor n) (X : HSMat n) : HSMat n :=
  F.rInv * Xᴴ * F.r

/-- Square-root modular operator `Δ^{1/2} X = r X r⁻¹`. -/
def modularSqrtC (F : PositiveComplexDensityFactor n) (X : HSMat n) : HSMat n :=
  F.r * X * F.rInv

/-- Inverse square-root modular operator `Δ^{-1/2} X = r⁻¹ X r`. -/
def modularInvSqrtC (F : PositiveComplexDensityFactor n) (X : HSMat n) : HSMat n :=
  F.rInv * X * F.r

/-- Modular operator `Δ X = ρ X ρ⁻¹`. -/
def modularOpC (F : PositiveComplexDensityFactor n) (X : HSMat n) : HSMat n :=
  F.rho * X * F.rhoInv

/-- Inverse modular operator `Δ⁻¹ X = ρ⁻¹ X ρ`. -/
def modularInvOpC (F : PositiveComplexDensityFactor n) (X : HSMat n) : HSMat n :=
  F.rhoInv * X * F.rho

@[simp]
theorem modularConjC_involutive (X : HSMat n) :
    modularConjC (modularConjC X) = X :=
  Matrix.conjTranspose_conjTranspose X

theorem modularConjC_antiunitary (X Y : HSMat n) :
    hsInnerC (modularConjC X) (modularConjC Y) = hsInnerC Y X := by
  unfold hsInnerC modularConjC
  rw [Matrix.conjTranspose_conjTranspose, ← Matrix.trace_mul_comm]

theorem tomitaOpC_involutive (F : PositiveComplexDensityFactor n) (X : HSMat n) :
    tomitaOpC F (tomitaOpC F X) = X := by
  unfold tomitaOpC
  rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, F.r_herm, F.rInv_herm,
    Matrix.conjTranspose_conjTranspose]
  calc F.rInv * (F.r * (X * F.rInv)) * F.r
      = (F.rInv * F.r) * X * (F.rInv * F.r) := by simp only [Matrix.mul_assoc]
    _ = 1 * X * 1 := by rw [F.rInv_mul_r]
    _ = X := by simp

/-- Exact complex polar decomposition `S = J ∘ Δ^{1/2}`. -/
theorem tomitaOpC_polar_decomposition (F : PositiveComplexDensityFactor n) (X : HSMat n) :
    tomitaOpC F X = modularConjC (modularSqrtC F X) := by
  unfold tomitaOpC modularConjC modularSqrtC
  rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, F.r_herm, F.rInv_herm, Matrix.mul_assoc]

/-- Modular square-root composition `Δ^{1/2} ∘ Δ^{1/2} = Δ`. -/
theorem modularSqrtC_sq (F : PositiveComplexDensityFactor n) (X : HSMat n) :
    modularSqrtC F (modularSqrtC F X) = modularOpC F X := by
  unfold modularSqrtC modularOpC PositiveComplexDensityFactor.rho PositiveComplexDensityFactor.rhoInv
  simp only [Matrix.mul_assoc]

/-- Inverse relation `Δ^{1/2} ∘ Δ^{-1/2} = id` and `Δ^{-1/2} ∘ Δ^{1/2} = id`. -/
theorem modularSqrtC_comp_inv (F : PositiveComplexDensityFactor n) (X : HSMat n) :
    modularSqrtC F (modularInvSqrtC F X) = X := by
  unfold modularSqrtC modularInvSqrtC
  calc F.r * (F.rInv * X * F.r) * F.rInv
      = (F.r * F.rInv) * X * (F.r * F.rInv) := by simp only [Matrix.mul_assoc]
    _ = 1 * X * 1 := by rw [F.r_mul_rInv]
    _ = X := by simp

theorem modularInvSqrtC_comp_sqrt (F : PositiveComplexDensityFactor n) (X : HSMat n) :
    modularInvSqrtC F (modularSqrtC F X) = X := by
  unfold modularSqrtC modularInvSqrtC
  calc F.rInv * (F.r * X * F.rInv) * F.r
      = (F.rInv * F.r) * X * (F.rInv * F.r) := by simp only [Matrix.mul_assoc]
    _ = 1 * X * 1 := by rw [F.rInv_mul_r]
    _ = X := by simp

/-- Conjugation symmetry `J (Δ (J X)) = Δ⁻¹ X`. -/
theorem modularConjC_modularOpC_conj (F : PositiveComplexDensityFactor n) (X : HSMat n) :
    modularConjC (modularOpC F (modularConjC X)) = modularInvOpC F X := by
  unfold modularConjC modularOpC modularInvOpC
  rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul,
    F.rhoInv_herm, F.rho_herm, Matrix.conjTranspose_conjTranspose, Matrix.mul_assoc]

/-- Exact finite complex KMS identity `Tr(ρ A Δ(B)) = Tr(ρ B A)`. -/
theorem modularOpC_kms_identity (F : PositiveComplexDensityFactor n) (A B : HSMat n) :
    (F.rho * (A * modularOpC F B)).trace = (F.rho * (B * A)).trace := by
  unfold modularOpC
  calc (F.rho * (A * (F.rho * B * F.rhoInv))).trace
      = (F.rho * A * F.rho * B * F.rhoInv).trace := by simp only [Matrix.mul_assoc]
    _ = (F.rhoInv * (F.rho * A * F.rho * B)).trace := Matrix.trace_mul_comm _ F.rhoInv
    _ = ((F.rhoInv * F.rho) * A * F.rho * B).trace := by simp only [Matrix.mul_assoc]
    _ = (A * F.rho * B).trace := by rw [F.rhoInv_mul_rho, Matrix.one_mul]
    _ = (F.rho * B * A).trace := by
          rw [Matrix.mul_assoc A F.rho B, Matrix.trace_mul_comm A (F.rho * B), Matrix.mul_assoc]
    _ = (F.rho * (B * A)).trace := by simp only [Matrix.mul_assoc]

/-- Discharges the abstract `TomitaModularData` interface cleanly on `HSMat n`. -/
def complexMatrixTomitaModularData (F : PositiveComplexDensityFactor n) :
    TomitaModularData (HSMat n) where
  vacuum := F.r
  S₀ := tomitaOpC F
  S₀_add := fun X Y => by simp [tomitaOpC, Matrix.conjTranspose_add, Matrix.mul_add, Matrix.add_mul]
  S₀_smul := fun c X => by
    simp [tomitaOpC, Matrix.conjTranspose_smul]
  S₀_involutive := tomitaOpC_involutive F
  S₀_vacuum := by
    unfold tomitaOpC
    rw [F.r_herm, F.rInv_mul_r, Matrix.one_mul]
  delta_half :=
    { toFun := modularSqrtC F
      map_add' := fun X Y => by simp [modularSqrtC, Matrix.mul_add, Matrix.add_mul]
      map_smul' := fun c X => by simp [modularSqrtC] }
  delta_inv_half :=
    { toFun := modularInvSqrtC F
      map_add' := fun X Y => by simp [modularInvSqrtC, Matrix.mul_add, Matrix.add_mul]
      map_smul' := fun c X => by simp [modularInvSqrtC] }
  delta_half_inv := modularSqrtC_comp_inv F
  delta_inv_half_right := modularInvSqrtC_comp_sqrt F
  delta_vacuum := by
    change modularSqrtC F F.r = F.r
    unfold modularSqrtC
    rw [Matrix.mul_assoc, F.r_mul_rInv, Matrix.mul_one]
  delta_inv_vacuum := by
    change modularInvSqrtC F F.r = F.r
    unfold modularInvSqrtC
    rw [F.rInv_mul_r, Matrix.one_mul]

@[simp]
theorem complexMatrixTomitaModularData_modularJ (F : PositiveComplexDensityFactor n) (X : HSMat n) :
    modularJ (complexMatrixTomitaModularData F) X = modularConjC X := by
  change tomitaOpC F (modularInvSqrtC F X) = modularConjC X
  rw [tomitaOpC_polar_decomposition, modularSqrtC_comp_inv]

end ComplexTomitaPolar

section RegularRepresentationCommutant

/-- Left regular multiplication action `L_A(X) = A * X` on `M_n(ℂ)`. -/
def leftMulC {n : ℕ} (A X : HSMat n) : HSMat n := A * X

/-- Right regular multiplication action `R_B(X) = X * B` on `M_n(ℂ)`. -/
def rightMulC {n : ℕ} (B X : HSMat n) : HSMat n := X * B

/-- Full left regular representation `{ L_A | A ∈ M_n(ℂ) }`. -/
def leftRegSet (n : ℕ) : Set (HSMat n → HSMat n) :=
  { f | ∃ A : HSMat n, f = leftMulC A }

/-- Full right regular representation `{ R_B | B ∈ M_n(ℂ) }`. -/
def rightRegSet (n : ℕ) : Set (HSMat n → HSMat n) :=
  { f | ∃ B : HSMat n, f = rightMulC B }

/-- `J(X) = Xᴴ` as an `AntiLinearInvolution` on `M_n(ℂ)`. -/
def modularConjInvolution (n : ℕ) : AntiLinearInvolution (HSMat n) where
  toFun := modularConjC
  map_add' := fun X Y => Matrix.conjTranspose_add X Y
  map_smul' := fun c X => Matrix.conjTranspose_smul c X
  involutive' := modularConjC_involutive

@[simp]
theorem modularConjInvolution_apply (n : ℕ) (X : HSMat n) :
    modularConjInvolution n X = Xᴴ :=
  rfl

/-- Every left multiplication commutes with every right multiplication. -/
theorem leftMulC_comm_rightMulC {n : ℕ} (A B X : HSMat n) :
    leftMulC A (rightMulC B X) = rightMulC B (leftMulC A X) := by
  simp [leftMulC, rightMulC, Matrix.mul_assoc]

/-- Commutant of the **full** left regular representation equals the **full** right regular representation:
    `{ L_A | A ∈ M_n(ℂ) }' = { R_B | B ∈ M_n(ℂ) }`. -/
theorem commutant_leftRegSet_eq_rightRegSet (n : ℕ) :
    commutant (leftRegSet n) = rightRegSet n := by
  ext T
  constructor
  · intro hT
    refine ⟨T 1, ?_⟩
    funext X
    have hcommX := hT (leftMulC X) ⟨X, rfl⟩ 1
    calc T X = T (leftMulC X 1) := by simp [leftMulC]
      _ = leftMulC X (T 1) := hcommX
      _ = rightMulC (T 1) X := rfl
  · rintro ⟨B, rfl⟩ f ⟨A, rfl⟩ X
    exact (leftMulC_comm_rightMulC A B X).symm

/-- Commutant of the **full** right regular representation equals the **full** left regular representation. -/
theorem commutant_rightRegSet_eq_leftRegSet (n : ℕ) :
    commutant (rightRegSet n) = leftRegSet n := by
  ext T
  constructor
  · intro hT
    refine ⟨T 1, ?_⟩
    funext X
    have hcommX := hT (rightMulC X) ⟨X, rfl⟩ 1
    calc T X = T (rightMulC X 1) := by simp [rightMulC]
      _ = rightMulC X (T 1) := hcommX
      _ = leftMulC (T 1) X := rfl
  · rintro ⟨A, rfl⟩ f ⟨B, rfl⟩ X
    exact leftMulC_comm_rightMulC A B X

/-- Spatial conjugation `Ad_J(L_A) = R_{Aᴴ}`. -/
theorem AdJ_leftMulC (n : ℕ) (A : HSMat n) :
    AdJ (modularConjInvolution n) (leftMulC A) = rightMulC Aᴴ := by
  funext X
  simp [AdJ, leftMulC, rightMulC, Matrix.conjTranspose_mul]

/-- Spatial conjugation `Ad_J(R_B) = L_{Bᴴ}`. -/
theorem AdJ_rightMulC (n : ℕ) (B : HSMat n) :
    AdJ (modularConjInvolution n) (rightMulC B) = leftMulC Bᴴ := by
  funext X
  simp [AdJ, leftMulC, rightMulC, Matrix.conjTranspose_mul]

/-- `J (leftRegSet n) J = rightRegSet n`. -/
theorem JConjugateSet_leftRegSet_eq_rightRegSet (n : ℕ) :
    JConjugateSet (modularConjInvolution n) (leftRegSet n) = rightRegSet n := by
  ext f
  constructor
  · rintro ⟨g, ⟨A, rfl⟩, rfl⟩
    exact ⟨Aᴴ, AdJ_leftMulC n A⟩
  · rintro ⟨B, rfl⟩
    refine ⟨leftMulC Bᴴ, ⟨Bᴴ, rfl⟩, ?_⟩
    rw [AdJ_leftMulC, Matrix.conjTranspose_conjTranspose]

/-- Constructive inhabitant of `TomitaDualityData` for the full left regular representation of `M_n(ℂ)`. -/
theorem complexMatrixTomitaDualityData (n : ℕ) :
    TomitaDualityData (modularConjInvolution n) (leftRegSet n) where
  forward_commute := by
    rintro f ⟨A, rfl⟩
    rw [AdJ_leftMulC, commutant_leftRegSet_eq_rightRegSet]
    exact ⟨Aᴴ, rfl⟩
  backward_span := by
    intro B hB
    rw [commutant_leftRegSet_eq_rightRegSet] at hB
    rcases hB with ⟨M, rfl⟩
    refine ⟨leftMulC Mᴴ, ⟨Mᴴ, rfl⟩, ?_⟩
    rw [AdJ_leftMulC, Matrix.conjTranspose_conjTranspose]

/-- Constructive inhabitant of `TomitaDualityData` for the commutant `(leftRegSet n)'`. -/
theorem complexMatrixCommutantDualityData (n : ℕ) :
    TomitaDualityData (modularConjInvolution n) (commutant (leftRegSet n)) where
  forward_commute := by
    intro f hf
    rw [commutant_leftRegSet_eq_rightRegSet] at hf ⊢
    rcases hf with ⟨B, rfl⟩
    rw [AdJ_rightMulC, commutant_rightRegSet_eq_leftRegSet]
    exact ⟨Bᴴ, rfl⟩
  backward_span := by
    intro f hf
    rw [commutant_leftRegSet_eq_rightRegSet, commutant_rightRegSet_eq_leftRegSet] at hf
    rcases hf with ⟨A, rfl⟩
    rw [commutant_leftRegSet_eq_rightRegSet]
    refine ⟨rightMulC Aᴴ, ⟨Aᴴ, rfl⟩, ?_⟩
    rw [AdJ_rightMulC, Matrix.conjTranspose_conjTranspose]

/-- Unconditional Tomita–Takesaki commutant duality on `M_n(ℂ)`: `M' = J M J`. -/
theorem complexMatrix_commutant_eq_J_conj (n : ℕ) :
    commutant (leftRegSet n) =
      JConjugateSet (modularConjInvolution n) (leftRegSet n) :=
  tomita_takesaki_commutant_duality (complexMatrixTomitaDualityData n)

/-- Unconditional von Neumann bicommutant theorem on `M_n(ℂ)`: `(M')' = M`. -/
theorem complexMatrix_bicommutant (n : ℕ) :
    commutant (commutant (leftRegSet n)) = leftRegSet n :=
  von_neumann_bicommutant_from_tomita
    (complexMatrixTomitaDualityData n)
    (complexMatrixCommutantDualityData n)

end RegularRepresentationCommutant

end InfoGeometry.Canonical.ComplexMatrixTomitaCommutantDuality
