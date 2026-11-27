/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import Mathlib.Algebra.Ring.Basic
import Mathlib.Algebra.Module.Basic
import Mathlib.Basic.Real.Basic
import Mathlib.Algebra.Algebra.Basic
import Mathlib.Data.Matrix.Basic
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.Tactic

import InfoGeometry.Algebra.PeirceDeWittChiralSplit
import InfoGeometry.Canonical.ComplexMatrixModularFlowAndCStarPolar

namespace InfoGeometry.Algebra.ModularDeWittFlow

set_option linter.unusedSimpArgs false

open InfoGeometry.Algebra.PeirceDeWittChiralSplit

/-!
# Abstract Peirce-scaling specification (not a constructed modular flow)
This section records hypotheses for a map acting on Peirce corners. It does
not construct a flow, assert a group law, or derive the action from a state.
The explicit finite-dimensional inner action is constructed and proved below.
-/

/-- Abstract complementary Peirce idempotent pair on a ring `A`. -/
class PeirceIdempotentSystem (A : Type*) [Ring A] where
  P1 : A
  P2 : A
  hP1 : IsIdempotent P1
  hP2 : IsIdempotent P2
  h_sum : P1 + P2 = 1
  h_ortho12 : P1 * P2 = 0
  h_ortho21 : P2 * P1 = 0

section ModularFlow

variable {A : Type*} [Ring A] [Algebra ℝ A] [S : PeirceIdempotentSystem A]

/-- The diagonal (even) Peirce part in a two-idempotent system. -/
def diagonal (X : A) : A :=
  S.P1 * X * S.P1 + S.P2 * X * S.P2

/-- The off-diagonal (odd) Peirce part in a two-idempotent system. -/
def off_diagonal (X : A) : A :=
  S.P1 * X * S.P2 + S.P2 * X * S.P1

/-- Conditional corner-action data. Its fields are hypotheses, not consequences
of Peirce idempotency or a state-derived Tomita--Takesaki construction. -/
structure PeirceScalingSpecification (a : ℝ) where
  σ : A → A
  -- It is an exact linear map over ℝ
  map_add : ∀ X Y, σ (X + Y) = σ X + σ Y
  map_smul : ∀ (c : ℝ) X, σ (c • X) = c • σ X

  -- The Chiral Idempotents are strictly stationary (Macroscopic Background Independence)
  h_σ_P1 : σ S.P1 = S.P1
  h_σ_P2 : σ S.P2 = S.P2

  -- Action on the Peirce Components:
  -- The Body (diagonal) is stationary
  h_σ_11 : ∀ X, σ (S.P1 * X * S.P1) = S.P1 * X * S.P1
  h_σ_22 : ∀ X, σ (S.P2 * X * S.P2) = S.P2 * X * S.P2

  -- The Soul (off-diagonal) undergoes Loxodromic Scaling (Time Evolution)
  h_σ_12 : ∀ X, σ (S.P1 * X * S.P2) = (algebraMap ℝ A a) * (S.P1 * X * S.P2)
  h_σ_21 : ∀ X, σ (S.P2 * X * S.P1) = (algebraMap ℝ A a⁻¹) * (S.P2 * X * S.P1)

variable (a : ℝ) (mod_flow : PeirceScalingSpecification (A := A) a)

/-!
# Archetype 708: Stationarity of the Classical Body
-/

/-- Under the stated corner-fixing hypotheses, the diagonal part is fixed. -/
theorem body_is_stationary (X : A) :
    mod_flow.σ (diagonal X) = diagonal X := by
  dsimp [diagonal]
  rw [mod_flow.map_add]
  rw [mod_flow.h_σ_11, mod_flow.h_σ_22]

/-!
# Archetype 709: Loxodromic Zitterbewegung of the Soul
-/

/-- Under the stated corner-scaling hypotheses, the two off-diagonal terms
transform with reciprocal scalar weights. -/
theorem soul_evolves (X : A) :
    mod_flow.σ (off_diagonal X) =
      (algebraMap ℝ A a) * (S.P1 * X * S.P2) +
      (algebraMap ℝ A a⁻¹) * (S.P2 * X * S.P1) := by
  dsimp [off_diagonal]
  rw [mod_flow.map_add]
  rw [mod_flow.h_σ_12, mod_flow.h_σ_21]

/-!
# Archetype 710: Covariance of the Dirac Mass Shell
-/

/-- The paired corner product is invariant under the stated reciprocal scaling
hypotheses. This is an algebraic corner identity, not a Dirac mass-shell result. -/
theorem evolved_soul_squared_invariant (ha : a ≠ 0) (X : A) :
    mod_flow.σ (S.P1 * X * S.P2) * mod_flow.σ (S.P2 * X * S.P1) =
      (S.P1 * X * S.P2) * (S.P2 * X * S.P1) := by
  have h_12 : mod_flow.σ (S.P1 * X * S.P2) = (algebraMap ℝ A a) * (S.P1 * X * S.P2) := mod_flow.h_σ_12 X
  have h_21 : mod_flow.σ (S.P2 * X * S.P1) = (algebraMap ℝ A a⁻¹) * (S.P2 * X * S.P1) := mod_flow.h_σ_21 X

  calc mod_flow.σ (S.P1 * X * S.P2) * mod_flow.σ (S.P2 * X * S.P1)
    _ = ((algebraMap ℝ A a) * (S.P1 * X * S.P2)) * ((algebraMap ℝ A a⁻¹) * (S.P2 * X * S.P1)) := by rw [h_12, h_21]
    _ = (algebraMap ℝ A a) * ((S.P1 * X * S.P2) * (algebraMap ℝ A a⁻¹)) * (S.P2 * X * S.P1) := by
        repeat rw [mul_assoc]
    _ = (algebraMap ℝ A a) * ((algebraMap ℝ A a⁻¹) * (S.P1 * X * S.P2)) * (S.P2 * X * S.P1) := by
        have h_comm : ∀ x : A, x * (algebraMap ℝ A a⁻¹) = (algebraMap ℝ A a⁻¹) * x :=
          fun x => (Algebra.commutes _ x).symm
        rw [h_comm (S.P1 * X * S.P2)]
    _ = ((algebraMap ℝ A a) * (algebraMap ℝ A a⁻¹)) * ((S.P1 * X * S.P2) * (S.P2 * X * S.P1)) := by
        simp only [mul_assoc]
    _ = (algebraMap ℝ A (a * a⁻¹)) * ((S.P1 * X * S.P2) * (S.P2 * X * S.P1)) := by rw [← map_mul]
    _ = (algebraMap ℝ A 1) * ((S.P1 * X * S.P2) * (S.P2 * X * S.P1)) := by
        have h_cancel : a * a⁻¹ = 1 := mul_inv_cancel₀ ha
        rw [h_cancel]
    _ = 1 * ((S.P1 * X * S.P2) * (S.P2 * X * S.P1)) := by rw [_root_.map_one]
    _ = (S.P1 * X * S.P2) * (S.P2 * X * S.P1) := one_mul _

end ModularFlow

end InfoGeometry.Algebra.ModularDeWittFlow

/-!
## A concrete finite-dimensional real flow

The generic commutator results above are parity statements, not a
Tomita--Takesaki theorem.  This finite model makes the additional dynamics
explicit: conjugation by `diag(a,1)` fixes diagonal entries and rescales the
two off-diagonal matrix units by reciprocal factors.  The parameter `a` is
required to be nonzero.  No state, KMS condition, or origin of time is inferred.
-/

namespace InfoGeometry.Algebra.ModularDeWittFlow.FiniteMatrix

open Matrix

abbrev M2 := Matrix (Fin 2) (Fin 2) ℝ

/-- The diagonal gauge with eigenvalues `a` and `1`. -/
def gauge (a : ℝ) : M2 := !![a, 0; 0, 1]

/-- The explicit inverse diagonal gauge. -/
noncomputable def gaugeInv (a : ℝ) : M2 := !![a⁻¹, 0; 0, 1]

/-- Inner conjugation by the diagonal gauge. -/
noncomputable def flow (a : ℝ) (X : M2) : M2 := gauge a * X * gaugeInv a

private theorem gauge_mul_gaugeInv (a : ℝ) (ha : a ≠ 0) :
    gauge a * gaugeInv a = (1 : M2) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [gauge, gaugeInv, Matrix.mul_apply, Fin.sum_univ_two, mul_inv_cancel₀ ha]

private theorem gaugeInv_mul_gauge (a : ℝ) (ha : a ≠ 0) :
    gaugeInv a * gauge a = (1 : M2) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [gauge, gaugeInv, Matrix.mul_apply, Fin.sum_univ_two, inv_mul_cancel₀ ha]

/-- Entrywise formula for the finite inner flow. -/
theorem flow_entries (a : ℝ) (ha : a ≠ 0) (X : M2) :
    flow a X = !![X 0 0, a * X 0 1; a⁻¹ * X 1 0, X 1 1] := by
  ext i j
  fin_cases i <;> fin_cases j
  · dsimp [flow, gauge, gaugeInv]
    simp [Matrix.mul_apply, Matrix.vecMul, dotProduct, Fin.sum_univ_two]
    calc a * X 0 0 * a⁻¹ = X 0 0 * (a * a⁻¹) := by ring
    _ = X 0 0 * 1 := by rw [mul_inv_cancel₀ ha]
    _ = X 0 0 := by ring
  · dsimp [flow, gauge, gaugeInv]
    simp [Matrix.mul_apply, Matrix.vecMul, dotProduct, Fin.sum_univ_two]
  · dsimp [flow, gauge, gaugeInv]
    simp [Matrix.mul_apply, Matrix.vecMul, dotProduct, Fin.sum_univ_two]
    ring
  · dsimp [flow, gauge, gaugeInv]
    simp [Matrix.mul_apply, Matrix.vecMul, dotProduct, Fin.sum_univ_two]

/-- The diagonal (even) matrix part is fixed by the gauge flow. -/
theorem flow_diagonal_part (a : ℝ) (ha : a ≠ 0) (x y : ℝ) :
    flow a (!![x, 0; 0, y] : M2) = !![x, 0; 0, y] := by
  rw [flow_entries a ha]
  simp

/-- The `0 → 1` matrix unit has weight `a`. -/
theorem flow_upper_matrix_unit (a : ℝ) (ha : a ≠ 0) :
    flow a (!![0, 1; 0, 0] : M2) = !![0, a; 0, 0] := by
  rw [flow_entries a ha]
  simp

/-- The `1 → 0` matrix unit has the reciprocal weight. -/
theorem flow_lower_matrix_unit (a : ℝ) (ha : a ≠ 0) :
    flow a (!![0, 0; 1, 0] : M2) = !![0, 0; a⁻¹, 0] := by
  rw [flow_entries a ha]
  simp

/-- Conjugation by the gauge respects multiplication. -/
theorem flow_mul (a : ℝ) (ha : a ≠ 0) (X Y : M2) :
    flow a (X * Y) = flow a X * flow a Y := by
  dsimp [flow]
  calc
    gauge a * (X * Y) * gaugeInv a = gauge a * X * 1 * Y * gaugeInv a := by simp [mul_assoc]
    _ = gauge a * X * (gaugeInv a * gauge a) * Y * gaugeInv a := by rw [gaugeInv_mul_gauge a ha]
    _ = (gauge a * X * gaugeInv a) * (gauge a * Y * gaugeInv a) := by simp [mul_assoc]

/-- Successive gauge flows compose by multiplying their parameters. -/
theorem flow_comp (a b : ℝ) (ha : a ≠ 0) (hb : b ≠ 0) (X : M2) :
    flow a (flow b X) = flow (a * b) X := by
  rw [flow_entries a ha, flow_entries b hb, flow_entries (a * b) (mul_ne_zero ha hb)]
  ext i j; fin_cases i <;> fin_cases j <;> simp <;> ring

/-- Explicit noncommuting generators on `M2 = Matrix (Fin 2) (Fin 2) ℝ`. -/
def matA : M2 := !![0, 1; 0, 0]

/-- Explicit lower-triangular noncommuting generator on `M2 = Matrix (Fin 2) (Fin 2) ℝ`. -/
def matB : M2 := !![0, 0; 1, 0]

/-- Explicit noncommutativity witness on `M2 = Matrix (Fin 2) (Fin 2) ℝ` (Trap T16). -/
theorem finiteMatrix_noncomm_witness :
    matA * matB ≠ matB * matA := by
  intro h
  have h00 := congrArg (fun M : M2 => M 0 0) h
  simp [matA, matB, Matrix.mul_apply, Fin.sum_univ_two] at h00

/-- Real `2×2` Peirce idempotent instance on `M2 = Matrix (Fin 2) (Fin 2) ℝ`. -/
instance instPeirceIdempotentSystemM2 :
    InfoGeometry.Algebra.ModularDeWittFlow.PeirceIdempotentSystem M2 where
  P1 := !![1, 0; 0, 0]
  P2 := !![0, 0; 0, 1]
  hP1 := by
    change (!![1, 0; 0, 0] : M2) * !![1, 0; 0, 0] = !![1, 0; 0, 0]
    ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]
  hP2 := by
    change (!![0, 0; 0, 1] : M2) * !![0, 0; 0, 1] = !![0, 0; 0, 1]
    ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]
  h_sum := by
    ext i j; fin_cases i <;> fin_cases j <;> simp
  h_ortho12 := by
    ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]
  h_ortho21 := by
    ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]

/-- Constructive `PeirceScalingSpecification` on `M2` realized by `FiniteMatrix.flow a`. -/
noncomputable def finiteMatrixPeirceScalingSpec (a : ℝ) (ha : a ≠ 0) :
    InfoGeometry.Algebra.ModularDeWittFlow.PeirceScalingSpecification (A := M2) a where
  σ := flow a
  map_add X Y := by
    dsimp [flow]
    rw [Matrix.mul_add, Matrix.add_mul]
  map_smul c X := by
    dsimp [flow]
    rw [Algebra.mul_smul_comm, Algebra.smul_mul_assoc]
  h_σ_P1 := by
    change flow a !![1, 0; 0, 0] = !![1, 0; 0, 0]
    rw [flow_entries a ha]
    simp
  h_σ_P2 := by
    change flow a !![0, 0; 0, 1] = !![0, 0; 0, 1]
    rw [flow_entries a ha]
    simp
  h_σ_11 X := by
    have h11 : (!![1, 0; 0, 0] : M2) * X * !![1, 0; 0, 0] = !![X 0 0, 0; 0, 0] := by
      ext i j; fin_cases i <;> fin_cases j <;>
        simp [Matrix.mul_apply, Matrix.vecMul_apply, dotProduct, Fin.sum_univ_two]
    change flow a ((!![1, 0; 0, 0] : M2) * X * !![1, 0; 0, 0]) =
      (!![1, 0; 0, 0] : M2) * X * !![1, 0; 0, 0]
    rw [h11, flow_entries a ha]
    ext i j; fin_cases i <;> fin_cases j <;> simp
  h_σ_22 X := by
    have h22 : (!![0, 0; 0, 1] : M2) * X * !![0, 0; 0, 1] = !![0, 0; 0, X 1 1] := by
      ext i j; fin_cases i <;> fin_cases j <;>
        simp [Matrix.mul_apply, Matrix.vecMul_apply, dotProduct, Fin.sum_univ_two]
    change flow a ((!![0, 0; 0, 1] : M2) * X * !![0, 0; 0, 1]) =
      (!![0, 0; 0, 1] : M2) * X * !![0, 0; 0, 1]
    rw [h22, flow_entries a ha]
    ext i j; fin_cases i <;> fin_cases j <;> simp
  h_σ_12 X := by
    have h12 : (!![1, 0; 0, 0] : M2) * X * !![0, 0; 0, 1] = !![0, X 0 1; 0, 0] := by
      ext i j; fin_cases i <;> fin_cases j <;>
        simp [Matrix.mul_apply, Matrix.vecMul_apply, dotProduct, Fin.sum_univ_two]
    change flow a ((!![1, 0; 0, 0] : M2) * X * !![0, 0; 0, 1]) =
      algebraMap ℝ M2 a * ((!![1, 0; 0, 0] : M2) * X * !![0, 0; 0, 1])
    rw [h12, flow_entries a ha, Algebra.algebraMap_eq_smul_one]
    ext i j; fin_cases i <;> fin_cases j <;> simp
  h_σ_21 X := by
    have h21 : (!![0, 0; 0, 1] : M2) * X * !![1, 0; 0, 0] = !![0, 0; X 1 0, 0] := by
      ext i j; fin_cases i <;> fin_cases j <;>
        simp [Matrix.mul_apply, Matrix.vecMul_apply, dotProduct, Fin.sum_univ_two]
    change flow a ((!![0, 0; 0, 1] : M2) * X * !![1, 0; 0, 0]) =
      algebraMap ℝ M2 a⁻¹ * ((!![0, 0; 0, 1] : M2) * X * !![1, 0; 0, 0])
    rw [h21, flow_entries a ha, Algebra.algebraMap_eq_smul_one]
    ext i j; fin_cases i <;> fin_cases j <;> simp

end InfoGeometry.Algebra.ModularDeWittFlow.FiniteMatrix

/-!
## Constructive Dynamic Gibbs Peirce-Scaling & Modular Flow on `Matrix (Fin (m + k)) (Fin (m + k)) ℂ`
-/

namespace InfoGeometry.Algebra.ModularDeWittFlow.DynamicGibbs

open Matrix Complex
open scoped Matrix.Norms.L2Operator
open InfoGeometry.Algebra.ModularDeWittFlow
open InfoGeometry.Canonical.ComplexMatrixModularFlowAndCStarPolar

section BlockPeirce

/-- Upper-left block projector `P1 = fromBlocks 1 0 0 0` reindexed to `Fin (m + k)`. -/
def blockP1 (m k : ℕ) : Matrix (Fin (m + k)) (Fin (m + k)) ℂ :=
  Matrix.reindex finSumFinEquiv finSumFinEquiv (Matrix.fromBlocks (1 : Matrix (Fin m) (Fin m) ℂ) 0 0 0)

/-- Lower-right block projector `P2 = fromBlocks 0 0 0 1` reindexed to `Fin (m + k)`. -/
def blockP2 (m k : ℕ) : Matrix (Fin (m + k)) (Fin (m + k)) ℂ :=
  Matrix.reindex finSumFinEquiv finSumFinEquiv (Matrix.fromBlocks 0 0 0 (1 : Matrix (Fin k) (Fin k) ℂ))

private theorem reindex_mul_self (m k : ℕ)
    (A B : Matrix (Fin m ⊕ Fin k) (Fin m ⊕ Fin k) ℂ) :
    Matrix.reindex finSumFinEquiv finSumFinEquiv A *
        Matrix.reindex finSumFinEquiv finSumFinEquiv B =
      Matrix.reindex finSumFinEquiv finSumFinEquiv (A * B) := by
  ext i j
  simp only [Matrix.mul_apply, Matrix.reindex_apply]
  let e := finSumFinEquiv (m := m) (n := k)
  exact (Fintype.sum_equiv (M := ℂ) e
    (fun x : Fin m ⊕ Fin k =>
      A (e.symm i) x * B x (e.symm j))
    (fun y : Fin (m + k) =>
      A (e.symm i) (e.symm y) * B (e.symm y) (e.symm j))
    (fun x => by simp)).symm

private theorem reindex_add_self (m k : ℕ)
    (A B : Matrix (Fin m ⊕ Fin k) (Fin m ⊕ Fin k) ℂ) :
    Matrix.reindex finSumFinEquiv finSumFinEquiv (A + B) =
      Matrix.reindex finSumFinEquiv finSumFinEquiv A +
        Matrix.reindex finSumFinEquiv finSumFinEquiv B := by
  ext i j; rfl

private theorem reindex_smul_self (m k : ℕ) (c : ℂ)
    (A : Matrix (Fin m ⊕ Fin k) (Fin m ⊕ Fin k) ℂ) :
    Matrix.reindex finSumFinEquiv finSumFinEquiv (c • A) =
      c • Matrix.reindex finSumFinEquiv finSumFinEquiv A := by
  ext i j; rfl

private theorem reindex_conjTranspose_self (m k : ℕ)
    (A : Matrix (Fin m ⊕ Fin k) (Fin m ⊕ Fin k) ℂ) :
    (Matrix.reindex finSumFinEquiv finSumFinEquiv A)ᴴ =
      Matrix.reindex finSumFinEquiv finSumFinEquiv Aᴴ := by
  ext i j; rfl

/-- Constructive `PeirceIdempotentSystem` on `Matrix (Fin (m + k)) (Fin (m + k)) ℂ`
(and on `Fin 2` via `m = 1, k = 1`). -/
instance instPeirceIdempotentSystemBlock (m k : ℕ) :
    PeirceIdempotentSystem (Matrix (Fin (m + k)) (Fin (m + k)) ℂ) where
  P1 := blockP1 m k
  P2 := blockP2 m k
  hP1 := by
    change blockP1 m k * blockP1 m k = blockP1 m k
    unfold blockP1
    rw [reindex_mul_self, Matrix.fromBlocks_multiply]
    simp
  hP2 := by
    change blockP2 m k * blockP2 m k = blockP2 m k
    unfold blockP2
    rw [reindex_mul_self, Matrix.fromBlocks_multiply]
    simp
  h_sum := by
    unfold blockP1 blockP2
    rw [← reindex_add_self, Matrix.fromBlocks_add]
    ext i j
    simp [Matrix.reindex_apply, Matrix.one_apply]
  h_ortho12 := by
    unfold blockP1 blockP2
    rw [reindex_mul_self, Matrix.fromBlocks_multiply]
    simp
  h_ortho21 := by
    unfold blockP1 blockP2
    rw [reindex_mul_self, Matrix.fromBlocks_multiply]
    simp

private theorem finSum11_symm_0 :
    (finSumFinEquiv (m := 1) (n := 1)).symm 0 = Sum.inl 0 := by decide

private theorem finSum11_symm_1 :
    (finSumFinEquiv (m := 1) (n := 1)).symm 1 = Sum.inr 0 := by decide

theorem blockP1_one_one : blockP1 1 1 = !![1, 0; 0, 0] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [blockP1, Matrix.reindex_apply, finSum11_symm_0, finSum11_symm_1]

theorem blockP2_one_one : blockP2 1 1 = !![0, 0; 0, 1] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [blockP2, Matrix.reindex_apply, finSum11_symm_0, finSum11_symm_1]

theorem blockP1_conjTranspose (m k : ℕ) : (blockP1 m k)ᴴ = blockP1 m k := by
  unfold blockP1
  rw [reindex_conjTranspose_self, Matrix.fromBlocks_conjTranspose]
  simp

theorem blockP2_conjTranspose (m k : ℕ) : (blockP2 m k)ᴴ = blockP2 m k := by
  unfold blockP2
  rw [reindex_conjTranspose_self, Matrix.fromBlocks_conjTranspose]
  simp

/-- Two-level block-scalar Hamiltonian `H(E₀, E₁) = E₀ • P1 + E₁ • P2`. -/
def gibbsTwoLevelH (m k : ℕ) (E₀ E₁ : ℝ) : Matrix (Fin (m + k)) (Fin (m + k)) ℂ :=
  (E₀ : ℂ) • blockP1 m k + (E₁ : ℂ) • blockP2 m k

theorem gibbsTwoLevelH_eq_fromBlocks (m k : ℕ) (E₀ E₁ : ℝ) :
    gibbsTwoLevelH m k E₀ E₁ =
      Matrix.reindex finSumFinEquiv finSumFinEquiv
        (Matrix.fromBlocks ((E₀ : ℂ) • (1 : Matrix (Fin m) (Fin m) ℂ)) 0 0
          ((E₁ : ℂ) • (1 : Matrix (Fin k) (Fin k) ℂ))) := by
  unfold gibbsTwoLevelH blockP1 blockP2
  rw [← reindex_smul_self, ← reindex_smul_self, ← reindex_add_self]
  congr 1
  ext (i | i) (j | j) <;> simp

theorem gibbsTwoLevelH_isHermitian (m k : ℕ) (E₀ E₁ : ℝ) :
    (gibbsTwoLevelH m k E₀ E₁).IsHermitian := by
  change (gibbsTwoLevelH m k E₀ E₁)ᴴ = gibbsTwoLevelH m k E₀ E₁
  unfold gibbsTwoLevelH
  rw [Matrix.conjTranspose_add, Matrix.conjTranspose_smul, Matrix.conjTranspose_smul,
    blockP1_conjTranspose, blockP2_conjTranspose]
  simp

/-- Algebra homomorphism `(ℂ × ℂ) →ₐ[ℂ] M_{m+k}(ℂ)` sending `(z₀, z₁) ↦ z₀ • P1 + z₁ • P2`. -/
def peircePairAlgHom (m k : ℕ) :
    (ℂ × ℂ) →ₐ[ℂ] Matrix (Fin (m + k)) (Fin (m + k)) ℂ where
  toFun z := z.1 • blockP1 m k + z.2 • blockP2 m k
  map_one' := by
    change (1 : ℂ) • blockP1 m k + (1 : ℂ) • blockP2 m k = 1
    rw [one_smul, one_smul]
    exact (instPeirceIdempotentSystemBlock m k).h_sum
  map_mul' z w := by
    let S := instPeirceIdempotentSystemBlock m k
    have h11 : blockP1 m k * blockP1 m k = blockP1 m k := S.hP1
    have h22 : blockP2 m k * blockP2 m k = blockP2 m k := S.hP2
    have h12 : blockP1 m k * blockP2 m k = 0 := S.h_ortho12
    have h21 : blockP2 m k * blockP1 m k = 0 := S.h_ortho21
    calc
      (z.1 * w.1) • blockP1 m k + (z.2 * w.2) • blockP2 m k
          = (z.1 * w.1) • (blockP1 m k * blockP1 m k) +
              (z.1 * w.2) • (blockP1 m k * blockP2 m k) +
              (z.2 * w.1) • (blockP2 m k * blockP1 m k) +
              (z.2 * w.2) • (blockP2 m k * blockP2 m k) := by
            rw [h11, h22, h12, h21, smul_zero, smul_zero, add_zero, add_zero]
      _ = (z.1 • blockP1 m k + z.2 • blockP2 m k) *
            (w.1 • blockP1 m k + w.2 • blockP2 m k) := by
            rw [add_mul, mul_add, mul_add, smul_mul_smul_comm, smul_mul_smul_comm,
              smul_mul_smul_comm, smul_mul_smul_comm]
            abel
  map_zero' := by simp
  map_add' z w := by
    simp only [Prod.fst_add, Prod.snd_add, add_smul]
    abel
  commutes' c := by
    change c • blockP1 m k + c • blockP2 m k = algebraMap ℂ _ c
    have hsum : blockP1 m k + blockP2 m k = 1 := (instPeirceIdempotentSystemBlock m k).h_sum
    rw [← smul_add, hsum, Algebra.algebraMap_eq_smul_one]

private theorem exp_prod_complex (z₀ z₁ : ℂ) :
    NormedSpace.exp (z₀, z₁) = (Complex.exp z₀, Complex.exp z₁) := by
  let _ : NormedAlgebra ℚ (ℂ × ℂ) := NormedAlgebra.restrictScalars ℚ ℂ (ℂ × ℂ)
  rw [Prod.ext_iff]
  constructor
  · have h1 := NormedSpace.map_exp (AlgHom.fst ℂ ℂ ℂ) continuous_fst (z₀, z₁)
    change (NormedSpace.exp (z₀, z₁)).1 = NormedSpace.exp z₀ at h1
    rw [h1, congrFun Complex.exp_eq_exp_ℂ z₀]
  · have h2 := NormedSpace.map_exp (AlgHom.snd ℂ ℂ ℂ) continuous_snd (z₀, z₁)
    change (NormedSpace.exp (z₀, z₁)).2 = NormedSpace.exp z₁ at h2
    rw [h2, congrFun Complex.exp_eq_exp_ℂ z₁]

/-- Exact exponential of a Peirce two-level combination:
`exp(z₀ • P1 + z₁ • P2) = exp(z₀) • P1 + exp(z₁) • P2`. -/
theorem exp_peirceLinearCombo (m k : ℕ) (z₀ z₁ : ℂ) :
    NormedSpace.exp (z₀ • blockP1 m k + z₁ • blockP2 m k) =
      Complex.exp z₀ • blockP1 m k + Complex.exp z₁ • blockP2 m k := by
  let _ : NormedAlgebra ℚ (ℂ × ℂ) := NormedAlgebra.restrictScalars ℚ ℂ (ℂ × ℂ)
  let _ : NormedAlgebra ℚ (Matrix (Fin (m + k)) (Fin (m + k)) ℂ) :=
    NormedAlgebra.restrictScalars ℚ ℂ _
  have hcont : Continuous (peircePairAlgHom m k) :=
    (peircePairAlgHom m k).toLinearMap.continuous_of_finiteDimensional
  have hmap := NormedSpace.map_exp (peircePairAlgHom m k) hcont (z₀, z₁)
  rw [exp_prod_complex] at hmap
  exact hmap.symm

theorem gibbsDensity_gibbsTwoLevelH (m k : ℕ) (E₀ E₁ : ℝ) :
    gibbsDensity (gibbsTwoLevelH m k E₀ E₁) =
      Complex.exp (-(E₀ : ℂ)) • blockP1 m k + Complex.exp (-(E₁ : ℂ)) • blockP2 m k := by
  unfold gibbsDensity gibbsTwoLevelH
  rw [neg_add, ← neg_smul, ← neg_smul]
  exact exp_peirceLinearCombo m k (-(E₀ : ℂ)) (-(E₁ : ℂ))

theorem gibbsDensityInv_gibbsTwoLevelH (m k : ℕ) (E₀ E₁ : ℝ) :
    gibbsDensityInv (gibbsTwoLevelH m k E₀ E₁) =
      Complex.exp (E₀ : ℂ) • blockP1 m k + Complex.exp (E₁ : ℂ) • blockP2 m k := by
  unfold gibbsDensityInv gibbsTwoLevelH
  exact exp_peirceLinearCombo m k (E₀ : ℂ) (E₁ : ℂ)

theorem uExp_gibbsTwoLevelH (m k : ℕ) (E₀ E₁ : ℝ) (t : ℝ) :
    uExp (gibbsTwoLevelH m k E₀ E₁) t =
      Complex.exp (Complex.I * (t : ℂ) * (E₀ : ℂ)) • blockP1 m k +
        Complex.exp (Complex.I * (t : ℂ) * (E₁ : ℂ)) • blockP2 m k := by
  unfold uExp gibbsTwoLevelH
  rw [smul_add, smul_smul, smul_smul]
  exact exp_peirceLinearCombo m k (Complex.I * (t : ℂ) * (E₀ : ℂ))
    (Complex.I * (t : ℂ) * (E₁ : ℂ))

private theorem peirce_conj_formula (m k : ℕ) (a₀ a₁ b₀ b₁ : ℂ)
    (X : Matrix (Fin (m + k)) (Fin (m + k)) ℂ) :
    (a₀ • blockP1 m k + a₁ • blockP2 m k) * X * (b₀ • blockP1 m k + b₁ • blockP2 m k) =
      (a₀ * b₀) • (blockP1 m k * X * blockP1 m k) +
      (a₀ * b₁) • (blockP1 m k * X * blockP2 m k) +
      (a₁ * b₀) • (blockP2 m k * X * blockP1 m k) +
      (a₁ * b₁) • (blockP2 m k * X * blockP2 m k) := by
  simp only [add_mul, mul_add, smul_add, smul_mul_assoc, mul_smul_comm, smul_smul]
  rw [mul_comm b₀ a₀, mul_comm b₀ a₁, mul_comm b₁ a₀, mul_comm b₁ a₁]
  abel

private theorem blockP1_sandwich_corners (m k : ℕ)
    (X : Matrix (Fin (m + k)) (Fin (m + k)) ℂ) :
    blockP1 m k * (blockP1 m k * X * blockP1 m k) * blockP1 m k = blockP1 m k * X * blockP1 m k ∧
    blockP1 m k * (blockP1 m k * X * blockP1 m k) * blockP2 m k = 0 ∧
    blockP2 m k * (blockP1 m k * X * blockP1 m k) * blockP1 m k = 0 ∧
    blockP2 m k * (blockP1 m k * X * blockP1 m k) * blockP2 m k = 0 := by
  let S := instPeirceIdempotentSystemBlock m k
  have h11 : blockP1 m k * blockP1 m k = blockP1 m k := S.hP1
  have h12 : blockP1 m k * blockP2 m k = 0 := S.h_ortho12
  have h21 : blockP2 m k * blockP1 m k = 0 := S.h_ortho21
  refine ⟨?_, ?_, ?_, ?_⟩
  · simp only [Matrix.mul_assoc, h11]; simp only [← Matrix.mul_assoc, h11]
  · simp only [Matrix.mul_assoc, h12, Matrix.mul_zero]
  · simp only [← Matrix.mul_assoc, h21, Matrix.zero_mul]
  · simp only [Matrix.mul_assoc, h12, Matrix.mul_zero]

private theorem blockP2_sandwich_corners (m k : ℕ)
    (X : Matrix (Fin (m + k)) (Fin (m + k)) ℂ) :
    blockP1 m k * (blockP2 m k * X * blockP2 m k) * blockP1 m k = 0 ∧
    blockP1 m k * (blockP2 m k * X * blockP2 m k) * blockP2 m k = 0 ∧
    blockP2 m k * (blockP2 m k * X * blockP2 m k) * blockP1 m k = 0 ∧
    blockP2 m k * (blockP2 m k * X * blockP2 m k) * blockP2 m k = blockP2 m k * X * blockP2 m k := by
  let S := instPeirceIdempotentSystemBlock m k
  have h22 : blockP2 m k * blockP2 m k = blockP2 m k := S.hP2
  have h12 : blockP1 m k * blockP2 m k = 0 := S.h_ortho12
  have h21 : blockP2 m k * blockP1 m k = 0 := S.h_ortho21
  refine ⟨?_, ?_, ?_, ?_⟩
  · simp only [Matrix.mul_assoc, h21, Matrix.mul_zero]
  · simp only [← Matrix.mul_assoc, h12, Matrix.zero_mul]
  · simp only [Matrix.mul_assoc, h21, Matrix.mul_zero]
  · simp only [Matrix.mul_assoc, h22]; simp only [← Matrix.mul_assoc, h22]

private theorem blockP12_sandwich_corners (m k : ℕ)
    (X : Matrix (Fin (m + k)) (Fin (m + k)) ℂ) :
    blockP1 m k * (blockP1 m k * X * blockP2 m k) * blockP1 m k = 0 ∧
    blockP1 m k * (blockP1 m k * X * blockP2 m k) * blockP2 m k = blockP1 m k * X * blockP2 m k ∧
    blockP2 m k * (blockP1 m k * X * blockP2 m k) * blockP1 m k = 0 ∧
    blockP2 m k * (blockP1 m k * X * blockP2 m k) * blockP2 m k = 0 := by
  let S := instPeirceIdempotentSystemBlock m k
  have h11 : blockP1 m k * blockP1 m k = blockP1 m k := S.hP1
  have h22 : blockP2 m k * blockP2 m k = blockP2 m k := S.hP2
  have h12 : blockP1 m k * blockP2 m k = 0 := S.h_ortho12
  have h21 : blockP2 m k * blockP1 m k = 0 := S.h_ortho21
  refine ⟨?_, ?_, ?_, ?_⟩
  · simp only [Matrix.mul_assoc, h21, Matrix.mul_zero]
  · simp only [Matrix.mul_assoc, h22]; simp only [← Matrix.mul_assoc, h11]
  · simp only [← Matrix.mul_assoc, h21, Matrix.zero_mul]
  · simp only [← Matrix.mul_assoc, h21, Matrix.zero_mul]

private theorem blockP21_sandwich_corners (m k : ℕ)
    (X : Matrix (Fin (m + k)) (Fin (m + k)) ℂ) :
    blockP1 m k * (blockP2 m k * X * blockP1 m k) * blockP1 m k = 0 ∧
    blockP1 m k * (blockP2 m k * X * blockP1 m k) * blockP2 m k = 0 ∧
    blockP2 m k * (blockP2 m k * X * blockP1 m k) * blockP1 m k = blockP2 m k * X * blockP1 m k ∧
    blockP2 m k * (blockP2 m k * X * blockP1 m k) * blockP2 m k = 0 := by
  let S := instPeirceIdempotentSystemBlock m k
  have h11 : blockP1 m k * blockP1 m k = blockP1 m k := S.hP1
  have h22 : blockP2 m k * blockP2 m k = blockP2 m k := S.hP2
  have h12 : blockP1 m k * blockP2 m k = 0 := S.h_ortho12
  have h21 : blockP2 m k * blockP1 m k = 0 := S.h_ortho21
  refine ⟨?_, ?_, ?_, ?_⟩
  · simp only [← Matrix.mul_assoc, h12, Matrix.zero_mul]
  · simp only [← Matrix.mul_assoc, h12, Matrix.zero_mul]
  · simp only [Matrix.mul_assoc, h11]; simp only [← Matrix.mul_assoc, h22]
  · simp only [Matrix.mul_assoc, h12, Matrix.mul_zero]

/-- **Constructive dynamic Gibbs inhabitant** of `PeirceScalingSpecification` with scaling
parameter `a = Real.exp (-(E₀ - E₁))` and `σ X = exp(-H) * X * exp(H)`, with zero
uninstantiated hypotheses. -/
noncomputable def gibbsPeirceScalingSpec (m k : ℕ) (E₀ E₁ : ℝ) :
    PeirceScalingSpecification (A := Matrix (Fin (m + k)) (Fin (m + k)) ℂ)
      (Real.exp (-(E₀ - E₁))) where
  σ X := gibbsDensity (gibbsTwoLevelH m k E₀ E₁) * X *
    gibbsDensityInv (gibbsTwoLevelH m k E₀ E₁)
  map_add X Y := by
    rw [Matrix.mul_add, Matrix.add_mul]
  map_smul c X := by
    rw [Algebra.mul_smul_comm, Algebra.smul_mul_assoc]
  h_σ_P1 := by
    let S := instPeirceIdempotentSystemBlock m k
    change gibbsDensity (gibbsTwoLevelH m k E₀ E₁) * blockP1 m k *
      gibbsDensityInv (gibbsTwoLevelH m k E₀ E₁) = blockP1 m k
    rw [gibbsDensity_gibbsTwoLevelH, gibbsDensityInv_gibbsTwoLevelH]
    have h11 : blockP1 m k * blockP1 m k = blockP1 m k := S.hP1
    have h12 : blockP1 m k * blockP2 m k = 0 := S.h_ortho12
    have h21 : blockP2 m k * blockP1 m k = 0 := S.h_ortho21
    rw [add_mul, smul_mul_assoc, smul_mul_assoc, h11, h21, smul_zero, add_zero,
      mul_add, mul_smul_comm, mul_smul_comm, smul_mul_assoc, smul_mul_assoc,
      h11, h12, smul_zero, smul_zero, add_zero, smul_smul, ← Complex.exp_add,
      add_neg_cancel, Complex.exp_zero, one_smul]
  h_σ_P2 := by
    let S := instPeirceIdempotentSystemBlock m k
    change gibbsDensity (gibbsTwoLevelH m k E₀ E₁) * blockP2 m k *
      gibbsDensityInv (gibbsTwoLevelH m k E₀ E₁) = blockP2 m k
    rw [gibbsDensity_gibbsTwoLevelH, gibbsDensityInv_gibbsTwoLevelH]
    have h22 : blockP2 m k * blockP2 m k = blockP2 m k := S.hP2
    have h12 : blockP1 m k * blockP2 m k = 0 := S.h_ortho12
    have h21 : blockP2 m k * blockP1 m k = 0 := S.h_ortho21
    rw [add_mul, smul_mul_assoc, smul_mul_assoc, h12, h22, smul_zero, zero_add,
      mul_add, mul_smul_comm, mul_smul_comm, smul_mul_assoc, smul_mul_assoc,
      h21, h22, smul_zero, smul_zero, zero_add, smul_smul, ← Complex.exp_add,
      add_neg_cancel, Complex.exp_zero, one_smul]
  h_σ_11 X := by
    change gibbsDensity (gibbsTwoLevelH m k E₀ E₁) * (blockP1 m k * X * blockP1 m k) *
      gibbsDensityInv (gibbsTwoLevelH m k E₀ E₁) = blockP1 m k * X * blockP1 m k
    rw [gibbsDensity_gibbsTwoLevelH, gibbsDensityInv_gibbsTwoLevelH, peirce_conj_formula]
    obtain ⟨c11, c12, c21, c22⟩ := blockP1_sandwich_corners m k X
    rw [c11, c12, c21, c22, smul_zero, smul_zero, smul_zero, add_zero, add_zero, add_zero,
      ← Complex.exp_add, neg_add_cancel, Complex.exp_zero, one_smul]
  h_σ_22 X := by
    change gibbsDensity (gibbsTwoLevelH m k E₀ E₁) * (blockP2 m k * X * blockP2 m k) *
      gibbsDensityInv (gibbsTwoLevelH m k E₀ E₁) = blockP2 m k * X * blockP2 m k
    rw [gibbsDensity_gibbsTwoLevelH, gibbsDensityInv_gibbsTwoLevelH, peirce_conj_formula]
    obtain ⟨c11, c12, c21, c22⟩ := blockP2_sandwich_corners m k X
    rw [c11, c12, c21, c22, smul_zero, smul_zero, smul_zero, zero_add, zero_add, zero_add,
      ← Complex.exp_add, neg_add_cancel, Complex.exp_zero, one_smul]
  h_σ_12 X := by
    change gibbsDensity (gibbsTwoLevelH m k E₀ E₁) * (blockP1 m k * X * blockP2 m k) *
      gibbsDensityInv (gibbsTwoLevelH m k E₀ E₁) =
        algebraMap ℝ _ (Real.exp (-(E₀ - E₁))) * (blockP1 m k * X * blockP2 m k)
    rw [gibbsDensity_gibbsTwoLevelH, gibbsDensityInv_gibbsTwoLevelH, peirce_conj_formula]
    obtain ⟨c11, c12, c21, c22⟩ := blockP12_sandwich_corners m k X
    rw [c11, c12, c21, c22, smul_zero, smul_zero, smul_zero, zero_add, add_zero, add_zero,
      ← Complex.exp_add]
    have harg : -(E₀ : ℂ) + (E₁ : ℂ) = ((-(E₀ - E₁) : ℝ) : ℂ) := by
      push_cast; abel
    rw [harg, ← Complex.ofReal_exp, Algebra.smul_def]
    rfl
  h_σ_21 X := by
    change gibbsDensity (gibbsTwoLevelH m k E₀ E₁) * (blockP2 m k * X * blockP1 m k) *
      gibbsDensityInv (gibbsTwoLevelH m k E₀ E₁) =
        algebraMap ℝ _ (Real.exp (-(E₀ - E₁)))⁻¹ * (blockP2 m k * X * blockP1 m k)
    rw [gibbsDensity_gibbsTwoLevelH, gibbsDensityInv_gibbsTwoLevelH, peirce_conj_formula]
    obtain ⟨c11, c12, c21, c22⟩ := blockP21_sandwich_corners m k X
    rw [c11, c12, c21, c22, smul_zero, smul_zero, smul_zero, zero_add, zero_add, add_zero,
      ← Complex.exp_add]
    have harg : -(E₁ : ℂ) + (E₀ : ℂ) = ((-( -(E₀ - E₁)) : ℝ) : ℂ) := by
      push_cast; abel
    rw [harg, ← Complex.ofReal_exp, Real.exp_neg, Algebra.smul_def]
    rfl

/-- Connection between `FiniteMatrix.flow` on `M₂(ℝ)` and the constructive dynamic Gibbs
`PeirceScalingSpecification` on `M₂(ℂ)`. -/
theorem finiteMatrix_flow_eq_gibbsPeirce (E₀ E₁ : ℝ) (X : InfoGeometry.Algebra.ModularDeWittFlow.FiniteMatrix.M2) :
    (InfoGeometry.Algebra.ModularDeWittFlow.FiniteMatrix.flow (Real.exp (-(E₀ - E₁))) X).map
        Complex.ofReal =
      (gibbsPeirceScalingSpec 1 1 E₀ E₁).σ (X.map Complex.ofReal) := by
  have ha : Real.exp (-(E₀ - E₁)) ≠ 0 := Real.exp_ne_zero _
  rw [InfoGeometry.Algebra.ModularDeWittFlow.FiniteMatrix.flow_entries _ ha]
  change (!![X 0 0, Real.exp (-(E₀ - E₁)) * X 0 1;
      (Real.exp (-(E₀ - E₁)))⁻¹ * X 1 0, X 1 1]).map Complex.ofReal =
    gibbsDensity (gibbsTwoLevelH 1 1 E₀ E₁) * X.map Complex.ofReal *
      gibbsDensityInv (gibbsTwoLevelH 1 1 E₀ E₁)
  rw [gibbsDensity_gibbsTwoLevelH, gibbsDensityInv_gibbsTwoLevelH, blockP1_one_one, blockP2_one_one]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Matrix.vecMul_apply, dotProduct, Fin.sum_univ_two]
  · rw [mul_comm _ (X 0 0 : ℂ), mul_assoc, ← Complex.exp_add]
    simp
  · rw [show (↑E₁ - ↑E₀ : ℂ) = -↑E₀ + ↑E₁ by ring]
    rw [Complex.exp_add]
    ring
  · rw [← Complex.exp_neg]
    rw [show -(↑E₁ - ↑E₀ : ℂ) = ↑E₀ + (-↑E₁) by ring]
    rw [Complex.exp_add]
    ring
  · rw [mul_comm _ (X 1 1 : ℂ), mul_assoc, ← Complex.exp_add]
    simp

/-- Under `matrixModularFlow (gibbsTwoLevelH m k E₀ E₁) _ t`, the Peirce diagonal (`body`)
is strictly stationary. -/
theorem matrixModularFlow_gibbsTwoLevelH_diagonal (m k : ℕ) (E₀ E₁ : ℝ) (t : ℝ)
    (X : Matrix (Fin (m + k)) (Fin (m + k)) ℂ) :
    matrixModularFlow (gibbsTwoLevelH m k E₀ E₁) (gibbsTwoLevelH_isHermitian m k E₀ E₁) t
      (diagonal X) = diagonal X := by
  rw [matrixModularFlow_apply, uExp_gibbsTwoLevelH, uExp_gibbsTwoLevelH]
  have h11 := blockP1_sandwich_corners m k X
  have h22 := blockP2_sandwich_corners m k X
  set U : Matrix (Fin (m + k)) (Fin (m + k)) ℂ :=
    Complex.exp (Complex.I * (t : ℂ) * (E₀ : ℂ)) • blockP1 m k +
      Complex.exp (Complex.I * (t : ℂ) * (E₁ : ℂ)) • blockP2 m k
  set Uinv : Matrix (Fin (m + k)) (Fin (m + k)) ℂ :=
    Complex.exp (Complex.I * ((-t : ℝ) : ℂ) * (E₀ : ℂ)) • blockP1 m k +
      Complex.exp (Complex.I * ((-t : ℝ) : ℂ) * (E₁ : ℂ)) • blockP2 m k
  have hD1 : U * (blockP1 m k * X * blockP1 m k) * Uinv = blockP1 m k * X * blockP1 m k := by
    dsimp [U, Uinv]
    rw [peirce_conj_formula, h11.1, h11.2.1, h11.2.2.1, h11.2.2.2,
      smul_zero, smul_zero, smul_zero, add_zero, add_zero, add_zero, ← Complex.exp_add]
    have harg : Complex.I * (t : ℂ) * (E₀ : ℂ) + Complex.I * ((-t : ℝ) : ℂ) * (E₀ : ℂ) = 0 := by
      rw [Complex.ofReal_neg, mul_neg, neg_mul, add_neg_cancel]
    rw [harg, Complex.exp_zero, one_smul]
  have hD2 : U * (blockP2 m k * X * blockP2 m k) * Uinv = blockP2 m k * X * blockP2 m k := by
    dsimp [U, Uinv]
    rw [peirce_conj_formula, h22.1, h22.2.1, h22.2.2.1, h22.2.2.2,
      smul_zero, smul_zero, smul_zero, zero_add, zero_add, zero_add, ← Complex.exp_add]
    have harg : Complex.I * (t : ℂ) * (E₁ : ℂ) + Complex.I * ((-t : ℝ) : ℂ) * (E₁ : ℂ) = 0 := by
      rw [Complex.ofReal_neg, mul_neg, neg_mul, add_neg_cancel]
    rw [harg, Complex.exp_zero, one_smul]
  change U * (blockP1 m k * X * blockP1 m k + blockP2 m k * X * blockP2 m k) * Uinv =
    blockP1 m k * X * blockP1 m k + blockP2 m k * X * blockP2 m k
  rw [Matrix.mul_add U, Matrix.add_mul _ _ Uinv, hD1, hD2]

/-- Under `matrixModularFlow (gibbsTwoLevelH m k E₀ E₁) _ t`, the `P1 * X * P2` corner
rotates by the phase `exp(I * t * (E₀ - E₁))`. -/
theorem matrixModularFlow_gibbsTwoLevelH_P1_X_P2 (m k : ℕ) (E₀ E₁ : ℝ) (t : ℝ)
    (X : Matrix (Fin (m + k)) (Fin (m + k)) ℂ) :
    matrixModularFlow (gibbsTwoLevelH m k E₀ E₁) (gibbsTwoLevelH_isHermitian m k E₀ E₁) t
      (blockP1 m k * X * blockP2 m k) =
        Complex.exp (Complex.I * (t : ℂ) * ((E₀ : ℂ) - (E₁ : ℂ))) •
          (blockP1 m k * X * blockP2 m k) := by
  rw [matrixModularFlow_apply, uExp_gibbsTwoLevelH, uExp_gibbsTwoLevelH, peirce_conj_formula]
  obtain ⟨c11, c12, c21, c22⟩ := blockP12_sandwich_corners m k X
  rw [c11, c12, c21, c22, smul_zero, smul_zero, smul_zero, zero_add, add_zero, add_zero,
    ← Complex.exp_add]
  have harg :
      Complex.I * (t : ℂ) * (E₀ : ℂ) + Complex.I * ((-t : ℝ) : ℂ) * (E₁ : ℂ) =
        Complex.I * (t : ℂ) * ((E₀ : ℂ) - (E₁ : ℂ)) := by
    rw [Complex.ofReal_neg, mul_neg, neg_mul, mul_sub]
    abel
  rw [harg]

/-- Under `matrixModularFlow (gibbsTwoLevelH m k E₀ E₁) _ t`, the `P2 * X * P1` corner
rotates by the conjugate phase `exp(-I * t * (E₀ - E₁))`. -/
theorem matrixModularFlow_gibbsTwoLevelH_P2_X_P1 (m k : ℕ) (E₀ E₁ : ℝ) (t : ℝ)
    (X : Matrix (Fin (m + k)) (Fin (m + k)) ℂ) :
    matrixModularFlow (gibbsTwoLevelH m k E₀ E₁) (gibbsTwoLevelH_isHermitian m k E₀ E₁) t
      (blockP2 m k * X * blockP1 m k) =
        Complex.exp (-(Complex.I * (t : ℂ) * ((E₀ : ℂ) - (E₁ : ℂ)))) •
          (blockP2 m k * X * blockP1 m k) := by
  rw [matrixModularFlow_apply, uExp_gibbsTwoLevelH, uExp_gibbsTwoLevelH, peirce_conj_formula]
  obtain ⟨c11, c12, c21, c22⟩ := blockP21_sandwich_corners m k X
  rw [c11, c12, c21, c22, smul_zero, smul_zero, smul_zero, zero_add, zero_add, add_zero,
    ← Complex.exp_add]
  have harg :
      Complex.I * (t : ℂ) * (E₁ : ℂ) + Complex.I * ((-t : ℝ) : ℂ) * (E₀ : ℂ) =
        -(Complex.I * (t : ℂ) * ((E₀ : ℂ) - (E₁ : ℂ))) := by
    rw [Complex.ofReal_neg, mul_neg, neg_mul, mul_sub]
    abel
  rw [harg]

end BlockPeirce

end InfoGeometry.Algebra.ModularDeWittFlow.DynamicGibbs
