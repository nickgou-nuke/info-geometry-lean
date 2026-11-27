/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import Mathlib.Data.Matrix.Basic
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.Tactic

noncomputable section

open Matrix

/-!
# Zorn split-quaternion realization of the Wigner angle

McKinstrie--Kozlov, *How to calculate the Wigner angle*, uses an `SU(1,1)`
spinor calculus and the associated `SO⁺(1,2)` adjoint action.  Over `ℝ`, with
no complex `i`, the relevant `2×2` matrices are exactly the imaginary units of
a split-quaternion sheet inside Zorn's split octonions.  This owner proves:

1. the three structure constants and squares of `G₁, G₂, G₃` (Eq. 79), the
   Zorn norm identity `det T = t² - x² - y²` (Eq. 32), and determinant
   preservation under unit-split-quaternion conjugation;
2. the `SO(1,2)` Schmidt extraction and the Wigner numerator/denominator
   identities for a product of two non-parallel boosts (Eqs. 24--25, 32--49);
3. the half-angle spinor identities (Eq. 68) that square to the full-angle
   `SO(1,2)` quantities (Eqs. 24--25, 49, 77).

No claim is made about the non-associative eight-dimensional octonions or the
full `G₂` derivation algebra: everything here lives in the associative
split-quaternion slice.
-/

namespace ZornSplitOctonionWignerAngleBridge

set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false

/-! ### Part 1: real split-quaternion slice ℍₛ ⊂ 𝕆ₛ -/

/-- Zorn split-quaternion imaginary basis: `G₁ = ℓe₃`, `G₂ = ℓ`, `G₃ = e₃`. -/
def zornG1 : Matrix (Fin 2) (Fin 2) ℝ := !![0, 1; 1, 0]
def zornG2 : Matrix (Fin 2) (Fin 2) ℝ := !![1, 0; 0, -1]
def zornG3 : Matrix (Fin 2) (Fin 2) ℝ := !![0, 1; -1, 0]

/-- Explicit matrix non-commutativity witness for `zornG1` and `zornG2`. -/
theorem zornG1_zornG2_noncommutative : zornG1 * zornG2 ≠ zornG2 * zornG1 := by
  intro h
  have h01 := congr_fun (congr_fun h 0) 1
  norm_num [zornG1, zornG2, Matrix.mul_apply, Fin.sum_univ_two] at h01

/-- Imaginary split-quaternion vector `T(t, x, y) = t e₃ + x ℓ + y (ℓe₃)`. -/
def imSplitQuat (t x y : ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  t • zornG3 + x • zornG2 + y • zornG1

/-- Eq. 79 commutation/square relations, Eq. 32 metric, and determinant
preservation under `SL(2,ℝ) ≅ SU(1,1)` conjugation. -/
theorem zorn_split_quaternion_su11_so12_bridge
    (t x y : ℝ) (M MInv : Matrix (Fin 2) (Fin 2) ℝ)
    (hDetM : M.det = 1) (hInv : M * MInv = 1) :
    (zornG1 * zornG1 = 1 ∧ zornG2 * zornG2 = 1 ∧ zornG3 * zornG3 = -1) ∧
    (zornG1 * zornG2 - zornG2 * zornG1 = (-2 : ℝ) • zornG3 ∧
     zornG2 * zornG3 - zornG3 * zornG2 = (2 : ℝ) • zornG1 ∧
     zornG3 * zornG1 - zornG1 * zornG3 = (2 : ℝ) • zornG2) ∧
    ((imSplitQuat t x y).det = t ^ 2 - x ^ 2 - y ^ 2) ∧
    ((M * imSplitQuat t x y * MInv).det = t ^ 2 - x ^ 2 - y ^ 2) := by
  have hDetT : (imSplitQuat t x y).det = t ^ 2 - x ^ 2 - y ^ 2 := by
    simp [imSplitQuat, zornG1, zornG2, zornG3, Matrix.det_fin_two]
    ring
  have hDetInv : MInv.det = 1 := by
    have h1 := congrArg Matrix.det hInv
    rw [Matrix.det_mul, Matrix.det_one, hDetM, one_mul] at h1
    exact h1
  refine ⟨⟨?_, ?_, ?_⟩, ⟨?_, ?_, ?_⟩, hDetT, ?_⟩
  · ext i j <;> fin_cases i <;> fin_cases j <;>
      simp [zornG1, Matrix.mul_apply, Fin.sum_univ_two]
  · ext i j <;> fin_cases i <;> fin_cases j <;>
      simp [zornG2, Matrix.mul_apply, Fin.sum_univ_two]
  · ext i j <;> fin_cases i <;> fin_cases j <;>
      simp [zornG3, Matrix.mul_apply, Fin.sum_univ_two]
  · ext i j <;> fin_cases i <;> fin_cases j <;>
      simp [zornG1, zornG2, zornG3, Matrix.mul_apply, Fin.sum_univ_two] <;> norm_num
  · ext i j <;> fin_cases i <;> fin_cases j <;>
      simp [zornG1, zornG2, zornG3, Matrix.mul_apply, Fin.sum_univ_two] <;> norm_num
  · ext i j <;> fin_cases i <;> fin_cases j <;>
      simp [zornG1, zornG2, zornG3, Matrix.mul_apply, Fin.sum_univ_two] <;> norm_num
  · rw [Matrix.det_mul, Matrix.det_mul, hDetM, hDetInv, one_mul, mul_one, hDetT]

/-! ### Part 2: SO(1,2) boosts, rotations, and the Wigner angle -/

/-- `SO(1,2)` metric `S = diag(1, -1, -1)` (Eq. 32). -/
def metric12 : Matrix (Fin 3) (Fin 3) ℝ :=
  !![1,  0,  0;
     0, -1,  0;
     0,  0, -1]

/-- Fundamental `x`-boost `Bₓ(γ, u)` (Eq. 33; `γ² - u² = 1`). -/
def so12BoostX (γ u : ℝ) : Matrix (Fin 3) (Fin 3) ℝ :=
  !![γ, u, 0;
     u, γ, 0;
     0, 0, 1]

/-- Spatial rotation `R(c, s)` (Eq. 34; `c² + s² = 1`). -/
def so12Rot (c s : ℝ) : Matrix (Fin 3) (Fin 3) ℝ :=
  !![1, 0,  0;
     0, c, -s;
     0, s,  c]

/-- Boost in direction `(c, s)` (Eqs. 35--36). -/
def so12BoostDir (γ u c s : ℝ) : Matrix (Fin 3) (Fin 3) ℝ :=
  !![γ,     u * c,             u * s;
     u * c, 1 + (γ - 1) * c^2, (γ - 1) * c * s;
     u * s, (γ - 1) * s * c,   1 + (γ - 1) * s^2]

/-- Schmidt extraction and Wigner numerator/denominator identities. -/
theorem mckinstrie_kozlov_so12_wigner_angle_identities
    (γ γ₁ u₁ γ₂ u₂ c s c₁ s₁ c₂ s₂ : ℝ)
    (h1 : γ₁ ^ 2 - u₁ ^ 2 = 1) (h2 : γ₂ ^ 2 - u₂ ^ 2 = 1) (hcs : c ^ 2 + s ^ 2 = 1) :
    let L_schmidt := so12Rot c₂ s₂ * so12BoostX γ u₁ * (so12Rot c₁ s₁)ᵀ
    let L_prod := so12BoostDir γ₂ u₂ c s * so12BoostX γ₁ u₁
    let δ₁ := γ₁ - 1
    let δ₂ := γ₂ - 1
    (L_schmidt 1 1 + L_schmidt 2 2 = (γ + 1) * (c₂ * c₁ + s₂ * s₁) ∧
     L_schmidt 2 1 - L_schmidt 1 2 = (γ + 1) * (s₂ * c₁ - c₂ * s₁)) ∧
    (L_prod 0 0 = γ₂ * γ₁ + u₂ * u₁ * c) ∧
    (L_prod 2 1 - L_prod 1 2 = (u₂ * u₁ + δ₂ * δ₁ * c) * s) ∧
    (L_prod 1 1 + L_prod 2 2 = γ₂ + γ₁ + (u₂ * u₁ + δ₂ * δ₁ * c) * c) ∧
    (L_prodᵀ * metric12 * L_prod = metric12) ∧
    (((u₂ * u₁ + δ₂ * δ₁ * c) * s) ^ 2 + (γ₂ + γ₁ + (u₂ * u₁ + δ₂ * δ₁ * c) * c) ^ 2 =
      (γ₂ * γ₁ + 1 + u₂ * u₁ * c) ^ 2) := by
  dsimp
  have hs2 : s ^ 2 = 1 - c ^ 2 := by linarith
  have hu1 : u₁ ^ 2 = γ₁ ^ 2 - 1 := by linarith
  have hu2 : u₂ ^ 2 = γ₂ ^ 2 - 1 := by linarith
  have hs3 : s ^ 3 = s * (1 - c ^ 2) := by
    calc
      s ^ 3 = s * s ^ 2 := by ring
      _ = s * (1 - c ^ 2) := by rw [hs2]
  have hs4 : s ^ 4 = (1 - c ^ 2) ^ 2 := by
    calc
      s ^ 4 = (s ^ 2) ^ 2 := by ring
      _ = (1 - c ^ 2) ^ 2 := by rw [hs2]
  have hc2 : c ^ 2 = 1 - s ^ 2 := by linarith
  have hc3 : c ^ 3 = c * (1 - s ^ 2) := by
    calc
      c ^ 3 = c * c ^ 2 := by ring
      _ = c * (1 - s ^ 2) := by rw [hc2]
  have hB1 : (so12BoostX γ₁ u₁)ᵀ * metric12 * so12BoostX γ₁ u₁ = metric12 := by
    ext i j <;> fin_cases i <;> fin_cases j <;>
      simp [so12BoostX, metric12, Matrix.mul_apply, Fin.sum_univ_three] <;> nlinarith [h1]
  have hB2 : (so12BoostDir γ₂ u₂ c s)ᵀ * metric12 * so12BoostDir γ₂ u₂ c s = metric12 := by
    ext i j <;> fin_cases i <;> fin_cases j <;>
      simp [so12BoostDir, metric12, Matrix.mul_apply, Fin.sum_univ_three]
    all_goals try ring_nf
    all_goals
      first | rw [hs4] | skip
    all_goals
      first | rw [hs3] | skip
    all_goals
      first | rw [hc3] | skip
    all_goals
      first | rw [hs2] | skip
    all_goals
      first | rw [hu2] | skip
    all_goals nlinarith [h2, hcs]
  have hLorentz : (so12BoostDir γ₂ u₂ c s * so12BoostX γ₁ u₁)ᵀ * metric12 *
      (so12BoostDir γ₂ u₂ c s * so12BoostX γ₁ u₁) = metric12 := by
    rw [Matrix.transpose_mul]
    calc
      (so12BoostX γ₁ u₁)ᵀ * (so12BoostDir γ₂ u₂ c s)ᵀ * metric12 *
          (so12BoostDir γ₂ u₂ c s * so12BoostX γ₁ u₁)
          = (so12BoostX γ₁ u₁)ᵀ *
              ((so12BoostDir γ₂ u₂ c s)ᵀ * metric12 * so12BoostDir γ₂ u₂ c s) *
              so12BoostX γ₁ u₁ := by simp only [Matrix.mul_assoc]
      _ = metric12 := by rw [hB2, hB1]
  refine ⟨⟨?_, ?_⟩, ?_, ?_, ?_, hLorentz, ?_⟩
  · simp [so12Rot, so12BoostX, Matrix.mul_apply, Fin.sum_univ_three]
    ring
  · simp [so12Rot, so12BoostX, Matrix.mul_apply, Fin.sum_univ_three]
    ring
  · simp [so12BoostDir, so12BoostX, Matrix.mul_apply, Fin.sum_univ_three]
    ring
  · simp [so12BoostDir, so12BoostX, Matrix.mul_apply, Fin.sum_univ_three]
    ring
  · simp [so12BoostDir, so12BoostX, Matrix.mul_apply, Fin.sum_univ_three]
    ring_nf
    rw [hs2]
    ring
  · ring_nf
    simp only [hs2, hu1, hu2]
    ring

/-! ### Part 3: spinor half-angle to full-angle doubling -/

/-- Eq. 68 spinor half-angle coordinates square to the full-angle Wigner
cosine, sine, and common denominator of Eqs. 24--25, 49, 77. -/
theorem zorn_spinor_half_angle_recovers_so12_wigner_angle
    (μ₁ ν₁ μ₂ ν₂ c s : ℝ)
    (h1 : μ₁ ^ 2 - ν₁ ^ 2 = 1) (h2 : μ₂ ^ 2 - ν₂ ^ 2 = 1) (hcs : c ^ 2 + s ^ 2 = 1) :
    let γ₁ := μ₁ ^ 2 + ν₁ ^ 2
    let γ₂ := μ₂ ^ 2 + ν₂ ^ 2
    let u₁ := 2 * μ₁ * ν₁
    let u₂ := 2 * μ₂ * ν₂
    let δ₁ := γ₁ - 1
    let δ₂ := γ₂ - 1
    let X_half := μ₂ * μ₁ + ν₂ * ν₁ * c
    let Y_half := ν₂ * ν₁ * s
    (γ₁ ^ 2 - u₁ ^ 2 = 1 ∧ γ₂ ^ 2 - u₂ ^ 2 = 1) ∧
    (2 * X_half * Y_half = (1 / 2 : ℝ) * ((u₂ * u₁ + δ₂ * δ₁ * c) * s)) ∧
    (X_half ^ 2 - Y_half ^ 2 =
      (1 / 2 : ℝ) * (γ₂ + γ₁ + (u₂ * u₁ + δ₂ * δ₁ * c) * c)) ∧
    (X_half ^ 2 + Y_half ^ 2 = (1 / 2 : ℝ) * (γ₂ * γ₁ + 1 + u₂ * u₁ * c)) := by
  dsimp
  have hμ1 : μ₁ ^ 2 = ν₁ ^ 2 + 1 := by linarith
  have hμ2 : μ₂ ^ 2 = ν₂ ^ 2 + 1 := by linarith
  have hs2 : s ^ 2 = 1 - c ^ 2 := by linarith
  refine ⟨⟨?_, ?_⟩, ?_, ?_, ?_⟩
  · calc
      (μ₁ ^ 2 + ν₁ ^ 2) ^ 2 - (2 * μ₁ * ν₁) ^ 2 = (μ₁ ^ 2 - ν₁ ^ 2) ^ 2 := by ring
      _ = 1 := by rw [h1]; norm_num
  · calc
      (μ₂ ^ 2 + ν₂ ^ 2) ^ 2 - (2 * μ₂ * ν₂) ^ 2 = (μ₂ ^ 2 - ν₂ ^ 2) ^ 2 := by ring
      _ = 1 := by rw [h2]; norm_num
  · ring_nf
    rw [hμ1, hμ2]
    ring
  · ring_nf
    rw [hs2, hμ1, hμ2]
    ring
  · ring_nf
    rw [hs2, hμ1, hμ2]
    ring

/-- Explicit `3 × 3` real matrix non-commutativity witness for the `SO(1,2)` carrier. -/
theorem so12_mat3r_noncomm :
    ∃ A B : Matrix (Fin 3) (Fin 3) ℝ, A * B ≠ B * A := by
  refine ⟨Matrix.single 0 1 1, Matrix.single 1 0 1, fun h => ?_⟩
  have h00 := congrArg (fun M : Matrix (Fin 3) (Fin 3) ℝ => M 0 0) h
  simp [Matrix.single_mul_single_same, Matrix.single_mul_single_of_ne] at h00

end ZornSplitOctonionWignerAngleBridge
