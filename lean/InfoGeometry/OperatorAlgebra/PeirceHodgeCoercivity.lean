/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.OperatorAlgebra.LieJordanHodgePairing

/-!
# Coercivity on the entire matrix algebra outside a harmonic corner

If p is an orthogonal projection and K >= gamma*(1-p) in native matrix
positive-semidefinite order, Jordan multiplication by K controls X-pXp.
The input matrix is arbitrary, including both off-diagonal corners.
-/

namespace InfoGeometry.OperatorAlgebra.PeirceHodgeCoercivity

open Matrix HilbertSchmidtMatrix
open InfoGeometry.OperatorAlgebra.LieJordanHodgePairing

variable {n : ℕ}
local notation "Mat" => Matrix (Fin n) (Fin n) ℝ
local notation "hs" => hilbertSchmidtPairing

theorem pairing_smul_right (r : ℝ) (x y : Mat) :
    hs x (r • y) = r * hs x y := by
  simp [hilbertSchmidtPairing, mul_smul_comm]

theorem sandwich_pairing {p : Mat} (hpt : pᵀ = p) (x y : Mat) :
    hs (p * x * p) y = hs x (p * y * p) := by
  rw [pairing_mul_right, pairing_mul_left, hpt]
  simp only [mul_assoc]

theorem sandwich_idempotent {p : Mat} (hp : p * p = p) (x : Mat) :
    p * (p * x * p) * p = p * x * p := by
  calc
    _ = (p * p) * x * (p * p) := by simp only [mul_assoc]
    _ = _ := by rw [hp]

theorem sandwich_self_pairing {p : Mat} (hp : p * p = p)
    (hpt : pᵀ = p) (x : Mat) :
    hs x (p * x * p) = hs (p * x * p) (p * x * p) := by
  rw [sandwich_pairing hpt, sandwich_idempotent hp]

theorem residual_self_pairing {p : Mat} (hp : p * p = p)
    (hpt : pᵀ = p) (x : Mat) :
    hs x (x - p * x * p) = hs (x - p * x * p) (x - p * x * p) := by
  have he := sandwich_self_pairing hp hpt x
  have hsx := hilbertSchmidt_symmetry x (p * x * p)
  simp only [pairing_sub_left, pairing_sub_right]
  linarith

/-- The complementary corner contributes once more, and is never discarded. -/
theorem complementary_jordan_energy {p : Mat} (hp : p * p = p)
    (hpt : pᵀ = p) (x : Mat) :
    hs x ((1 - p) * x + x * (1 - p)) =
      hs (x - p * x * p) (x - p * x * p) +
      hs ((1 - p) * x * (1 - p)) ((1 - p) * x * (1 - p)) := by
  have hq : (1 - p) * (1 - p) = 1 - p := by
    noncomm_ring [hp]
  have hqt : (1 - p)ᵀ = 1 - p := by simp [hpt]
  have he : (1 - p) * x + x * (1 - p) =
      (x - p * x * p) + (1 - p) * x * (1 - p) := by noncomm_ring
  rw [he, pairing_add_right, residual_self_pairing hp hpt,
    sandwich_self_pairing hq hqt]

/-- Positive-semidefinite coefficients give positive Jordan quadratic forms. -/
theorem jordan_pairing_nonneg {K : Mat} (hK : K.PosSemidef) (x : Mat) :
    0 ≤ hs x (K * x + x * K) := by
  have ht : xᴴ = xᵀ := by ext i j; simp
  have h₁ := (hK.conjTranspose_mul_mul_same x).trace_nonneg
  have h₂ := (hK.mul_mul_conjTranspose_same x).trace_nonneg
  rw [ht] at h₁ h₂
  calc
    0 ≤ trace (xᵀ * K * x) + trace (x * K * xᵀ) := add_nonneg h₁ h₂
    _ = hs x (K * x + x * K) := by
      unfold hilbertSchmidtPairing
      rw [mul_add, trace_add]
      congr 1
      · rw [mul_assoc]
      · exact trace_mul_comm _ _

/-- Native Loewner comparison, evaluated on every full matrix input. -/
theorem jordan_pairing_lower_bound (K Q : Mat) (gamma : ℝ)
    (hK : (K - gamma • Q).PosSemidef) (x : Mat) :
    gamma * hs x (Q * x + x * Q) ≤ hs x (K * x + x * K) := by
  have h := jordan_pairing_nonneg hK x
  have he : (K - gamma • Q) * x + x * (K - gamma • Q) =
      (K * x + x * K) - gamma • (Q * x + x * Q) := by
    simp only [sub_mul, mul_sub, smul_mul_assoc, mul_smul_comm, smul_add]
    abel
  rw [he, pairing_sub_right, pairing_smul_right] at h
  linarith

/-- A coefficient bound yields coercivity outside the entire pXp corner. -/
theorem full_matrix_corner_coercivity
    {p : Mat} (hp : p * p = p) (hpt : pᵀ = p)
    (K : Mat) {gamma : ℝ} (hgamma : 0 ≤ gamma)
    (hK : (K - gamma • (1 - p)).PosSemidef) (x : Mat) :
    gamma * hs (x - p * x * p) (x - p * x * p) ≤ hs x (K * x + x * K) := by
  have hq := hilbertSchmidt_pos_semidef ((1 - p) * x * (1 - p))
  calc
    _ ≤ gamma * (hs (x - p * x * p) (x - p * x * p) +
        hs ((1 - p) * x * (1 - p)) ((1 - p) * x * (1 - p))) :=
      mul_le_mul_of_nonneg_left (le_add_of_nonneg_right hq) hgamma
    _ = gamma * hs x ((1 - p) * x + x * (1 - p)) := by
      rw [complementary_jordan_energy hp hpt]
    _ ≤ _ := jordan_pairing_lower_bound K (1 - p) gamma hK x

end InfoGeometry.OperatorAlgebra.PeirceHodgeCoercivity
