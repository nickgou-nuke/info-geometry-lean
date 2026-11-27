/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import Mathlib.LinearAlgebra.CliffordAlgebra.Basic
import Mathlib.LinearAlgebra.CliffordAlgebra.Even
import Mathlib.LinearAlgebra.CliffordAlgebra.EvenEquiv
import Mathlib.LinearAlgebra.CliffordAlgebra.Conjugation
import Mathlib.LinearAlgebra.CliffordAlgebra.Grading
import Mathlib.LinearAlgebra.CliffordAlgebra.Star
import Mathlib.LinearAlgebra.QuadraticForm.IsometryEquiv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Tactic.NoncommRing
import InfoGeometry.Algebra.CliffordGA
import InfoGeometry.Clifford.GradedGraceContraction
import InfoGeometry.Clifford.LipschitzWittRieszPrimary

/-!
# Spacetime Split `Cl(3,0) ≃ₐ[ℝ] Cl⁺(1,3)` and Faraday Decomposition

Formalizes Gull–Lasenby–Doran (1993), *Imaginary Numbers are not Real — the Geometric Algebra
of Spacetime*, §5 (Eqs. 5.1–5.15):
- Real Minkowski Clifford algebra `Cl13 := CliffordAlgebra Q13` with signature `(+,-,-,-)`
  on `Fin 4 → ℝ`, orthonormal generators `γ μ`, relative spatial bivectors `σ k = γ k.succ * γ 0`,
  and unit spacetime pseudoscalar `I13 = γ 0 * γ 1 * γ 2 * γ 3`.
- Real 3D Euclidean Clifford algebra `Cl30 := CliffordAlgebra Q30` and the canonical spacetime
  split isomorphism `spacetimeSplitEquiv : Cl30 ≃ₐ[ℝ] CliffordAlgebra.even Q13` mapping
  `e30 k ↦ σ k`, `I30 ↦ I13`, and `star x ↦ reverse (spacetimeSplitEquiv x)`.
- Faraday bivector split `F = faradayE F + faradayBI F` in the `γ 0` observer frame, with
  explicit 6-component `γ μ * γ ν` correspondence and `bivectorSubmodule` characterization.
- Canonical STA Dirac spinor form `diracSpinor ρ β R` with `ψ * reverse ψ = ρ (cos β + I sin β)`.
- Downstream M2B helpers (`η13`, `γRecip`, `γRecip_mul_γ_add_swap`, `ι_Q13_eq_sum`).
-/

namespace InfoGeometry.Hestenes.SpacetimeSplit

section ScalarHelpers

private lemma q13_apply_helper (x : Fin 4 → ℝ) :
    x 0 * x 0 - (x 1 * x 1 + x 2 * x 2 + x 3 * x 3) =
      x 0 ^ 2 - x 1 ^ 2 - x 2 ^ 2 - x 3 ^ 2 := by
  ring

private lemma q13_polar_helper (x y : Fin 4 → ℝ) :
    (x 0 + y 0) ^ 2 - (x 1 + y 1) ^ 2 - (x 2 + y 2) ^ 2 - (x 3 + y 3) ^ 2 -
        (x 0 ^ 2 - x 1 ^ 2 - x 2 ^ 2 - x 3 ^ 2) -
        (y 0 ^ 2 - y 1 ^ 2 - y 2 ^ 2 - y 3 ^ 2) =
      2 * (x 0 * y 0 - x 1 * y 1 - x 2 * y 2 - x 3 * y 3) := by
  ring

private lemma q30_apply_helper (x : Fin 3 → ℝ) :
    x 0 * x 0 + x 1 * x 1 + x 2 * x 2 = x 0 ^ 2 + x 1 ^ 2 + x 2 ^ 2 := by
  ring

private lemma q30_polar_helper (x y : Fin 3 → ℝ) :
    (x 0 + y 0) ^ 2 + (x 1 + y 1) ^ 2 + (x 2 + y 2) ^ 2 -
        (x 0 ^ 2 + x 1 ^ 2 + x 2 ^ 2) - (y 0 ^ 2 + y 1 ^ 2 + y 2 ^ 2) =
      2 * (x 0 * y 0 + x 1 * y 1 + x 2 * y 2) := by
  ring

private lemma q13_cons_split_helper (r a b c : ℝ) :
    r ^ 2 - a ^ 2 - b ^ 2 - c ^ 2 = r * r - (a ^ 2 + b ^ 2 + c ^ 2) := by
  ring

private lemma half_mul_two : (1 / 2 : ℝ) * 2 = 1 := by
  norm_num

private lemma two_mul_half_real : (2 : ℝ) * (1 / 2 : ℝ) = 1 := by
  norm_num

private lemma cos_half_sq_sub_sin_half_sq (β : ℝ) :
    Real.cos (β / 2) ^ 2 - Real.sin (β / 2) ^ 2 = Real.cos β := by
  rw [← Real.cos_two_mul', mul_div_cancel₀ β two_ne_zero]

private lemma two_sin_half_cos_half (β : ℝ) :
    2 * Real.sin (β / 2) * Real.cos (β / 2) = Real.sin β := by
  rw [← Real.sin_two_mul, mul_div_cancel₀ β two_ne_zero]

private lemma sqrt_mul_sqrt_cos (ρ β : ℝ) (hρ : 0 ≤ ρ) :
    Real.sqrt ρ * Real.sqrt ρ * (Real.cos (β / 2) ^ 2 - Real.sin (β / 2) ^ 2) =
      ρ * Real.cos β := by
  rw [Real.mul_self_sqrt hρ, cos_half_sq_sub_sin_half_sq]

private lemma sqrt_mul_sqrt_sin (ρ β : ℝ) (hρ : 0 ≤ ρ) :
    Real.sqrt ρ * Real.sqrt ρ *
        (Real.cos (β / 2) * Real.sin (β / 2) + Real.sin (β / 2) * Real.cos (β / 2)) =
      ρ * Real.sin β := by
  rw [Real.mul_self_sqrt hρ, ← two_sin_half_cos_half β]
  ring

end ScalarHelpers

noncomputable section

open CliffordAlgebra
open InfoGeometry.Algebra.CliffordGA
open InfoGeometry.Clifford.GradedGraceContraction
open InfoGeometry.Clifford.LipschitzWittRieszPrimary

/-! ### Section 2: `Q13`, `Q30`, Generators `γ`, `σ`, `I13` -/

/-- Real Minkowski quadratic form with `(+,-,-,-)` signature on `Fin 4 → ℝ`. -/
def Q13 : QuadraticForm ℝ (Fin 4 → ℝ) :=
  QuadraticMap.sq.comp (LinearMap.proj 0) -
    (QuadraticMap.sq.comp (LinearMap.proj 1) +
     QuadraticMap.sq.comp (LinearMap.proj 2) +
     QuadraticMap.sq.comp (LinearMap.proj 3))

/-- Real 3D Euclidean quadratic form with `(+,+,+)` signature on `Fin 3 → ℝ`. -/
def Q30 : QuadraticForm ℝ (Fin 3 → ℝ) :=
  ∑ k : Fin 3, QuadraticMap.sq.comp (LinearMap.proj k)

abbrev Cl13 := CliffordAlgebra Q13
abbrev Cl30 := CliffordAlgebra Q30

theorem Q13_apply (x : Fin 4 → ℝ) :
    Q13 x = x 0 ^ 2 - x 1 ^ 2 - x 2 ^ 2 - x 3 ^ 2 := by
  simp only [Q13, sub_apply, add_apply, QuadraticMap.comp_apply,
    QuadraticMap.sq_apply, LinearMap.proj_apply]
  exact q13_apply_helper x

theorem Q13_polar (x y : Fin 4 → ℝ) :
    QuadraticMap.polar Q13 x y = 2 * (x 0 * y 0 - x 1 * y 1 - x 2 * y 2 - x 3 * y 3) := by
  simp only [QuadraticMap.polar, Q13_apply, Pi.add_apply]
  exact q13_polar_helper x y

theorem Q30_apply (x : Fin 3 → ℝ) :
    Q30 x = x 0 ^ 2 + x 1 ^ 2 + x 2 ^ 2 := by
  simp [Q30, Fin.sum_univ_three]
  exact q30_apply_helper x

theorem Q30_polar (x y : Fin 3 → ℝ) :
    QuadraticMap.polar Q30 x y = 2 * (x 0 * y 0 + x 1 * y 1 + x 2 * y 2) := by
  simp only [QuadraticMap.polar, Q30_apply, Pi.add_apply]
  exact q30_polar_helper x y

/-- Standard orthonormal spacetime basis vectors `γ μ` (`μ : Fin 4`) in `Cl(1,3)`. -/
def γ (μ : Fin 4) : Cl13 := CliffordAlgebra.ι Q13 (Pi.single μ 1)

/-- Relative spatial basis bivectors `σ k := γ k.succ * γ 0` (`k : Fin 3`) in `Cl⁺(1,3)`. -/
def σ (k : Fin 3) : Cl13 := γ k.succ * γ 0

/-- Spacetime unit pseudoscalar `I13 := γ 0 * γ 1 * γ 2 * γ 3` in `Cl(1,3)`. -/
def I13 : Cl13 := γ 0 * γ 1 * γ 2 * γ 3

/-- Standard orthonormal 3D spatial basis vectors `e30 k` in `Cl(3,0)`. -/
def e30 (k : Fin 3) : Cl30 := CliffordAlgebra.ι Q30 (Pi.single k 1)

/-- 3D unit pseudoscalar `I30 := e30 0 * e30 1 * e30 2` in `Cl(3,0)`. -/
def I30 : Cl30 := e30 0 * e30 1 * e30 2

theorem Q13_single (μ : Fin 4) :
    Q13 (Pi.single μ 1) = if μ = 0 then 1 else -1 := by
  fin_cases μ <;> simp [Q13_apply]

theorem Q13_polar_single_ne {μ ν : Fin 4} (h : μ ≠ ν) :
    QuadraticMap.polar Q13 (Pi.single μ 1) (Pi.single ν 1) = 0 := by
  fin_cases μ <;> fin_cases ν <;> first | exact absurd rfl h | simp [Q13_polar]

theorem Q30_single (k : Fin 3) : Q30 (Pi.single k 1) = 1 := by
  fin_cases k <;> simp [Q30_apply]

theorem Q30_polar_single_ne {j k : Fin 3} (h : j ≠ k) :
    QuadraticMap.polar Q30 (Pi.single j 1) (Pi.single k 1) = 0 := by
  fin_cases j <;> fin_cases k <;> first | exact absurd rfl h | simp [Q30_polar]

@[simp]
theorem gamma_zero_sq : γ 0 * γ 0 = 1 := by
  rw [γ, CliffordAlgebra.ι_sq_scalar, Q13_single]
  simp

@[simp]
theorem gamma_succ_sq (k : Fin 3) : γ k.succ * γ k.succ = -1 := by
  rw [γ, CliffordAlgebra.ι_sq_scalar, Q13_single]
  have hne : k.succ ≠ 0 := Fin.succ_ne_zero k
  simp [hne]

private lemma gamma_one_sq : γ 1 * γ 1 = -1 := gamma_succ_sq 0
private lemma gamma_two_sq : γ 2 * γ 2 = -1 := gamma_succ_sq 1
private lemma gamma_three_sq : γ 3 * γ 3 = -1 := gamma_succ_sq 2

theorem gamma_anticomm {μ ν : Fin 4} (h : μ ≠ ν) : γ μ * γ ν = -(γ ν * γ μ) := by
  exact clifford_orthogonal_vectors_anticommute Q13 _ _ (Q13_polar_single_ne h.symm)

theorem gamma_mul_add_swap {μ ν : Fin 4} (h : μ ≠ ν) : γ μ * γ ν + γ ν * γ μ = 0 := by
  rw [gamma_anticomm h, neg_add_cancel]

theorem sigma_mul_sigma_eq (j k : Fin 3) : σ j * σ k = -(γ j.succ * γ k.succ) := by
  unfold σ
  have h0k : γ 0 * γ k.succ = -(γ k.succ * γ 0) := gamma_anticomm (Fin.succ_ne_zero k).symm
  calc
    (γ j.succ * γ 0) * (γ k.succ * γ 0)
        = γ j.succ * (γ 0 * γ k.succ) * γ 0 := by noncomm_ring
    _ = γ j.succ * (-(γ k.succ * γ 0)) * γ 0 := by rw [h0k]
    _ = -(γ j.succ * γ k.succ * (γ 0 * γ 0)) := by noncomm_ring
    _ = -(γ j.succ * γ k.succ) := by rw [gamma_zero_sq, mul_one]

@[simp]
theorem sigma_sq (k : Fin 3) : σ k * σ k = 1 := by
  rw [sigma_mul_sigma_eq, gamma_succ_sq, neg_neg]

theorem sigma_anticomm {j k : Fin 3} (h : j ≠ k) : σ j * σ k = -(σ k * σ j) := by
  rw [sigma_mul_sigma_eq, sigma_mul_sigma_eq]
  have hs : j.succ ≠ k.succ := fun h' => h (Fin.succ_inj.mp h')
  rw [gamma_anticomm hs]

theorem sigma_mul_add_swap {j k : Fin 3} (h : j ≠ k) : σ j * σ k + σ k * σ j = 0 := by
  rw [sigma_anticomm h, neg_add_cancel]

theorem sigma_prod_eq_I13 : σ 0 * σ 1 * σ 2 = I13 := by
  have h01 : (0 : Fin 4) ≠ 1 := by decide
  have h02 : (0 : Fin 4) ≠ 2 := by decide
  have h03 : (0 : Fin 4) ≠ 3 := by decide
  rw [sigma_mul_sigma_eq, σ]
  change -(γ 1 * γ 2) * (γ 3 * γ 0) = γ 0 * γ 1 * γ 2 * γ 3
  have h30 : γ 3 * γ 0 = -(γ 0 * γ 3) := gamma_anticomm h03.symm
  have h20 : γ 2 * γ 0 = -(γ 0 * γ 2) := gamma_anticomm h02.symm
  have h10 : γ 1 * γ 0 = -(γ 0 * γ 1) := gamma_anticomm h01.symm
  calc
    -(γ 1 * γ 2) * (γ 3 * γ 0)
        = γ 1 * γ 2 * (γ 0 * γ 3) := by rw [h30]; noncomm_ring
    _ = γ 1 * (γ 2 * γ 0) * γ 3 := by noncomm_ring
    _ = -(γ 1 * γ 0 * γ 2 * γ 3) := by rw [h20]; noncomm_ring
    _ = γ 0 * γ 1 * γ 2 * γ 3 := by rw [h10]; noncomm_ring

@[simp]
theorem I13_sq : I13 * I13 = -1 := by
  have h01 : γ 1 * γ 0 = -(γ 0 * γ 1) := gamma_anticomm (by decide)
  have h02 : γ 2 * γ 0 = -(γ 0 * γ 2) := gamma_anticomm (by decide)
  have h03 : γ 3 * γ 0 = -(γ 0 * γ 3) := gamma_anticomm (by decide)
  have h12 : γ 2 * γ 1 = -(γ 1 * γ 2) := gamma_anticomm (by decide)
  have h13 : γ 3 * γ 1 = -(γ 1 * γ 3) := gamma_anticomm (by decide)
  have h23 : γ 3 * γ 2 = -(γ 2 * γ 3) := gamma_anticomm (by decide)
  have g1 : γ 1 * γ 1 = -1 := gamma_succ_sq 0
  have g2 : γ 2 * γ 2 = -1 := gamma_succ_sq 1
  have g3 : γ 3 * γ 3 = -1 := gamma_succ_sq 2
  unfold I13
  calc
    (γ 0 * γ 1 * γ 2 * γ 3) * (γ 0 * γ 1 * γ 2 * γ 3)
        = γ 0 * γ 1 * γ 2 * (γ 3 * γ 0) * γ 1 * γ 2 * γ 3 := by noncomm_ring
    _ = -(γ 0 * γ 1 * (γ 2 * γ 0) * γ 3 * γ 1 * γ 2 * γ 3) := by rw [h03]; noncomm_ring
    _ = γ 0 * (γ 1 * γ 0) * γ 2 * γ 3 * γ 1 * γ 2 * γ 3 := by rw [h02]; noncomm_ring
    _ = -((γ 0 * γ 0) * γ 1 * γ 2 * γ 3 * γ 1 * γ 2 * γ 3) := by rw [h01]; noncomm_ring
    _ = -(γ 1 * γ 2 * (γ 3 * γ 1) * γ 2 * γ 3) := by rw [gamma_zero_sq]; noncomm_ring
    _ = γ 1 * (γ 2 * γ 1) * γ 3 * γ 2 * γ 3 := by rw [h13]; noncomm_ring
    _ = -((γ 1 * γ 1) * γ 2 * γ 3 * γ 2 * γ 3) := by rw [h12]; noncomm_ring
    _ = γ 2 * (γ 3 * γ 2) * γ 3 := by rw [g1]; noncomm_ring
    _ = -((γ 2 * γ 2) * (γ 3 * γ 3)) := by rw [h23]; noncomm_ring
    _ = -1 := by rw [g2, g3]; noncomm_ring

theorem I13_anticomm_gamma (μ : Fin 4) : I13 * γ μ = -(γ μ * I13) := by
  have h01 : γ 1 * γ 0 = -(γ 0 * γ 1) := gamma_anticomm (by decide)
  have h02 : γ 2 * γ 0 = -(γ 0 * γ 2) := gamma_anticomm (by decide)
  have h03 : γ 3 * γ 0 = -(γ 0 * γ 3) := gamma_anticomm (by decide)
  have h12 : γ 2 * γ 1 = -(γ 1 * γ 2) := gamma_anticomm (by decide)
  have h13 : γ 3 * γ 1 = -(γ 1 * γ 3) := gamma_anticomm (by decide)
  have h23 : γ 3 * γ 2 = -(γ 2 * γ 3) := gamma_anticomm (by decide)
  have h10 : γ 0 * γ 1 = -(γ 1 * γ 0) := gamma_anticomm (by decide)
  have h20 : γ 0 * γ 2 = -(γ 2 * γ 0) := gamma_anticomm (by decide)
  have h30 : γ 0 * γ 3 = -(γ 3 * γ 0) := gamma_anticomm (by decide)
  have h21 : γ 1 * γ 2 = -(γ 2 * γ 1) := gamma_anticomm (by decide)
  have h31 : γ 1 * γ 3 = -(γ 3 * γ 1) := gamma_anticomm (by decide)
  have h32 : γ 2 * γ 3 = -(γ 3 * γ 2) := gamma_anticomm (by decide)
  unfold I13
  fin_cases μ
  · calc
      γ 0 * γ 1 * γ 2 * γ 3 * γ 0 = γ 0 * γ 1 * γ 2 * (γ 3 * γ 0) := by noncomm_ring
      _ = -(γ 0 * γ 1 * (γ 2 * γ 0) * γ 3) := by rw [h03]; noncomm_ring
      _ = γ 0 * (γ 1 * γ 0) * γ 2 * γ 3 := by rw [h02]; noncomm_ring
      _ = -(γ 0 * (γ 0 * γ 1 * γ 2 * γ 3)) := by
        (conv_lhs => rw [h01])
        noncomm_ring
  · calc
      γ 0 * γ 1 * γ 2 * γ 3 * γ 1 = γ 0 * γ 1 * γ 2 * (γ 3 * γ 1) := by noncomm_ring
      _ = -(γ 0 * γ 1 * (γ 2 * γ 1) * γ 3) := by rw [h13]; noncomm_ring
      _ = γ 0 * (γ 1 * γ 1) * γ 2 * γ 3 := by rw [h12]; noncomm_ring
      _ = -(γ 0 * γ 2 * γ 3) := by rw [gamma_one_sq]; noncomm_ring
      _ = (γ 1 * γ 1) * (γ 0 * γ 2 * γ 3) := by rw [gamma_one_sq]; noncomm_ring
      _ = γ 1 * (γ 1 * γ 0) * γ 2 * γ 3 := by noncomm_ring
      _ = -(γ 1 * (γ 0 * γ 1 * γ 2 * γ 3)) := by rw [h01]; noncomm_ring
  · calc
      γ 0 * γ 1 * γ 2 * γ 3 * γ 2 = γ 0 * γ 1 * γ 2 * (γ 3 * γ 2) := by noncomm_ring
      _ = -(γ 0 * γ 1 * (γ 2 * γ 2) * γ 3) := by rw [h23]; noncomm_ring
      _ = γ 0 * γ 1 * γ 3 := by rw [gamma_two_sq]; noncomm_ring
      _ = -(γ 2 * γ 2) * (γ 0 * γ 1 * γ 3) := by rw [gamma_two_sq]; noncomm_ring
      _ = -(γ 2 * (γ 2 * γ 0) * γ 1 * γ 3) := by noncomm_ring
      _ = γ 2 * γ 0 * (γ 2 * γ 1) * γ 3 := by
        (conv_lhs => rw [h02])
        noncomm_ring
      _ = -(γ 2 * (γ 0 * γ 1 * γ 2 * γ 3)) := by rw [h12]; noncomm_ring
  · calc
      γ 0 * γ 1 * γ 2 * γ 3 * γ 3 = γ 0 * γ 1 * γ 2 * (γ 3 * γ 3) := by noncomm_ring
      _ = -(γ 0 * γ 1 * γ 2) := by rw [gamma_three_sq]; noncomm_ring
      _ = (γ 3 * γ 3) * (γ 0 * γ 1 * γ 2) := by rw [gamma_three_sq]; noncomm_ring
      _ = γ 3 * (γ 3 * γ 0) * γ 1 * γ 2 := by noncomm_ring
      _ = -(γ 3 * γ 0 * (γ 3 * γ 1) * γ 2) := by
        (conv_lhs => rw [h03])
        noncomm_ring
      _ = γ 3 * γ 0 * γ 1 * (γ 3 * γ 2) := by
        (conv_lhs => rw [h13])
        noncomm_ring
      _ = -(γ 3 * (γ 0 * γ 1 * γ 2 * γ 3)) := by rw [h23]; noncomm_ring

theorem ι_Q13_eq_sum (x : Fin 4 → ℝ) :
    CliffordAlgebra.ι Q13 x = ∑ μ : Fin 4, x μ • γ μ := by
  have hx : x = ∑ μ : Fin 4, x μ • Pi.single μ (1 : ℝ) := by
    ext ν
    simp [Finset.sum_apply, Pi.single_apply]
  conv_lhs => rw [hx]
  simp only [map_sum, map_smul, γ]

theorem I13_anticomm_ι (v : Fin 4 → ℝ) :
    I13 * CliffordAlgebra.ι Q13 v = -(CliffordAlgebra.ι Q13 v * I13) := by
  rw [ι_Q13_eq_sum, Finset.mul_sum, Finset.sum_mul, ← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun μ _ => ?_
  rw [Algebra.mul_smul_comm, Algebra.smul_mul_assoc, I13_anticomm_gamma μ, smul_neg]

theorem gamma_mem_odd (μ : Fin 4) : γ μ ∈ CliffordAlgebra.evenOdd Q13 1 :=
  CliffordAlgebra.ι_mem_evenOdd_one Q13 (Pi.single μ 1)

theorem sigma_mem_even (k : Fin 3) : σ k ∈ CliffordAlgebra.even Q13 := by
  change σ k ∈ CliffordAlgebra.evenOdd Q13 0
  exact CliffordAlgebra.ι_mul_ι_mem_evenOdd_zero Q13 (Pi.single k.succ 1) (Pi.single 0 1)

theorem I13_mem_even : I13 ∈ CliffordAlgebra.even Q13 := by
  rw [← sigma_prod_eq_I13]
  exact Subalgebra.mul_mem _ (Subalgebra.mul_mem _ (sigma_mem_even 0) (sigma_mem_even 1))
    (sigma_mem_even 2)

theorem I13_comm_of_mem_even {x : Cl13} (hx : x ∈ CliffordAlgebra.even Q13) :
    I13 * x = x * I13 := by
  change x ∈ CliffordAlgebra.evenOdd Q13 0 at hx
  induction x, hx using CliffordAlgebra.even_induction with
  | algebraMap r => exact (Algebra.commutes r I13).symm
  | add a b _ _ ha hb =>
      rw [mul_add, add_mul, ha, hb]
  | ι_mul_ι_mul m₁ m₂ a _ ha =>
      calc
        I13 * (CliffordAlgebra.ι Q13 m₁ * CliffordAlgebra.ι Q13 m₂ * a)
            = (I13 * CliffordAlgebra.ι Q13 m₁) * CliffordAlgebra.ι Q13 m₂ * a := by
              noncomm_ring
        _ = (-(CliffordAlgebra.ι Q13 m₁ * I13)) * CliffordAlgebra.ι Q13 m₂ * a := by
              rw [I13_anticomm_ι m₁]
        _ = -(CliffordAlgebra.ι Q13 m₁ * (I13 * CliffordAlgebra.ι Q13 m₂) * a) := by
              noncomm_ring
        _ = -(CliffordAlgebra.ι Q13 m₁ * (-(CliffordAlgebra.ι Q13 m₂ * I13)) * a) := by
              rw [I13_anticomm_ι m₂]
        _ = CliffordAlgebra.ι Q13 m₁ * CliffordAlgebra.ι Q13 m₂ * (I13 * a) := by
              noncomm_ring
        _ = CliffordAlgebra.ι Q13 m₁ * CliffordAlgebra.ι Q13 m₂ * (a * I13) := by
              rw [ha]
        _ = CliffordAlgebra.ι Q13 m₁ * CliffordAlgebra.ι Q13 m₂ * a * I13 := by
              noncomm_ring

theorem I13_comm_sigma (k : Fin 3) : I13 * σ k = σ k * I13 :=
  I13_comm_of_mem_even (sigma_mem_even k)

private lemma reverse_gamma (μ : Fin 4) : CliffordAlgebra.reverse (γ μ) = γ μ :=
  CliffordAlgebra.reverse_ι _

@[simp]
theorem reverse_I13 : CliffordAlgebra.reverse I13 = I13 := by
  have h01 : γ 1 * γ 0 = -(γ 0 * γ 1) := gamma_anticomm (by decide)
  have h02 : γ 2 * γ 0 = -(γ 0 * γ 2) := gamma_anticomm (by decide)
  have h03 : γ 3 * γ 0 = -(γ 0 * γ 3) := gamma_anticomm (by decide)
  have h12 : γ 2 * γ 1 = -(γ 1 * γ 2) := gamma_anticomm (by decide)
  have h13 : γ 3 * γ 1 = -(γ 1 * γ 3) := gamma_anticomm (by decide)
  have h23 : γ 3 * γ 2 = -(γ 2 * γ 3) := gamma_anticomm (by decide)
  unfold I13
  simp only [CliffordAlgebra.reverse.map_mul, reverse_gamma]
  calc
    γ 3 * (γ 2 * (γ 1 * γ 0)) = γ 3 * γ 2 * γ 1 * γ 0 := by noncomm_ring
    _ = -(γ 2 * γ 3) * γ 1 * γ 0 := by rw [h23]
    _ = -(γ 2 * (γ 3 * γ 1) * γ 0) := by noncomm_ring
    _ = γ 2 * γ 1 * γ 3 * γ 0 := by rw [h13]; noncomm_ring
    _ = -(γ 1 * γ 2) * γ 3 * γ 0 := by rw [h12]
    _ = -(γ 1 * γ 2 * (γ 3 * γ 0)) := by noncomm_ring
    _ = γ 1 * (γ 2 * γ 0) * γ 3 := by rw [h03]; noncomm_ring
    _ = -(γ 1 * γ 0 * γ 2 * γ 3) := by rw [h02]; noncomm_ring
    _ = γ 0 * γ 1 * γ 2 * γ 3 := by rw [h01]; noncomm_ring

theorem reverse_sigma (k : Fin 3) : CliffordAlgebra.reverse (σ k) = -(σ k) := by
  unfold σ
  rw [CliffordAlgebra.reverse.map_mul, reverse_gamma, reverse_gamma]
  exact gamma_anticomm (Fin.succ_ne_zero k).symm

theorem sigma_zero_mul_one : σ 0 * σ 1 = I13 * σ 2 := by
  calc
    σ 0 * σ 1 = (σ 0 * σ 1) * (σ 2 * σ 2) := by rw [sigma_sq, mul_one]
    _ = (σ 0 * σ 1 * σ 2) * σ 2 := by noncomm_ring
    _ = I13 * σ 2 := by rw [sigma_prod_eq_I13]

theorem sigma_one_mul_two : σ 1 * σ 2 = I13 * σ 0 := by
  have h01 : σ 1 * σ 0 = -(σ 0 * σ 1) := sigma_anticomm (by decide)
  have h02 : σ 2 * σ 0 = -(σ 0 * σ 2) := sigma_anticomm (by decide)
  calc
    σ 1 * σ 2 = (σ 0 * σ 0) * (σ 1 * σ 2) := by rw [sigma_sq, one_mul]
    _ = σ 0 * (σ 0 * σ 1 * σ 2) := by noncomm_ring
    _ = σ 0 * I13 := by rw [sigma_prod_eq_I13]
    _ = I13 * σ 0 := (I13_comm_sigma 0).symm

theorem sigma_two_mul_zero : σ 2 * σ 0 = I13 * σ 1 := by
  have h12 : σ 2 * σ 1 = -(σ 1 * σ 2) := sigma_anticomm (by decide)
  have h01 : σ 1 * σ 0 = -(σ 0 * σ 1) := sigma_anticomm (by decide)
  have h20 : σ 2 * σ 0 = -(σ 0 * σ 2) := sigma_anticomm (by decide)
  calc
    σ 2 * σ 0 = (σ 2 * σ 1) * (σ 1 * σ 0) := by
      calc
        σ 2 * σ 0 = σ 2 * (σ 1 * σ 1) * σ 0 := by rw [sigma_sq, mul_one]
        _ = (σ 2 * σ 1) * (σ 1 * σ 0) := by noncomm_ring
    _ = -(σ 1 * σ 2) * (σ 1 * σ 0) := by rw [h12]
    _ = (σ 1 * σ 2) * (σ 0 * σ 1) := by rw [h01]; noncomm_ring
    _ = σ 1 * (σ 2 * σ 0) * σ 1 := by noncomm_ring
    _ = σ 1 * (-(σ 0 * σ 2)) * σ 1 := by rw [h20]
    _ = -(σ 1 * σ 0 * σ 2 * σ 1) := by noncomm_ring
    _ = (σ 0 * σ 1 * σ 2) * σ 1 := by rw [h01]; noncomm_ring
    _ = I13 * σ 1 := by rw [sigma_prod_eq_I13]

@[simp]
theorem e30_sq (k : Fin 3) : e30 k * e30 k = 1 := by
  rw [e30, CliffordAlgebra.ι_sq_scalar, Q30_single, map_one]

theorem e30_anticomm {j k : Fin 3} (h : j ≠ k) : e30 j * e30 k = -(e30 k * e30 j) := by
  exact clifford_orthogonal_vectors_anticommute Q30 _ _ (Q30_polar_single_ne h.symm)

@[simp]
theorem I30_sq : I30 * I30 = -1 := by
  have h01 : e30 1 * e30 0 = -(e30 0 * e30 1) := e30_anticomm (by decide)
  have h02 : e30 2 * e30 0 = -(e30 0 * e30 2) := e30_anticomm (by decide)
  have h12 : e30 2 * e30 1 = -(e30 1 * e30 2) := e30_anticomm (by decide)
  unfold I30
  calc
    (e30 0 * e30 1 * e30 2) * (e30 0 * e30 1 * e30 2)
        = e30 0 * e30 1 * (e30 2 * e30 0) * e30 1 * e30 2 := by noncomm_ring
    _ = -(e30 0 * (e30 1 * e30 0) * e30 2 * e30 1 * e30 2) := by rw [h02]; noncomm_ring
    _ = (e30 0 * e30 0) * e30 1 * e30 2 * e30 1 * e30 2 := by rw [h01]; noncomm_ring
    _ = e30 1 * (e30 2 * e30 1) * e30 2 := by rw [e30_sq]; noncomm_ring
    _ = -((e30 1 * e30 1) * (e30 2 * e30 2)) := by rw [h12]; noncomm_ring
    _ = -1 := by rw [e30_sq, e30_sq]; noncomm_ring

/-! ### Section 3: Non-Commutativity Witnesses (`T16`) & Scalar Embedding Check -/

theorem algebraMap_cl13_injective : Function.Injective (algebraMap ℝ Cl13) := by
  intro r₁ r₂ h
  have h1 := congrArg
    (fun x => ExteriorAlgebra.algebraMapInv (CliffordAlgebra.equivExterior Q13 x)) h
  simpa [CliffordAlgebra.equivExterior, CliffordAlgebra.changeFormEquiv_apply,
    CliffordAlgebra.changeForm_algebraMap, AlgHom.commutes] using h1

theorem one_ne_zero_cl13 : (1 : Cl13) ≠ 0 := by
  intro h
  have h10 : algebraMap ℝ Cl13 (1 : ℝ) = algebraMap ℝ Cl13 (0 : ℝ) := by
    rw [map_one, map_zero]
    exact h
  have h01 : (1 : ℝ) = 0 := algebraMap_cl13_injective h10
  norm_num at h01

def gamma0 : Cl13 := γ 0
def gamma1 : Cl13 := γ 1
def sigma0 : Cl13 := σ 0
def sigma1 : Cl13 := σ 1

theorem gamma0_gamma1_noncomm : gamma0 * gamma1 ≠ gamma1 * gamma0 := by
  intro hcomm
  change γ 0 * γ 1 = γ 1 * γ 0 at hcomm
  have hanti : γ 0 * γ 1 = -(γ 1 * γ 0) := gamma_anticomm (by decide)
  have hadd : γ 0 * γ 1 + γ 0 * γ 1 = 0 := by
    calc
      γ 0 * γ 1 + γ 0 * γ 1 = γ 1 * γ 0 + γ 0 * γ 1 := by rw [hcomm]
      _ = γ 1 * γ 0 + -(γ 1 * γ 0) := by rw [hanti]
      _ = 0 := add_neg_cancel _
  have htwo : (2 : ℝ) • (γ 0 * γ 1) = 0 := by
    rw [two_smul]
    exact hadd
  have hzero : γ 0 * γ 1 = 0 := by
    have := congrArg (fun x : Cl13 => (1 / 2 : ℝ) • x) htwo
    simpa [smul_smul, two_mul_half_real] using this
  have hcontra : (-1 : Cl13) = 0 := by
    calc
      (-1 : Cl13) = (γ 0 * γ 0) * (γ 1 * γ 1) := by
        rw [gamma_zero_sq, gamma_one_sq, one_mul]
      _ = γ 0 * (γ 0 * γ 1) * γ 1 := by noncomm_ring
      _ = 0 := by rw [hzero, mul_zero, zero_mul]
  have hone : (1 : Cl13) = 0 := by
    rw [← neg_neg (1 : Cl13), hcontra, neg_zero]
  exact one_ne_zero_cl13 hone

theorem gamma_zero_one_noncomm : γ 0 * γ 1 ≠ γ 1 * γ 0 :=
  gamma0_gamma1_noncomm

theorem sigma0_sigma1_noncomm : sigma0 * sigma1 ≠ sigma1 * sigma0 := by
  intro hcomm
  change σ 0 * σ 1 = σ 1 * σ 0 at hcomm
  have hanti : σ 0 * σ 1 = -(σ 1 * σ 0) := sigma_anticomm (by decide)
  have hadd : σ 0 * σ 1 + σ 0 * σ 1 = 0 := by
    calc
      σ 0 * σ 1 + σ 0 * σ 1 = σ 1 * σ 0 + σ 0 * σ 1 := by rw [hcomm]
      _ = σ 1 * σ 0 + -(σ 1 * σ 0) := by rw [hanti]
      _ = 0 := add_neg_cancel _
  have htwo : (2 : ℝ) • (σ 0 * σ 1) = 0 := by
    rw [two_smul]
    exact hadd
  have hzero : σ 0 * σ 1 = 0 := by
    have := congrArg (fun x : Cl13 => (1 / 2 : ℝ) • x) htwo
    simpa [smul_smul, two_mul_half_real] using this
  have hcontra : (1 : Cl13) = 0 := by
    calc
      (1 : Cl13) = (σ 0 * σ 0) * (σ 1 * σ 1) := by rw [sigma_sq, sigma_sq, one_mul]
      _ = σ 0 * (σ 0 * σ 1) * σ 1 := by noncomm_ring
      _ = 0 := by rw [hzero, mul_zero, zero_mul]
  exact one_ne_zero_cl13 hcontra

theorem sigma_zero_one_noncomm : σ 0 * σ 1 ≠ σ 1 * σ 0 :=
  sigma0_sigma1_noncomm

/-! ### Section 4: Spacetime Split Isomorphism `Cl(3,0) ≃ₐ[ℝ] Cl⁺(1,3)` -/

/-- Coordinate linear equivalence `(Fin 3 → ℝ) × ℝ ≃ₗ[ℝ] (Fin 4 → ℝ)` sending `(m, r) ↦ Fin.cons r m`. -/
def splitLinearEquiv : ((Fin 3 → ℝ) × ℝ) ≃ₗ[ℝ] (Fin 4 → ℝ) where
  toFun p := Fin.cons p.2 p.1
  map_add' p q := by
    ext i
    refine Fin.cases ?_ (fun j => ?_) i <;> simp
  map_smul' c p := by
    ext i
    refine Fin.cases ?_ (fun j => ?_) i <;> simp
  invFun x := (Fin.tail x, x 0)
  left_inv p := by
    ext <;> simp
  right_inv x := Fin.cons_self_tail x

@[simp]
theorem splitLinearEquiv_apply (m : Fin 3 → ℝ) (r : ℝ) :
    splitLinearEquiv (m, r) = Fin.cons r m :=
  rfl

@[simp]
theorem splitLinearEquiv_zero_one : splitLinearEquiv (0, 1) = Pi.single 0 1 := by
  ext i
  refine Fin.cases ?_ (fun j => ?_) i <;> simp

@[simp]
theorem splitLinearEquiv_single_zero (k : Fin 3) :
    splitLinearEquiv (Pi.single k 1, 0) = Pi.single k.succ 1 := by
  ext i
  refine Fin.cases ?_ (fun j => ?_) i
  · simp
  · simp [Pi.single_apply]

/-- Isometric equivalence between `-(CliffordAlgebra.EquivEven.Q' Q30)` and `Q13`. -/
def splitIsometry : (-(CliffordAlgebra.EquivEven.Q' Q30)).IsometryEquiv Q13 where
  toLinearEquiv := splitLinearEquiv
  map_app' p := by
    change Q13 (Fin.cons p.2 p.1) = -(CliffordAlgebra.EquivEven.Q' Q30 p)
    rw [Q13_apply, CliffordAlgebra.EquivEven.Q'_apply, Q30_apply]
    have h0 : (Fin.cons p.2 p.1 : Fin 4 → ℝ) 0 = p.2 := by simp
    have h1 : (Fin.cons p.2 p.1 : Fin 4 → ℝ) 1 = p.1 0 := by simp
    have h2 : (Fin.cons p.2 p.1 : Fin 4 → ℝ) 2 = p.1 1 := by
      rw [show (2 : Fin 4) = Fin.succ 1 from rfl]
      exact Fin.cons_succ (α := fun _ => ℝ) p.2 p.1 1
    have h3 : (Fin.cons p.2 p.1 : Fin 4 → ℝ) 3 = p.1 2 := by
      rw [show (3 : Fin 4) = Fin.succ 2 from rfl]
      exact Fin.cons_succ (α := fun _ => ℝ) p.2 p.1 2
    rw [h0, h1, h2, h3, neg_sub]
    exact q13_cons_split_helper p.2 (p.1 0) (p.1 1) (p.1 2)

/-- Canonical spacetime split algebra isomorphism `Cl(3,0) ≃ₐ[ℝ] Cl⁺(1,3)`
sending `e30 k ↦ σ k` and `I30 ↦ I13` (Gull–Lasenby–Doran §5). -/
noncomputable def spacetimeSplitEquiv : Cl30 ≃ₐ[ℝ] CliffordAlgebra.even Q13 :=
  (CliffordAlgebra.equivEven Q30).trans
    ((CliffordAlgebra.evenEquivEvenNeg (CliffordAlgebra.EquivEven.Q' Q30)).trans
      (evenEquivOfIsometry splitIsometry))

@[simp]
theorem coe_spacetimeSplitEquiv_ι (m : Fin 3 → ℝ) :
    (spacetimeSplitEquiv (CliffordAlgebra.ι Q30 m) : Cl13) =
      CliffordAlgebra.ι Q13 (Fin.cons 0 m) * γ 0 := by
  have h01 : (CliffordAlgebra.equivEven Q30 (CliffordAlgebra.ι Q30 m)) =
      (CliffordAlgebra.even.ι (CliffordAlgebra.EquivEven.Q' Q30)).bilin (0, 1) (m, 0) := by
    ext1
    exact CliffordAlgebra.toEven_ι Q30 m
  have hev :
      (CliffordAlgebra.evenEquivEvenNeg (CliffordAlgebra.EquivEven.Q' Q30)
          ((CliffordAlgebra.even.ι (CliffordAlgebra.EquivEven.Q' Q30)).bilin (0, 1) (m, 0))) =
        -(CliffordAlgebra.even.ι (-CliffordAlgebra.EquivEven.Q' Q30)).bilin (0, 1) (m, 0) := by
    exact CliffordAlgebra.evenToNeg_ι _ _ rfl (0, 1) (m, 0)
  have hcoe :
      (spacetimeSplitEquiv (CliffordAlgebra.ι Q30 m) : Cl13) =
        -(γ 0 * CliffordAlgebra.ι Q13 (Fin.cons 0 m)) := by
    simp only [spacetimeSplitEquiv, AlgEquiv.trans_apply, h01, hev, map_neg, Subalgebra.coe_neg]
    congr 1
    change CliffordAlgebra.equivOfIsometry splitIsometry
        (CliffordAlgebra.ι (-CliffordAlgebra.EquivEven.Q' Q30) (0, 1) *
          CliffordAlgebra.ι (-CliffordAlgebra.EquivEven.Q' Q30) (m, 0)) =
      γ 0 * CliffordAlgebra.ι Q13 (Fin.cons 0 m)
    rw [map_mul, CliffordAlgebra.equivOfIsometry_apply, CliffordAlgebra.equivOfIsometry_apply,
      CliffordAlgebra.map_apply_ι, CliffordAlgebra.map_apply_ι]
    have hzero : splitIsometry.toIsometry (0, 1) = Pi.single 0 1 := splitLinearEquiv_zero_one
    have hm : splitIsometry.toIsometry (m, 0) = Fin.cons 0 m := rfl
    rw [hzero, hm]
    rfl
  have horth : QuadraticMap.polar Q13 (Fin.cons 0 m) (Pi.single 0 1) = 0 := by
    rw [Q13_polar]
    simp
  have hanti : γ 0 * CliffordAlgebra.ι Q13 (Fin.cons 0 m) =
      -(CliffordAlgebra.ι Q13 (Fin.cons 0 m) * γ 0) := by
    exact clifford_orthogonal_vectors_anticommute Q13 _ _ horth
  rw [hcoe, hanti, neg_neg]

@[simp]
theorem coe_spacetimeSplitEquiv_e30 (k : Fin 3) :
    (spacetimeSplitEquiv (e30 k) : Cl13) = σ k := by
  rw [e30, coe_spacetimeSplitEquiv_ι]
  have hsingle : Fin.cons (0 : ℝ) (Pi.single k 1 : Fin 3 → ℝ) = (Pi.single k.succ 1 : Fin 4 → ℝ) := by
    ext i
    refine Fin.cases ?_ (fun j => ?_) i <;> simp [Pi.single_apply]
  rw [hsingle]
  rfl

@[simp]
theorem coe_spacetimeSplitEquiv_I30 :
    (spacetimeSplitEquiv I30 : Cl13) = I13 := by
  rw [I30, map_mul, map_mul]
  simp only [Subalgebra.coe_mul, coe_spacetimeSplitEquiv_e30]
  exact sigma_prod_eq_I13

theorem spacetimeSplitEquiv_symm_sigma (k : Fin 3) :
    spacetimeSplitEquiv.symm ⟨σ k, sigma_mem_even k⟩ = e30 k := by
  apply spacetimeSplitEquiv.injective
  rw [spacetimeSplitEquiv.apply_symm_apply]
  ext1
  exact (coe_spacetimeSplitEquiv_e30 k).symm

theorem spacetimeSplitEquiv_symm_I13 :
    spacetimeSplitEquiv.symm ⟨I13, I13_mem_even⟩ = I30 := by
  apply spacetimeSplitEquiv.injective
  rw [spacetimeSplitEquiv.apply_symm_apply]
  ext1
  exact coe_spacetimeSplitEquiv_I30.symm

theorem coe_spacetimeSplitEquiv_star (x : Cl30) :
    (spacetimeSplitEquiv (star x) : Cl13) =
      CliffordAlgebra.reverse (spacetimeSplitEquiv x : Cl13) := by
  induction x using CliffordAlgebra.induction with
  | algebraMap r =>
      simp [CliffordAlgebra.star_algebraMap, CliffordAlgebra.reverse.commutes]
  | ι m =>
      rw [CliffordAlgebra.star_ι, map_neg, Subalgebra.coe_neg, coe_spacetimeSplitEquiv_ι,
        CliffordAlgebra.reverse.map_mul, CliffordAlgebra.reverse_ι, γ, CliffordAlgebra.reverse_ι]
      have horth : QuadraticMap.polar Q13 (Fin.cons 0 m) (Pi.single 0 1) = 0 := by
        rw [Q13_polar]
        simp
      have hanti : γ 0 * CliffordAlgebra.ι Q13 (Fin.cons 0 m) =
          -(CliffordAlgebra.ι Q13 (Fin.cons 0 m) * γ 0) :=
        clifford_orthogonal_vectors_anticommute Q13 _ _ horth
      exact hanti.symm
  | mul a b ha hb =>
      rw [star_mul, map_mul, map_mul, Subalgebra.coe_mul, Subalgebra.coe_mul,
        CliffordAlgebra.reverse.map_mul, ha, hb]
  | add a b ha hb =>
      rw [star_add, map_add, map_add, Subalgebra.coe_add, Subalgebra.coe_add,
        map_add, ha, hb]

def e30_0 : Cl30 := e30 0
def e30_1 : Cl30 := e30 1

theorem e30_0_e30_1_noncomm : e30_0 * e30_1 ≠ e30_1 * e30_0 := by
  intro hcomm
  have hm := congrArg (fun z : Cl30 => (spacetimeSplitEquiv z : Cl13)) hcomm
  simp only [e30_0, e30_1, map_mul, Subalgebra.coe_mul, coe_spacetimeSplitEquiv_e30] at hm
  exact sigma0_sigma1_noncomm hm

/-! ### Section 5: Faraday Bivector Split `F = E + I B` (Eqs. 5.9–5.10) -/

/-- Electric relative-vector part `E = 1/2 (F - γ 0 * F * γ 0)` of a spacetime multivector
(Gull–Lasenby–Doran §5 Eq. 5.10). -/
def faradayE (F : Cl13) : Cl13 := (1 / 2 : ℝ) • (F - γ 0 * F * γ 0)

/-- Magnetic bivector part `I B = 1/2 (F + γ 0 * F * γ 0)` of a spacetime multivector
(Gull–Lasenby–Doran §5 Eq. 5.10). -/
def faradayBI (F : Cl13) : Cl13 := (1 / 2 : ℝ) • (F + γ 0 * F * γ 0)

@[simp]
theorem faradayE_zero : faradayE 0 = 0 := by
  simp [faradayE]

@[simp]
theorem faradayBI_zero : faradayBI 0 = 0 := by
  simp [faradayBI]

theorem faradayE_add (F G : Cl13) : faradayE (F + G) = faradayE F + faradayE G := by
  unfold faradayE
  rw [← smul_add]
  congr 1
  noncomm_ring

theorem faradayE_smul (c : ℝ) (F : Cl13) : faradayE (c • F) = c • faradayE F := by
  unfold faradayE
  rw [Algebra.mul_smul_comm, Algebra.smul_mul_assoc, ← smul_sub, smul_comm (1 / 2 : ℝ) c]

theorem faradayE_sub (F G : Cl13) : faradayE (F - G) = faradayE F - faradayE G := by
  rw [sub_eq_add_neg, faradayE_add, ← neg_one_smul ℝ G, faradayE_smul, neg_one_smul,
    ← sub_eq_add_neg]

theorem faradayE_neg (F : Cl13) : faradayE (-F) = -faradayE F := by
  rw [← neg_one_smul ℝ F, faradayE_smul, neg_one_smul]

theorem faradayBI_add (F G : Cl13) : faradayBI (F + G) = faradayBI F + faradayBI G := by
  unfold faradayBI
  rw [← smul_add]
  congr 1
  noncomm_ring

theorem faradayBI_smul (c : ℝ) (F : Cl13) : faradayBI (c • F) = c • faradayBI F := by
  unfold faradayBI
  rw [Algebra.mul_smul_comm, Algebra.smul_mul_assoc, ← smul_add, smul_comm (1 / 2 : ℝ) c]

theorem faradayBI_sub (F G : Cl13) : faradayBI (F - G) = faradayBI F - faradayBI G := by
  rw [sub_eq_add_neg, faradayBI_add, ← neg_one_smul ℝ G, faradayBI_smul, neg_one_smul,
    ← sub_eq_add_neg]

theorem faradayBI_neg (F : Cl13) : faradayBI (-F) = -faradayBI F := by
  rw [← neg_one_smul ℝ F, faradayBI_smul, neg_one_smul]

/-- `faradayE` as an `ℝ`-linear map `Cl13 →ₗ[ℝ] Cl13`. -/
def faradayELin : Cl13 →ₗ[ℝ] Cl13 where
  toFun := faradayE
  map_add' := faradayE_add
  map_smul' := faradayE_smul

/-- `faradayBI` as an `ℝ`-linear map `Cl13 →ₗ[ℝ] Cl13`. -/
def faradayBILin : Cl13 →ₗ[ℝ] Cl13 where
  toFun := faradayBI
  map_add' := faradayBI_add
  map_smul' := faradayBI_smul

/-- General spacetime split `F = faradayE F + faradayBI F` (Eq. 5.9). -/
theorem faraday_split_eq (F : Cl13) : F = faradayE F + faradayBI F := by
  unfold faradayE faradayBI
  rw [← smul_add, sub_add_add_cancel, ← two_smul ℝ F, smul_smul, half_mul_two, one_smul]

theorem gamma_zero_mul_faradayE (F : Cl13) :
    γ 0 * faradayE F = -(faradayE F * γ 0) := by
  unfold faradayE
  rw [Algebra.mul_smul_comm, Algebra.smul_mul_assoc, ← smul_neg]
  congr 1
  calc
    γ 0 * (F - γ 0 * F * γ 0) = γ 0 * F - (γ 0 * γ 0) * F * γ 0 := by noncomm_ring
    _ = γ 0 * F - F * γ 0 := by rw [gamma_zero_sq, one_mul]
    _ = -(F * γ 0 - γ 0 * F * (γ 0 * γ 0)) := by rw [gamma_zero_sq, mul_one]; noncomm_ring
    _ = -((F - γ 0 * F * γ 0) * γ 0) := by noncomm_ring

theorem gamma_zero_mul_faradayBI (F : Cl13) :
    γ 0 * faradayBI F = faradayBI F * γ 0 := by
  unfold faradayBI
  rw [Algebra.mul_smul_comm, Algebra.smul_mul_assoc]
  congr 1
  calc
    γ 0 * (F + γ 0 * F * γ 0) = γ 0 * F + (γ 0 * γ 0) * F * γ 0 := by noncomm_ring
    _ = γ 0 * F + F * γ 0 := by rw [gamma_zero_sq, one_mul]
    _ = F * γ 0 + γ 0 * F := by abel
    _ = F * γ 0 + γ 0 * F * (γ 0 * γ 0) := by rw [gamma_zero_sq, mul_one]
    _ = (F + γ 0 * F * γ 0) * γ 0 := by noncomm_ring

theorem faradayE_idem (F : Cl13) : faradayE (faradayE F) = faradayE F := by
  unfold faradayE
  have h : γ 0 * ((1 / 2 : ℝ) • (F - γ 0 * F * γ 0)) * γ 0 =
      -((1 / 2 : ℝ) • (F - γ 0 * F * γ 0)) := by
    rw [Algebra.mul_smul_comm, Algebra.smul_mul_assoc, ← smul_neg]
    congr 1
    calc
      γ 0 * (F - γ 0 * F * γ 0) * γ 0
          = γ 0 * F * γ 0 - (γ 0 * γ 0) * F * (γ 0 * γ 0) := by noncomm_ring
      _ = -(F - γ 0 * F * γ 0) := by rw [gamma_zero_sq, one_mul, mul_one]; noncomm_ring
  rw [h, sub_neg_eq_add, ← two_smul ℝ _, smul_smul, half_mul_two, one_smul]

theorem faradayBI_idem (F : Cl13) : faradayBI (faradayBI F) = faradayBI F := by
  unfold faradayBI
  have h : γ 0 * ((1 / 2 : ℝ) • (F + γ 0 * F * γ 0)) * γ 0 =
      (1 / 2 : ℝ) • (F + γ 0 * F * γ 0) := by
    rw [Algebra.mul_smul_comm, Algebra.smul_mul_assoc]
    congr 1
    calc
      γ 0 * (F + γ 0 * F * γ 0) * γ 0
          = γ 0 * F * γ 0 + (γ 0 * γ 0) * F * (γ 0 * γ 0) := by noncomm_ring
      _ = F + γ 0 * F * γ 0 := by rw [gamma_zero_sq, one_mul, mul_one]; noncomm_ring
  rw [h, ← two_smul ℝ _, smul_smul, half_mul_two, one_smul]

theorem faradayE_faradayBI (F : Cl13) : faradayE (faradayBI F) = 0 := by
  unfold faradayE faradayBI
  have h : γ 0 * ((1 / 2 : ℝ) • (F + γ 0 * F * γ 0)) * γ 0 =
      (1 / 2 : ℝ) • (F + γ 0 * F * γ 0) := by
    rw [Algebra.mul_smul_comm, Algebra.smul_mul_assoc]
    congr 1
    calc
      γ 0 * (F + γ 0 * F * γ 0) * γ 0
          = γ 0 * F * γ 0 + (γ 0 * γ 0) * F * (γ 0 * γ 0) := by noncomm_ring
      _ = F + γ 0 * F * γ 0 := by rw [gamma_zero_sq, one_mul, mul_one]; noncomm_ring
  rw [h, sub_self, smul_zero]

theorem faradayBI_faradayE (F : Cl13) : faradayBI (faradayE F) = 0 := by
  unfold faradayE faradayBI
  have h : γ 0 * ((1 / 2 : ℝ) • (F - γ 0 * F * γ 0)) * γ 0 =
      -((1 / 2 : ℝ) • (F - γ 0 * F * γ 0)) := by
    rw [Algebra.mul_smul_comm, Algebra.smul_mul_assoc, ← smul_neg]
    congr 1
    calc
      γ 0 * (F - γ 0 * F * γ 0) * γ 0
          = γ 0 * F * γ 0 - (γ 0 * γ 0) * F * (γ 0 * γ 0) := by noncomm_ring
      _ = -(F - γ 0 * F * γ 0) := by rw [gamma_zero_sq, one_mul, mul_one]; noncomm_ring
  rw [h, add_neg_cancel, smul_zero]

theorem faradayE_mem_even {F : Cl13} (hF : F ∈ CliffordAlgebra.even Q13) :
    faradayE F ∈ CliffordAlgebra.even Q13 := by
  unfold faradayE
  have hg0 : γ 0 ∈ CliffordAlgebra.evenOdd Q13 1 := gamma_mem_odd 0
  have hF0 : F ∈ CliffordAlgebra.evenOdd Q13 0 := hF
  have hconj : γ 0 * F * γ 0 ∈ CliffordAlgebra.evenOdd Q13 0 := by
    have h1 := SetLike.mul_mem_graded hg0 hF0
    have h2 := SetLike.mul_mem_graded h1 hg0
    have hidx : ((1 : ZMod 2) + 0 + 1 : ZMod 2) = 0 := by decide
    rwa [hidx] at h2
  exact Subalgebra.smul_mem _ (Subalgebra.sub_mem _ hF hconj) _

theorem faradayBI_mem_even {F : Cl13} (hF : F ∈ CliffordAlgebra.even Q13) :
    faradayBI F ∈ CliffordAlgebra.even Q13 := by
  unfold faradayBI
  have hg0 : γ 0 ∈ CliffordAlgebra.evenOdd Q13 1 := gamma_mem_odd 0
  have hF0 : F ∈ CliffordAlgebra.evenOdd Q13 0 := hF
  have hconj : γ 0 * F * γ 0 ∈ CliffordAlgebra.evenOdd Q13 0 := by
    have h1 := SetLike.mul_mem_graded hg0 hF0
    have h2 := SetLike.mul_mem_graded h1 hg0
    have hidx : ((1 : ZMod 2) + 0 + 1 : ZMod 2) = 0 := by decide
    rwa [hidx] at h2
  exact Subalgebra.smul_mem _ (Subalgebra.add_mem _ hF hconj) _

private lemma gamma_zero_mul_sigma_mul_gamma_zero (k : Fin 3) :
    γ 0 * σ k * γ 0 = -(σ k) := by
  unfold σ
  have h0k : γ 0 * γ k.succ = -(γ k.succ * γ 0) := gamma_anticomm (Fin.succ_ne_zero k).symm
  calc
    γ 0 * (γ k.succ * γ 0) * γ 0 = (γ 0 * γ k.succ) * (γ 0 * γ 0) := by noncomm_ring
    _ = -(γ k.succ * γ 0) := by rw [h0k, gamma_zero_sq, mul_one]

private lemma gamma_zero_mul_I13_sigma_mul_gamma_zero (k : Fin 3) :
    γ 0 * (I13 * σ k) * γ 0 = I13 * σ k := by
  have h0 : γ 0 * I13 = -(I13 * γ 0) := by
    rw [I13_anticomm_gamma 0, neg_neg]
  calc
    γ 0 * (I13 * σ k) * γ 0 = (γ 0 * I13) * (σ k * γ 0) := by noncomm_ring
    _ = (-(I13 * γ 0)) * (σ k * γ 0) := by rw [h0]
    _ = -(I13 * (γ 0 * σ k * γ 0)) := by noncomm_ring
    _ = -(I13 * (-(σ k))) := by rw [gamma_zero_mul_sigma_mul_gamma_zero]
    _ = I13 * σ k := by noncomm_ring

@[simp]
theorem faradayE_sigma (k : Fin 3) : faradayE (σ k) = σ k := by
  unfold faradayE
  rw [gamma_zero_mul_sigma_mul_gamma_zero, sub_neg_eq_add, ← two_smul ℝ _, smul_smul,
    half_mul_two, one_smul]

@[simp]
theorem faradayBI_sigma (k : Fin 3) : faradayBI (σ k) = 0 := by
  unfold faradayBI
  rw [gamma_zero_mul_sigma_mul_gamma_zero, add_neg_cancel, smul_zero]

@[simp]
theorem faradayE_I13_sigma (k : Fin 3) : faradayE (I13 * σ k) = 0 := by
  unfold faradayE
  rw [gamma_zero_mul_I13_sigma_mul_gamma_zero, sub_self, smul_zero]

@[simp]
theorem faradayBI_I13_sigma (k : Fin 3) : faradayBI (I13 * σ k) = I13 * σ k := by
  unfold faradayBI
  rw [gamma_zero_mul_I13_sigma_mul_gamma_zero, ← two_smul ℝ _, smul_smul,
    half_mul_two, one_smul]

theorem gamma_zero_succ (k : Fin 3) : γ 0 * γ k.succ = -(σ k) := by
  unfold σ
  exact gamma_anticomm (Fin.succ_ne_zero k).symm

private lemma gamma_01_eq : γ 0 * γ 1 = -(σ 0) := gamma_zero_succ 0
private lemma gamma_02_eq : γ 0 * γ 2 = -(σ 1) := gamma_zero_succ 1
private lemma gamma_03_eq : γ 0 * γ 3 = -(σ 2) := gamma_zero_succ 2

theorem gamma_23_eq : γ 2 * γ 3 = -(I13 * σ 0) := by
  have h12 : γ 2 * γ 1 = -(γ 1 * γ 2) := gamma_anticomm (by decide)
  have h13 : γ 3 * γ 1 = -(γ 1 * γ 3) := gamma_anticomm (by decide)
  have h02 : γ 2 * γ 0 = -(γ 0 * γ 2) := gamma_anticomm (by decide)
  have h03 : γ 3 * γ 0 = -(γ 0 * γ 3) := gamma_anticomm (by decide)
  have h : I13 * σ 0 = -(γ 2 * γ 3) := by
    unfold I13 σ
    change (γ 0 * γ 1 * γ 2 * γ 3) * (γ 1 * γ 0) = -(γ 2 * γ 3)
    calc
      (γ 0 * γ 1 * γ 2 * γ 3) * (γ 1 * γ 0)
          = γ 0 * γ 1 * γ 2 * (γ 3 * γ 1) * γ 0 := by noncomm_ring
      _ = -(γ 0 * γ 1 * (γ 2 * γ 1) * γ 3 * γ 0) := by rw [h13]; noncomm_ring
      _ = γ 0 * (γ 1 * γ 1) * γ 2 * γ 3 * γ 0 := by rw [h12]; noncomm_ring
      _ = -(γ 0 * γ 2 * (γ 3 * γ 0)) := by rw [gamma_one_sq]; noncomm_ring
      _ = γ 0 * (γ 2 * γ 0) * γ 3 := by rw [h03]; noncomm_ring
      _ = -((γ 0 * γ 0) * γ 2 * γ 3) := by rw [h02]; noncomm_ring
      _ = -(γ 2 * γ 3) := by rw [gamma_zero_sq, one_mul]
  rw [h, neg_neg]

theorem gamma_13_eq : γ 1 * γ 3 = I13 * σ 1 := by
  have h23 : γ 3 * γ 2 = -(γ 2 * γ 3) := gamma_anticomm (by decide)
  have h01 : γ 1 * γ 0 = -(γ 0 * γ 1) := gamma_anticomm (by decide)
  have h03 : γ 3 * γ 0 = -(γ 0 * γ 3) := gamma_anticomm (by decide)
  unfold I13 σ
  change γ 1 * γ 3 = (γ 0 * γ 1 * γ 2 * γ 3) * (γ 2 * γ 0)
  symm
  calc
    (γ 0 * γ 1 * γ 2 * γ 3) * (γ 2 * γ 0)
        = γ 0 * γ 1 * γ 2 * (γ 3 * γ 2) * γ 0 := by noncomm_ring
    _ = -(γ 0 * γ 1 * (γ 2 * γ 2) * γ 3 * γ 0) := by rw [h23]; noncomm_ring
    _ = γ 0 * γ 1 * (γ 3 * γ 0) := by rw [gamma_two_sq]; noncomm_ring
    _ = -(γ 0 * (γ 1 * γ 0) * γ 3) := by rw [h03]; noncomm_ring
    _ = (γ 0 * γ 0) * γ 1 * γ 3 := by rw [h01]; noncomm_ring
    _ = γ 1 * γ 3 := by rw [gamma_zero_sq, one_mul]

theorem gamma_12_eq : γ 1 * γ 2 = -(I13 * σ 2) := by
  have h01 : γ 1 * γ 0 = -(γ 0 * γ 1) := gamma_anticomm (by decide)
  have h02 : γ 2 * γ 0 = -(γ 0 * γ 2) := gamma_anticomm (by decide)
  have h : I13 * σ 2 = -(γ 1 * γ 2) := by
    unfold I13 σ
    change (γ 0 * γ 1 * γ 2 * γ 3) * (γ 3 * γ 0) = -(γ 1 * γ 2)
    calc
      (γ 0 * γ 1 * γ 2 * γ 3) * (γ 3 * γ 0)
          = γ 0 * γ 1 * γ 2 * (γ 3 * γ 3) * γ 0 := by noncomm_ring
      _ = -(γ 0 * γ 1 * (γ 2 * γ 0)) := by rw [gamma_three_sq]; noncomm_ring
      _ = γ 0 * (γ 1 * γ 0) * γ 2 := by rw [h02]; noncomm_ring
      _ = -((γ 0 * γ 0) * γ 1 * γ 2) := by rw [h01]; noncomm_ring
      _ = -(γ 1 * γ 2) := by rw [gamma_zero_sq, one_mul]
  rw [h, neg_neg]

/-- Submodule of `Cl13` spanned by the 6 basis bivectors `γ μ * γ ν` (`μ < ν`). -/
def bivectorSubmodule : Submodule ℝ Cl13 :=
  Submodule.span ℝ {x : Cl13 | ∃ μ ν : Fin 4, μ < ν ∧ x = γ μ * γ ν}

theorem faradayE_bivector_coords (c : Fin 4 → Fin 4 → ℝ) :
    let F := ∑ μ : Fin 4, ∑ ν : Fin 4, if μ < ν then c μ ν • (γ μ * γ ν) else 0
    faradayE F = (-c 0 1) • σ 0 + (-c 0 2) • σ 1 + (-c 0 3) • σ 2 := by
  intro F
  dsimp [F]
  simp only [Fin.sum_univ_four]
  simp only [show ¬((0 : Fin 4) < 0) by decide, show (0 : Fin 4) < 1 by decide,
    show (0 : Fin 4) < 2 by decide, show (0 : Fin 4) < 3 by decide,
    show ¬((1 : Fin 4) < 0) by decide, show ¬((1 : Fin 4) < 1) by decide,
    show (1 : Fin 4) < 2 by decide, show (1 : Fin 4) < 3 by decide,
    show ¬((2 : Fin 4) < 0) by decide, show ¬((2 : Fin 4) < 1) by decide,
    show ¬((2 : Fin 4) < 2) by decide, show (2 : Fin 4) < 3 by decide,
    show ¬((3 : Fin 4) < 0) by decide, show ¬((3 : Fin 4) < 1) by decide,
    show ¬((3 : Fin 4) < 2) by decide, show ¬((3 : Fin 4) < 3) by decide,
    ite_true, ite_false, zero_add, add_zero]
  rw [gamma_01_eq, gamma_02_eq, gamma_03_eq,
    gamma_12_eq, gamma_13_eq, gamma_23_eq]
  simp only [faradayE_add, faradayE_smul, faradayE_sigma, faradayE_I13_sigma,
    smul_zero, add_zero, smul_neg, ← neg_smul]

theorem faradayBI_bivector_coords (c : Fin 4 → Fin 4 → ℝ) :
    let F := ∑ μ : Fin 4, ∑ ν : Fin 4, if μ < ν then c μ ν • (γ μ * γ ν) else 0
    faradayBI F = I13 * ((-c 2 3) • σ 0 + c 1 3 • σ 1 + (-c 1 2) • σ 2) := by
  intro F
  dsimp [F]
  simp only [Fin.sum_univ_four]
  simp only [show ¬((0 : Fin 4) < 0) by decide, show (0 : Fin 4) < 1 by decide,
    show (0 : Fin 4) < 2 by decide, show (0 : Fin 4) < 3 by decide,
    show ¬((1 : Fin 4) < 0) by decide, show ¬((1 : Fin 4) < 1) by decide,
    show (1 : Fin 4) < 2 by decide, show (1 : Fin 4) < 3 by decide,
    show ¬((2 : Fin 4) < 0) by decide, show ¬((2 : Fin 4) < 1) by decide,
    show ¬((2 : Fin 4) < 2) by decide, show (2 : Fin 4) < 3 by decide,
    show ¬((3 : Fin 4) < 0) by decide, show ¬((3 : Fin 4) < 1) by decide,
    show ¬((3 : Fin 4) < 2) by decide, show ¬((3 : Fin 4) < 3) by decide,
    ite_true, ite_false, zero_add, add_zero]
  rw [gamma_01_eq, gamma_02_eq, gamma_03_eq,
    gamma_12_eq, gamma_13_eq, gamma_23_eq]
  simp only [faradayBI_add, faradayBI_smul, faradayBI_sigma, faradayBI_I13_sigma,
    smul_zero, zero_add, add_zero, smul_neg, ← neg_smul]
  simp only [mul_add, Algebra.mul_smul_comm]
  abel

theorem sigma_mem_bivectorSubmodule (k : Fin 3) : σ k ∈ bivectorSubmodule := by
  have hmem : γ 0 * γ k.succ ∈ bivectorSubmodule :=
    Submodule.subset_span ⟨0, k.succ, Fin.succ_pos k, rfl⟩
  have hneg : -(γ 0 * γ k.succ) ∈ bivectorSubmodule := Submodule.neg_mem _ hmem
  rwa [gamma_zero_succ, neg_neg] at hneg

theorem I13_mul_sigma_mem_bivectorSubmodule (k : Fin 3) :
    I13 * σ k ∈ bivectorSubmodule := by
  fin_cases k
  · have hmem : γ 2 * γ 3 ∈ bivectorSubmodule := Submodule.subset_span ⟨2, 3, by decide, rfl⟩
    have hneg : -(γ 2 * γ 3) ∈ bivectorSubmodule := Submodule.neg_mem _ hmem
    rwa [gamma_23_eq, neg_neg] at hneg
  · have hmem : γ 1 * γ 3 ∈ bivectorSubmodule := Submodule.subset_span ⟨1, 3, by decide, rfl⟩
    rwa [gamma_13_eq] at hmem
  · have hmem : γ 1 * γ 2 ∈ bivectorSubmodule := Submodule.subset_span ⟨1, 2, by decide, rfl⟩
    have hneg : -(γ 1 * γ 2) ∈ bivectorSubmodule := Submodule.neg_mem _ hmem
    rwa [gamma_12_eq, neg_neg] at hneg

theorem mem_bivectorSubmodule_iff (F : Cl13) :
    F ∈ bivectorSubmodule ↔
      ∃ E B : Fin 3 → ℝ, F = (∑ k : Fin 3, E k • σ k) + I13 * (∑ k : Fin 3, B k • σ k) := by
  constructor
  · intro hF
    refine Submodule.span_induction ?_ ?_ ?_ ?_ hF
    · rintro x ⟨μ, ν, hμν, rfl⟩
      fin_cases μ <;> fin_cases ν <;> simp at hμν
      · refine ⟨![-1, 0, 0], 0, ?_⟩
        change γ 0 * γ 1 = _
        rw [gamma_01_eq]
        simp [Fin.sum_univ_three]
      · refine ⟨![0, -1, 0], 0, ?_⟩
        change γ 0 * γ 2 = _
        rw [gamma_02_eq]
        simp [Fin.sum_univ_three]
      · refine ⟨![0, 0, -1], 0, ?_⟩
        change γ 0 * γ 3 = _
        rw [gamma_03_eq]
        simp [Fin.sum_univ_three]
      · refine ⟨0, ![0, 0, -1], ?_⟩
        change γ 1 * γ 2 = _
        rw [gamma_12_eq]
        simp [Fin.sum_univ_three]
      · refine ⟨0, ![0, 1, 0], ?_⟩
        change γ 1 * γ 3 = _
        rw [gamma_13_eq]
        simp [Fin.sum_univ_three]
      · refine ⟨0, ![-1, 0, 0], ?_⟩
        change γ 2 * γ 3 = _
        rw [gamma_23_eq]
        simp [Fin.sum_univ_three]
    · exact ⟨0, 0, by simp⟩
    · rintro x y _ _ ⟨Ex, Bx, rfl⟩ ⟨Ey, By, rfl⟩
      refine ⟨Ex + Ey, Bx + By, ?_⟩
      simp only [Pi.add_apply, add_smul, Finset.sum_add_distrib, mul_add]
      abel
    · rintro c x _ ⟨Ex, Bx, rfl⟩
      refine ⟨c • Ex, c • Bx, ?_⟩
      simp only [Pi.smul_apply, smul_eq_mul, ← smul_smul, ← Finset.smul_sum, smul_add,
        Algebra.mul_smul_comm]
  · rintro ⟨E, B, rfl⟩
    refine Submodule.add_mem _ (Submodule.sum_mem _ fun k _ =>
      Submodule.smul_mem _ _ (sigma_mem_bivectorSubmodule k)) ?_
    rw [Finset.mul_sum]
    refine Submodule.sum_mem _ fun k _ => ?_
    rw [Algebra.mul_smul_comm]
    exact Submodule.smul_mem _ _ (I13_mul_sigma_mem_bivectorSubmodule k)

theorem faradayE_faradayBI_of_mem_bivectorSubmodule {F : Cl13} (hF : F ∈ bivectorSubmodule) :
    ∃ E B : Fin 3 → ℝ,
      faradayE F = ∑ k : Fin 3, E k • σ k ∧
        faradayBI F = I13 * (∑ k : Fin 3, B k • σ k) := by
  obtain ⟨E, B, hEB⟩ := (mem_bivectorSubmodule_iff F).mp hF
  refine ⟨E, B, ?_, ?_⟩
  · rw [hEB, faradayE_add, Finset.mul_sum]
    change faradayELin (∑ k, E k • σ k) + faradayELin (∑ k, I13 * (B k • σ k)) = _
    simp only [map_sum, faradayELin, LinearMap.coe_mk, AddHom.coe_mk, faradayE_smul,
      faradayE_sigma, Algebra.mul_smul_comm, faradayE_I13_sigma, smul_zero, Finset.sum_const_zero,
      add_zero]
  · rw [hEB, faradayBI_add, Finset.mul_sum]
    have hE0 : faradayBI (∑ k : Fin 3, E k • σ k) = 0 := by
      change faradayBILin (∑ k, E k • σ k) = 0
      simp only [map_sum, faradayBILin, LinearMap.coe_mk, AddHom.coe_mk, faradayBI_smul,
        faradayBI_sigma, smul_zero, Finset.sum_const_zero]
    have hB1 : faradayBI (∑ k : Fin 3, I13 * (B k • σ k)) = ∑ k : Fin 3, I13 * (B k • σ k) := by
      change faradayBILin (∑ k, I13 * (B k • σ k)) = _
      simp only [map_sum, faradayBILin, LinearMap.coe_mk, AddHom.coe_mk, Algebra.mul_smul_comm,
        faradayBI_smul, faradayBI_I13_sigma]
    rw [hE0, zero_add, hB1]

/-! ### Section 6: Canonical STA Dirac Spinor Form (Eq. 5.13) -/

/-- Dual/chiral phase factor `exp(I β / 2) = cos(β / 2) + sin(β / 2) • I13` in `Cl⁺(1,3)`. -/
def diracPhase (β : ℝ) : Cl13 :=
  Real.cos (β / 2) • (1 : Cl13) + Real.sin (β / 2) • I13

/-- Canonical STA Dirac spinor `ψ = √ρ exp(I β / 2) R` (Gull–Lasenby–Doran §5 Eq. 5.13). -/
def diracSpinor (ρ β : ℝ) (R : Cl13) : Cl13 :=
  Real.sqrt ρ • (diracPhase β * R)

/-- Even-subalgebra STA Dirac spinor `ψ ∈ Cl⁺(1,3)`. -/
def diracSpinorEven (ρ β : ℝ) (R : CliffordAlgebra.even Q13) : CliffordAlgebra.even Q13 :=
  Real.sqrt ρ • (⟨diracPhase β, by
    unfold diracPhase
    exact Subalgebra.add_mem _ (Subalgebra.smul_mem _ (Subalgebra.one_mem _) _)
      (Subalgebra.smul_mem _ I13_mem_even _)⟩ * R)

theorem diracPhase_mem_even (β : ℝ) : diracPhase β ∈ CliffordAlgebra.even Q13 := by
  unfold diracPhase
  exact Subalgebra.add_mem _ (Subalgebra.smul_mem _ (Subalgebra.one_mem _) _)
    (Subalgebra.smul_mem _ I13_mem_even _)

@[simp]
theorem reverse_diracPhase (β : ℝ) : CliffordAlgebra.reverse (diracPhase β) = diracPhase β := by
  simp only [diracPhase, map_add, map_smul, CliffordAlgebra.reverse.map_one, reverse_I13]

theorem diracPhase_mul_self (β : ℝ) :
    diracPhase β * diracPhase β = Real.cos β • (1 : Cl13) + Real.sin β • I13 := by
  unfold diracPhase
  rw [add_mul, mul_add, mul_add]
  simp only [Algebra.smul_mul_assoc, Algebra.mul_smul_comm, one_mul, mul_one, I13_sq, smul_neg,
    smul_smul]
  rw [mul_comm (Real.cos (β / 2)) (Real.sin (β / 2))]
  have h1 :
      (Real.cos (β / 2) * Real.cos (β / 2)) • (1 : Cl13) +
          (Real.sin (β / 2) * Real.cos (β / 2)) • I13 +
          ((Real.sin (β / 2) * Real.cos (β / 2)) • I13 +
            -((Real.sin (β / 2) * Real.sin (β / 2)) • (1 : Cl13))) =
        (Real.cos (β / 2) ^ 2 - Real.sin (β / 2) ^ 2) • (1 : Cl13) +
          (2 * Real.sin (β / 2) * Real.cos (β / 2)) • I13 := by
    rw [pow_two, pow_two, sub_smul, two_mul, add_mul, add_smul]
    abel
  rw [h1, cos_half_sq_sub_sin_half_sq, two_sin_half_cos_half]

theorem diracSpinor_mem_even {ρ β : ℝ} {R : Cl13} (hR : R ∈ CliffordAlgebra.even Q13) :
    diracSpinor ρ β R ∈ CliffordAlgebra.even Q13 := by
  unfold diracSpinor
  exact Subalgebra.smul_mem _ (Subalgebra.mul_mem _ (diracPhase_mem_even β) hR) _

theorem diracSpinor_eq_mul_phase {ρ β : ℝ} {R : Cl13} (hR : R ∈ CliffordAlgebra.even Q13) :
    diracSpinor ρ β R = Real.sqrt ρ • (R * diracPhase β) := by
  unfold diracSpinor diracPhase
  congr 1
  rw [add_mul, mul_add]
  simp only [Algebra.smul_mul_assoc, Algebra.mul_smul_comm, one_mul, mul_one,
    I13_comm_of_mem_even hR]

theorem diracSpinor_mul_reverse {ρ β : ℝ} {R : Cl13}
    (hρ : 0 ≤ ρ) (hR : R * CliffordAlgebra.reverse R = 1) :
    diracSpinor ρ β R * CliffordAlgebra.reverse (diracSpinor ρ β R) =
      (ρ * Real.cos β) • (1 : Cl13) + (ρ * Real.sin β) • I13 := by
  unfold diracSpinor
  rw [map_smul, CliffordAlgebra.reverse.map_mul, reverse_diracPhase]
  rw [Algebra.smul_mul_assoc, Algebra.mul_smul_comm, smul_smul]
  have hcore :
      (diracPhase β * R) * (CliffordAlgebra.reverse R * diracPhase β) =
        diracPhase β * diracPhase β := by
    calc
      (diracPhase β * R) * (CliffordAlgebra.reverse R * diracPhase β)
          = diracPhase β * (R * CliffordAlgebra.reverse R) * diracPhase β := by noncomm_ring
      _ = diracPhase β * diracPhase β := by rw [hR, mul_one]
  rw [hcore, diracPhase_mul_self, smul_add, smul_smul, smul_smul, Real.mul_self_sqrt hρ]

theorem diracSpinorEven_mul_reverse (ρ β : ℝ) (R : CliffordAlgebra.even Q13)
    (hρ : 0 ≤ ρ) (hR : (R : Cl13) * CliffordAlgebra.reverse (R : Cl13) = 1) :
    (diracSpinorEven ρ β R : Cl13) * CliffordAlgebra.reverse (diracSpinorEven ρ β R : Cl13) =
      (ρ * Real.cos β) • (1 : Cl13) + (ρ * Real.sin β) • I13 := by
  change diracSpinor ρ β (R : Cl13) * CliffordAlgebra.reverse (diracSpinor ρ β (R : Cl13)) = _
  exact diracSpinor_mul_reverse hρ hR

/-! ### Section 7: Downstream M2B Helpers (`GeometricCalculusAndMaxwell.lean`) -/

/-- Minkowski metric signature signs `η13 0 = 1`, `η13 1 = η13 2 = η13 3 = -1`. -/
def η13 (μ : Fin 4) : ℝ := if μ = 0 then 1 else -1

/-- Reciprocal spacetime frame vectors `γ^μ = η^{μμ} γ_μ` (Gull–Lasenby–Doran §5 Eq. 5.7). -/
def γRecip (μ : Fin 4) : Cl13 := η13 μ • γ μ

theorem γ_mul_γRecip_self (μ : Fin 4) : γ μ * γRecip μ = 1 := by
  unfold γRecip η13
  rw [Algebra.mul_smul_comm]
  fin_cases μ
  · simp [gamma_zero_sq]
  · simp [gamma_one_sq]
  · simp [gamma_two_sq]
  · simp [gamma_three_sq]

theorem γRecip_mul_γ_add_swap (μ ν : Fin 4) :
    γRecip μ * γ ν + γ ν * γRecip μ = (2 * if μ = ν then (1 : ℝ) else 0) • (1 : Cl13) := by
  by_cases h : μ = ν
  · subst h
    simp only [↓reduceIte, mul_one]
    have hself : γRecip μ * γ μ = 1 := by
      unfold γRecip η13
      rw [Algebra.smul_mul_assoc]
      fin_cases μ
      · simp [gamma_zero_sq]
      · simp [gamma_one_sq]
      · simp [gamma_two_sq]
      · simp [gamma_three_sq]
    rw [hself, γ_mul_γRecip_self, two_smul]
  · simp only [h, ↓reduceIte, mul_zero, zero_smul]
    unfold γRecip
    rw [Algebra.smul_mul_assoc, Algebra.mul_smul_comm, ← smul_add, gamma_mul_add_swap h, smul_zero]

end

end InfoGeometry.Hestenes.SpacetimeSplit
