/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import Mathlib.Data.Matrix.Basic
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Tactic

/-!
# Loxodromic Horizon Three-Projector Decomposition and Twin Thermal Waves (`SO⁺(1,3)`)

Formalizes the three-projector decomposition `P₁ ⊕ P₀ ⊕ P₂ = I₄` of 4D Minkowski spacetime
around the bifurcate Killing horizon `(t, x, y, z) ∈ ℝ^{1,3}`:
- `P₁`, `P₂`: rank-1 nullcone sheet projectors (`t = ±z`) carrying the Rindler boost `K₃ = P₁ - P₂`
- `P₀`: rank-2 transverse horizon projector (`(x, y)`) carrying the spin generator `J₃`
- Exact annihilation `K₃ J₃ = J₃ K₃ = 0` and completeness `K₃² - J₃² = I₄`
- Kerr–Rindler loxodromic generator `Λ(κ, ω) = κ K₃ + ω J₃ ∈ so(1,3)` with first Casimir
  `κ² - ω²` and second (chiral) determinant Casimir `-κ² ω²`
- Closed-form finite loxodromic 4-screw flow `L(s; κ, ω) ∈ SO⁺(1,3)` solving `dL/ds = Λ L`.
-/

set_option autoImplicit false

noncomputable section

open Matrix Real

namespace InfoGeometry.Canonical.LoxodromicHorizonThreeProjectorFlow

/-- Minkowski metric `η = diag(1, -1, -1, -1)` in coordinates `(t, x, y, z)`. -/
def eta4 : Matrix (Fin 4) (Fin 4) ℝ :=
  !![1, 0, 0, 0; 0, -1, 0, 0; 0, 0, -1, 0; 0, 0, 0, -1]

/-- Outgoing null sheet projector `P₁` onto `t = +z`. -/
def P1 : Matrix (Fin 4) (Fin 4) ℝ :=
  !![1 / 2, 0, 0, 1 / 2; 0, 0, 0, 0; 0, 0, 0, 0; 1 / 2, 0, 0, 1 / 2]

/-- Ingoing null sheet projector `P₂` onto `t = -z`. -/
def P2 : Matrix (Fin 4) (Fin 4) ℝ :=
  !![1 / 2, 0, 0, -1 / 2; 0, 0, 0, 0; 0, 0, 0, 0; -1 / 2, 0, 0, 1 / 2]

/-- Transverse 2D bifurcate Killing horizon projector `P₀` onto `(x, y)`. -/
def P0 : Matrix (Fin 4) (Fin 4) ℝ :=
  !![0, 0, 0, 0; 0, 1, 0, 0; 0, 0, 1, 0; 0, 0, 0, 0]

/-- Longitudinal Rindler boost generator `K₃` in the `(t, z)` plane. -/
def K3 : Matrix (Fin 4) (Fin 4) ℝ :=
  !![0, 0, 0, 1; 0, 0, 0, 0; 0, 0, 0, 0; 1, 0, 0, 0]

/-- Transverse horizon spin generator `J₃` in the `(x, y)` plane. -/
def J3 : Matrix (Fin 4) (Fin 4) ℝ :=
  !![0, 0, 0, 0; 0, 0, -1, 0; 0, 1, 0, 0; 0, 0, 0, 0]

/-- Rotated boost–spin non-commutativity generator `K₁` in the `(t, x)` plane. -/
def K1 : Matrix (Fin 4) (Fin 4) ℝ :=
  !![0, 1, 0, 0; 1, 0, 0, 0; 0, 0, 0, 0; 0, 0, 0, 0]

/-- Explicit non-commutativity witness in `so(1,3)`: `K₁ J₃ ≠ J₃ K₁`. -/
theorem K1_mul_J3_ne : K1 * J3 ≠ J3 * K1 := by
  intro h
  have h02 := congrArg (fun M : Matrix (Fin 4) (Fin 4) ℝ => M 0 2) h
  simp [K1, J3, Matrix.mul_apply, Fin.sum_univ_four] at h02

/-- Existential T16 non-commutativity witness for `M₄(ℝ)`. -/
theorem exists_noncomm_mat4_real :
    ∃ A B : Matrix (Fin 4) (Fin 4) ℝ, A * B ≠ B * A :=
  ⟨K1, J3, K1_mul_J3_ne⟩

/-- Partition of unity: `P₁ + P₀ + P₂ = I₄`. -/
theorem projectors_sum_one : P1 + P0 + P2 = (1 : Matrix (Fin 4) (Fin 4) ℝ) := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [P1, P0, P2] <;> norm_num

/-- All three projectors are idempotent. -/
theorem projectors_idempotent : P1 * P1 = P1 ∧ P2 * P2 = P2 ∧ P0 * P0 = P0 := by
  refine ⟨?_, ?_, ?_⟩ <;>
    { ext i j; fin_cases i <;> fin_cases j <;>
        simp [P1, P2, P0, Matrix.mul_apply, Fin.sum_univ_four] <;> norm_num }

/-- Mutual orthogonality of the three horizon projectors. -/
theorem projectors_orthogonal :
    P1 * P2 = 0 ∧ P2 * P1 = 0 ∧ P1 * P0 = 0 ∧ P0 * P1 = 0 ∧ P2 * P0 = 0 ∧ P0 * P2 = 0 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    { ext i j; fin_cases i <;> fin_cases j <;>
        simp [P1, P2, P0, Matrix.mul_apply, Fin.sum_univ_four] <;> norm_num }

/-- Traces give the subspace dimensions `1, 1, 2`. -/
theorem projectors_traces :
    Matrix.trace P1 = 1 ∧ Matrix.trace P2 = 1 ∧ Matrix.trace P0 = 2 := by
  refine ⟨?_, ?_, ?_⟩ <;>
    { simp [Matrix.trace, Matrix.diag, P1, P2, P0, Fin.sum_univ_four]; try norm_num }

/-- Boost decomposition `K₃ = P₁ - P₂` and spectral identities. -/
theorem boost_algebra :
    K3 = P1 - P2 ∧ K3 * K3 = P1 + P2 ∧ K3 * K3 * K3 = K3 := by
  refine ⟨?_, ?_, ?_⟩
  · ext i j; fin_cases i <;> fin_cases j <;> simp [K3, P1, P2] <;> norm_num
  · ext i j; fin_cases i <;> fin_cases j <;>
      simp [K3, P1, P2, Matrix.mul_apply, Fin.sum_univ_four] <;> norm_num
  · ext i j; fin_cases i <;> fin_cases j <;>
      simp [K3, Matrix.mul_apply, Fin.sum_univ_four]

/-- Horizon spin identities `J₃² = -P₀` and `J₃³ = -J₃`. -/
theorem spin_algebra : J3 * J3 = -P0 ∧ J3 * J3 * J3 = -J3 := by
  refine ⟨?_, ?_⟩ <;>
    { ext i j; fin_cases i <;> fin_cases j <;>
        simp [J3, P0, Matrix.mul_apply, Fin.sum_univ_four] }

/-- Exact boost–spin annihilation and identity resolution `K₃² - J₃² = I₄`. -/
theorem boost_spin_annihilation_and_unity :
    K3 * J3 = 0 ∧ J3 * K3 = 0 ∧ K3 * K3 - J3 * J3 = (1 : Matrix (Fin 4) (Fin 4) ℝ) := by
  refine ⟨?_, ?_, ?_⟩ <;>
    { ext i j; fin_cases i <;> fin_cases j <;>
        simp [K3, J3, Matrix.mul_apply, Fin.sum_univ_four] }

/-- Kerr–Rindler loxodromic generator `Λ(κ, ω) = κ K₃ + ω J₃`. -/
def loxodromicGen (κ ω : ℝ) : Matrix (Fin 4) (Fin 4) ℝ :=
  κ • K3 + ω • J3

/-- `Λ(κ, ω)` lies in the Lorentz Lie algebra `so(1,3)`: `Λᵀ η + η Λ = 0`. -/
theorem loxodromicGen_in_so13 (κ ω : ℝ) :
    (loxodromicGen κ ω)ᵀ * eta4 + eta4 * loxodromicGen κ ω = 0 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [loxodromicGen, K3, J3, eta4, Matrix.mul_apply, Fin.sum_univ_four]

/-- Symmetric/skew split separating thermal boost `κ K₃` from horizon spin `ω J₃`. -/
theorem loxodromicGen_sym_skew_split (κ ω : ℝ) :
    ((1 / 2 : ℝ) • (loxodromicGen κ ω + (loxodromicGen κ ω)ᵀ) = κ • K3) ∧
    ((1 / 2 : ℝ) • (loxodromicGen κ ω - (loxodromicGen κ ω)ᵀ) = ω • J3) := by
  refine ⟨?_, ?_⟩ <;>
    { ext i j; fin_cases i <;> fin_cases j <;>
        simp [loxodromicGen, K3, J3] <;> ring }

/-- First Lorentz Casimir: `Tr(Λ²) / 2 = κ² - ω²`. -/
theorem loxodromicGen_first_casimir (κ ω : ℝ) :
    Matrix.trace (loxodromicGen κ ω * loxodromicGen κ ω) / 2 = κ ^ 2 - ω ^ 2 := by
  simp [Matrix.trace, Matrix.diag, loxodromicGen, K3, J3, Matrix.mul_apply, Fin.sum_univ_four]
  ring

private lemma det_fin4 (M : Matrix (Fin 4) (Fin 4) ℝ) :
    Matrix.det M =
      M 0 0 * Matrix.det !![M 1 1, M 1 2, M 1 3; M 2 1, M 2 2, M 2 3; M 3 1, M 3 2, M 3 3] -
      M 0 1 * Matrix.det !![M 1 0, M 1 2, M 1 3; M 2 0, M 2 2, M 2 3; M 3 0, M 3 2, M 3 3] +
      M 0 2 * Matrix.det !![M 1 0, M 1 1, M 1 3; M 2 0, M 2 1, M 2 3; M 3 0, M 3 1, M 3 3] -
      M 0 3 * Matrix.det !![M 1 0, M 1 1, M 1 2; M 2 0, M 2 1, M 2 2; M 3 0, M 3 1, M 3 2] := by
  have s0 : M.submatrix Fin.succ (Fin.succAbove 0) =
      !![M 1 1, M 1 2, M 1 3; M 2 1, M 2 2, M 2 3; M 3 1, M 3 2, M 3 3] := by
    ext i j; fin_cases i <;> fin_cases j <;> rfl
  have s1 : M.submatrix Fin.succ (Fin.succAbove 1) =
      !![M 1 0, M 1 2, M 1 3; M 2 0, M 2 2, M 2 3; M 3 0, M 3 2, M 3 3] := by
    ext i j; fin_cases i <;> fin_cases j <;> rfl
  have s2 : M.submatrix Fin.succ (Fin.succAbove 2) =
      !![M 1 0, M 1 1, M 1 3; M 2 0, M 2 1, M 2 3; M 3 0, M 3 1, M 3 3] := by
    ext i j; fin_cases i <;> fin_cases j <;> rfl
  have s3 : M.submatrix Fin.succ (Fin.succAbove 3) =
      !![M 1 0, M 1 1, M 1 2; M 2 0, M 2 1, M 2 2; M 3 0, M 3 1, M 3 2] := by
    ext i j; fin_cases i <;> fin_cases j <;> rfl
  have hp0 : (-1 : ℝ) ^ ((0 : Fin 4) : ℕ) = 1 := by norm_num
  have hp1 : (-1 : ℝ) ^ ((1 : Fin 4) : ℕ) = -1 := by norm_num
  have hp2 : (-1 : ℝ) ^ ((2 : Fin 4) : ℕ) = 1 := by norm_num
  have hp3 : (-1 : ℝ) ^ ((3 : Fin 4) : ℕ) = -1 := by norm_num
  rw [Matrix.det_succ_row_zero, Fin.sum_univ_four, s0, s1, s2, s3, hp0, hp1, hp2, hp3]
  ring

/-- Explicit chiral determinant invariant `det Λ(κ, ω) = -κ² ω²`. -/
theorem loxodromicGen_second_casimir_det (κ ω : ℝ) :
    Matrix.det (loxodromicGen κ ω) = -(κ ^ 2 * ω ^ 2) := by
  rw [det_fin4]
  simp [Matrix.det_fin_three, loxodromicGen, K3, J3]
  ring

/-- True loxodromic characterization: `det Λ(κ, ω) ≠ 0 ↔ κ ≠ 0 ∧ ω ≠ 0`. -/
theorem loxodromicGen_det_ne_zero_iff (κ ω : ℝ) :
    Matrix.det (loxodromicGen κ ω) ≠ 0 ↔ κ ≠ 0 ∧ ω ≠ 0 := by
  rw [loxodromicGen_second_casimir_det]
  constructor
  · intro h
    constructor
    · intro hk
      apply h
      rw [hk]
      ring
    · intro hw
      apply h
      rw [hw]
      ring
  · rintro ⟨hk, hw⟩ h0
    have hprod : κ ^ 2 * ω ^ 2 = 0 := neg_eq_zero.mp h0
    rcases mul_eq_zero.mp hprod with hk2 | hw2
    · exact hk (sq_eq_zero_iff.mp hk2)
    · exact hw (sq_eq_zero_iff.mp hw2)

/-- Closed-form finite loxodromic 4-screw flow `L(s; κ, ω) ∈ SO⁺(1,3)` splitting into
outgoing/ingoing twin thermal waves `e^{±κ s} P₁,₂` and horizon spin `(cos ωs) P₀ + (sin ωs) J₃`. -/
def loxodromicFlow (s κ ω : ℝ) : Matrix (Fin 4) (Fin 4) ℝ :=
  Real.exp (κ * s) • P1 + Real.exp (-κ * s) • P2 + Real.cos (ω * s) • P0 + Real.sin (ω * s) • J3

/-- Initial condition `L(0; κ, ω) = I₄`. -/
theorem loxodromicFlow_zero (κ ω : ℝ) : loxodromicFlow 0 κ ω = 1 := by
  unfold loxodromicFlow
  simp only [mul_zero, Real.exp_zero, Real.cos_zero, Real.sin_zero, one_smul, zero_smul, add_zero]
  rw [add_assoc, add_comm P2 P0, ← add_assoc]
  exact projectors_sum_one

private lemma P1_mul_J3 : P1 * J3 = 0 := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [P1, J3, Matrix.mul_apply, Fin.sum_univ_four]

private lemma J3_mul_P1 : J3 * P1 = 0 := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [P1, J3, Matrix.mul_apply, Fin.sum_univ_four]

private lemma P2_mul_J3 : P2 * J3 = 0 := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [P2, J3, Matrix.mul_apply, Fin.sum_univ_four]

private lemma J3_mul_P2 : J3 * P2 = 0 := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [P2, J3, Matrix.mul_apply, Fin.sum_univ_four]

private lemma P0_mul_J3 : P0 * J3 = J3 := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [P0, J3, Matrix.mul_apply, Fin.sum_univ_four]

private lemma J3_mul_P0 : J3 * P0 = J3 := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [P0, J3, Matrix.mul_apply, Fin.sum_univ_four]

/-- One-parameter group law `L(s₁ + s₂; κ, ω) = L(s₁; κ, ω) * L(s₂; κ, ω)`. -/
theorem loxodromicFlow_add (s₁ s₂ κ ω : ℝ) :
    loxodromicFlow (s₁ + s₂) κ ω = loxodromicFlow s₁ κ ω * loxodromicFlow s₂ κ ω := by
  have he1 : Real.exp (κ * (s₁ + s₂)) = Real.exp (κ * s₁) * Real.exp (κ * s₂) := by
    rw [mul_add, Real.exp_add]
  have he2 : Real.exp (-κ * (s₁ + s₂)) = Real.exp (-κ * s₁) * Real.exp (-κ * s₂) := by
    rw [mul_add, Real.exp_add]
  have hc : Real.cos (ω * (s₁ + s₂)) =
      Real.cos (ω * s₁) * Real.cos (ω * s₂) - Real.sin (ω * s₁) * Real.sin (ω * s₂) := by
    rw [mul_add, Real.cos_add]
  have hs : Real.sin (ω * (s₁ + s₂)) =
      Real.sin (ω * s₁) * Real.cos (ω * s₂) + Real.cos (ω * s₁) * Real.sin (ω * s₂) := by
    rw [mul_add, Real.sin_add]
  unfold loxodromicFlow
  rw [he1, he2, hc, hs]
  have hId := projectors_idempotent
  have hOrth := projectors_orthogonal
  have hJ := spin_algebra
  simp only [add_mul, mul_add, smul_mul_assoc, mul_smul_comm, smul_smul,
    hId.1, hId.2.1, hId.2.2, hOrth.1, hOrth.2.1, hOrth.2.2.1, hOrth.2.2.2.1,
    hOrth.2.2.2.2.1, hOrth.2.2.2.2.2, P1_mul_J3, J3_mul_P1, P2_mul_J3, J3_mul_P2,
    P0_mul_J3, J3_mul_P0, hJ.1, smul_zero, zero_add, add_zero, smul_neg]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [P1, P2, P0, J3] <;> ring

/-- Every finite loxodromic flow preserves the Minkowski metric `η`: `Lᵀ η L = η`. -/
theorem loxodromicFlow_preserves_eta (s κ ω : ℝ) :
    (loxodromicFlow s κ ω)ᵀ * eta4 * loxodromicFlow s κ ω = eta4 := by
  have hcos_sin : Real.cos (ω * s) ^ 2 + Real.sin (ω * s) ^ 2 = 1 := Real.cos_sq_add_sin_sq _
  have hexp : Real.exp (κ * s) * Real.exp (-(κ * s)) = 1 := by
    rw [← Real.exp_add]
    have h0 : κ * s + -(κ * s) = 0 := by ring
    rw [h0, Real.exp_zero]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [loxodromicFlow, P1, P2, P0, J3, eta4, Matrix.mul_apply, Fin.sum_univ_four] <;>
    ring_nf <;>
    first
      | rfl
      | exact hexp
      | (rw [hexp])
      | (have hc : -(Real.cos (ω * s) ^ 2) - Real.sin (ω * s) ^ 2 =
            -(Real.cos (ω * s) ^ 2 + Real.sin (ω * s) ^ 2) := by ring
         rw [hc, hcos_sin])
      | (have hc : -(Real.sin (ω * s) ^ 2) - Real.cos (ω * s) ^ 2 =
            -(Real.cos (ω * s) ^ 2 + Real.sin (ω * s) ^ 2) := by ring
         rw [hc, hcos_sin])

/-- Every finite loxodromic 4-screw has unit determinant (`L(s; κ, ω) ∈ SO⁺(1,3)`). -/
theorem loxodromicFlow_det (s κ ω : ℝ) : Matrix.det (loxodromicFlow s κ ω) = 1 := by
  have hcos_sin : Real.cos (ω * s) ^ 2 + Real.sin (ω * s) ^ 2 = 1 := Real.cos_sq_add_sin_sq _
  have hexp : Real.exp (κ * s) * Real.exp (-(κ * s)) = 1 := by
    rw [← Real.exp_add]
    have h0 : κ * s + -(κ * s) = 0 := by ring
    rw [h0, Real.exp_zero]
  rw [det_fin4]
  simp only [Matrix.det_fin_three, loxodromicFlow, P1, P2, P0, J3,
    Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]
  norm_num
  linear_combination (Real.cos (ω * s) ^ 2 + Real.sin (ω * s) ^ 2) * hexp + hcos_sin

/-- Closed-form flow solves the first-order ODE `d/ds L(s; κ, ω) = Λ(κ, ω) L(s; κ, ω)` entrywise. -/
theorem loxodromicFlow_hasDerivAt (κ ω s : ℝ) (i j : Fin 4) :
    HasDerivAt (fun t => loxodromicFlow t κ ω i j) ((loxodromicGen κ ω * loxodromicFlow s κ ω) i j) s := by
  have hDerivMat :
      (κ * Real.exp (κ * s)) * P1 i j + ((-κ) * Real.exp (-κ * s)) * P2 i j +
          (-ω * Real.sin (ω * s)) * P0 i j + (ω * Real.cos (ω * s)) * J3 i j =
        (loxodromicGen κ ω * loxodromicFlow s κ ω) i j := by
    fin_cases i <;> fin_cases j <;>
      simp [loxodromicGen, loxodromicFlow, K3, J3, P1, P2, P0, Matrix.mul_apply,
        Fin.sum_univ_four] <;> ring
  rw [← hDerivMat]
  have hfun : (fun t => loxodromicFlow t κ ω i j) =
      fun t => Real.exp (κ * t) * P1 i j + Real.exp (-κ * t) * P2 i j +
        Real.cos (ω * t) * P0 i j + Real.sin (ω * t) * J3 i j := by
    ext t
    simp [loxodromicFlow]
  rw [hfun]
  have h1 : HasDerivAt (fun t => Real.exp (κ * t) * P1 i j)
      ((κ * Real.exp (κ * s)) * P1 i j) s := by
    have he : HasDerivAt (fun t => Real.exp (κ * t)) (Real.exp (κ * s) * (κ * 1)) s :=
      ((hasDerivAt_id s).const_mul κ).exp
    convert he.mul_const (P1 i j) using 1
    ring
  have h2 : HasDerivAt (fun t => Real.exp (-κ * t) * P2 i j)
      (((-κ) * Real.exp (-κ * s)) * P2 i j) s := by
    have he : HasDerivAt (fun t => Real.exp (-κ * t)) (Real.exp (-κ * s) * (-κ * 1)) s :=
      ((hasDerivAt_id s).const_mul (-κ)).exp
    convert he.mul_const (P2 i j) using 1
    ring
  have h3 : HasDerivAt (fun t => Real.cos (ω * t) * P0 i j)
      ((-ω * Real.sin (ω * s)) * P0 i j) s := by
    have hc : HasDerivAt (fun t => Real.cos (ω * t)) (-Real.sin (ω * s) * (ω * 1)) s :=
      ((hasDerivAt_id s).const_mul ω).cos
    convert hc.mul_const (P0 i j) using 1
    ring
  have h4 : HasDerivAt (fun t => Real.sin (ω * t) * J3 i j)
      ((ω * Real.cos (ω * s)) * J3 i j) s := by
    have hs : HasDerivAt (fun t => Real.sin (ω * t)) (Real.cos (ω * s) * (ω * 1)) s :=
      ((hasDerivAt_id s).const_mul ω).sin
    convert hs.mul_const (J3 i j) using 1
    ring
  exact ((h1.add h2).add h3).add h4

end InfoGeometry.Canonical.LoxodromicHorizonThreeProjectorFlow
