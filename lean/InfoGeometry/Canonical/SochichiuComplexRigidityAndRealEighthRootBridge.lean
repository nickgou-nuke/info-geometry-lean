/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Algebra.SochichiuNambu3AlgebraObstruction
import InfoGeometry.Algebra.SochichiuPeirceNambuBridge
import InfoGeometry.Algebra.RealPauliNambuSign
import InfoGeometry.Canonical.DoubledMinkowskiRotatingSpinInstability
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Tactic

/-!
# Sochichiu `M₂(ℂ)` Nonconstant-`T₄` Rigidity, Parametric Spin-1/2 Families, & Real `Cl(1,1)` Eighth Root

Canonical bridge extending `InfoGeometry.Algebra.SochichiuNambu3AlgebraObstruction` and
`InfoGeometry.Algebra.SochichiuPeirceNambuBridge` for Corneliu Sochichiu,
*"On Nambu-Lie 3-algebra representations"* (arXiv:0806.3520v2, 2008), without duplicating
`nambu3`, `pauli1..3`, Lemma 1 (`sochichiu_lemma1_scalar_zero`), Eq. (2.21)
(`nambu3_eq_deformed_bracket`), or the all-dimension finite Hermitian no-go
(`euclidean_A4_hermitian_matrix_rep_trivial`):

1. **Part 1 — Exact PDF Factor-of-`i` Audit & Complex Nonconstant `T₄` Rigidity (`Sec. 2.4`,
   Eqs. 2.21–2.29)**:
   On `M₂(ℂ)` with `T_k = c • pauli_k` (`c ≠ 0`) and arbitrary
   `T₄ = μ₀ • 1 + μ₁ • pauli1 + μ₂ • pauli2 + μ₃ • pauli3`, direct Pauli evaluation gives
   `[T₄, pauli₁, pauli₂]_N = (2 i μ₀) • pauli₃ + (6 i μ₃) • 1` (noting that PDF Eqs. 2.24–2.25
   omit the factor `i` in `2 i μ₀` and `6 i μ₃`). Solving the `A₄` system forces
   `μ₁ = μ₂ = μ₃ = 0`, `c = -(2 μ₀)⁻¹`, and `μ₀^4 = -3/4` (`sochichiu_nonconstant_T4_M2C_rigidity`).
2. **Part 2 — Parametric Spin-1/2 Euclidean `A₄` & Strictly Hermitian Lorentzian `M₂(ℂ)` Families**:
   - `sochichiu_spin_half_parametric_euclidean`: every complex quartic root `t₄^4 = -3/4` yields a
     genuine solution of all four Euclidean `A₄` equations in both `nambu3` and
     `PeirceSpine.alternatingProduct3` (bridged via `SochichiuPeirceNambuBridge`).
   - `sochichiu_spin_half_parametric_lorentzian_hermitian`: flipping `[T₁, T₂, T₃]_N` to `-i T₄`
     changes the quartic constraint to `t₄^4 = +3/4` (`t₄ ∈ ℝ`), yielding strictly Hermitian
     `M₂(ℂ)` solutions (`T_kᴴ = T_k`, `T₄ᴴ = T₄`) and complementing both
     `lorentzian_A31_hermitian_nontrivial_witness` and `RealPauliNambuSign.symmetric_sign_flipped_nambu_solution`.
3. **Part 3 — Real `Cl(1,1) ≅ M₂(ℝ)` Eighth-Root Realization (`R₈⁴ = -I₂`, Zero Complex `i`)**:
   Reuses `DoubledMinkowskiRotatingSpinInstability.eps2` (`ε² = -I₂`) to construct
   `realEighthRoot2 = (1 / √2) • (1 + eps2) ∈ M₂(ℝ)`, proving `R₈² = ε`, `R₈⁴ = -I₂`, and an
   explicit pure-real `M₂(ℝ)` solution `T^4 = -(3/4) • I₂` to the Euclidean quartic obstruction.

## Three-Bucket Audit Map

#### BUCKET 1: CLOSED FINITE MATRIX THEOREMS
* `nambu3_pauliLinear_12`, `nambu3_pauliLinear_23`, `nambu3_pauliLinear_31`
* `sochichiu_nonconstant_T4_M2C_rigidity`
* `sochichiu_spin_half_parametric_euclidean`
* `sochichiu_spin_half_parametric_lorentzian_hermitian`
* `realEighthRoot2_sq`, `realEighthRoot2_pow_four`, `realQuarticNegThreeFourths_pow_four`

#### BUCKET 2: CONDITIONAL THEOREMS FROM EXPLICIT HYPOTHESES
* `sochichiu_nonconstant_T4_M2C_rigidity` holds for all nonzero spatial scales `c ≠ 0` under
  the `M₂(ℂ)` Pauli ansatz.

#### BUCKET 3: OPEN CLOSURE DEBT
* No classification of higher-rank `n ≥ 3` nonconstant-`T₄` ansätze or infinite-dimensional
  unbounded `A₄` operators is claimed here.
-/

set_option autoImplicit false

noncomputable section

namespace InfoGeometry.Canonical.SochichiuComplexRigidityAndRealEighthRootBridge

open Matrix Complex
open InfoGeometry.Algebra.SochichiuNambu3AlgebraObstruction
open InfoGeometry.Algebra.SochichiuPeirceNambuBridge
open InfoGeometry.Canonical.DoubledMinkowskiRotatingSpinInstability
open InfoGeometry.OperatorAlgebra.PeirceSpine

/-! ### Part 1: PDF Factor-of-`i` Audit & Complex Nonconstant `T₄` Rigidity on `M₂(ℂ)` -/

section PauliLinearAndRigidity

private lemma nambu3_add_left {R : Type*} [Ring R] (A₁ A₂ B C : R) :
    nambu3 (A₁ + A₂) B C = nambu3 A₁ B C + nambu3 A₂ B C := by
  unfold nambu3; noncomm_ring

private lemma nambu3_smul_left (c : ℂ) (A B C : Matrix (Fin 2) (Fin 2) ℂ) :
    nambu3 (c • A) B C = c • nambu3 A B C := by
  unfold nambu3
  simp only [smul_mul_assoc, mul_smul_comm, ← smul_add, ← smul_sub]

theorem nambu3_pauliLinear_12 (μ₀ μ₁ μ₂ μ₃ : ℂ) :
    nambu3 (μ₀ • (1 : Matrix (Fin 2) (Fin 2) ℂ) + μ₁ • pauli1 + μ₂ • pauli2 + μ₃ • pauli3)
        pauli1 pauli2 =
      (2 * Complex.I * μ₀) • pauli3 +
        (6 * Complex.I * μ₃) • (1 : Matrix (Fin 2) (Fin 2) ℂ) := by
  have h1 : nambu3 (1 : Matrix (Fin 2) (Fin 2) ℂ) pauli1 pauli2 = (2 * Complex.I) • pauli3 := by
    ext i j; fin_cases i <;> fin_cases j <;> simp [nambu3, pauli1, pauli2, pauli3] <;> ring
  have h2 : nambu3 pauli1 pauli1 pauli2 = 0 := by
    ext i j; fin_cases i <;> fin_cases j <;> simp [nambu3, pauli1, pauli2]
  have h3 : nambu3 pauli2 pauli1 pauli2 = 0 := by
    ext i j; fin_cases i <;> fin_cases j <;> simp [nambu3, pauli1, pauli2]
  have h4 : nambu3 pauli3 pauli1 pauli2 = (6 * Complex.I) • (1 : Matrix (Fin 2) (Fin 2) ℂ) := by
    ext i j; fin_cases i <;> fin_cases j <;> simp [nambu3, pauli1, pauli2, pauli3] <;> ring
  simp only [nambu3_add_left, nambu3_smul_left, h1, h2, h3, h4, smul_zero, add_zero, smul_smul]
  congr 1 <;> ring

theorem nambu3_pauliLinear_23 (μ₀ μ₁ μ₂ μ₃ : ℂ) :
    nambu3 (μ₀ • (1 : Matrix (Fin 2) (Fin 2) ℂ) + μ₁ • pauli1 + μ₂ • pauli2 + μ₃ • pauli3)
        pauli2 pauli3 =
      (2 * Complex.I * μ₀) • pauli1 +
        (6 * Complex.I * μ₁) • (1 : Matrix (Fin 2) (Fin 2) ℂ) := by
  have h1 : nambu3 (1 : Matrix (Fin 2) (Fin 2) ℂ) pauli2 pauli3 = (2 * Complex.I) • pauli1 := by
    ext i j; fin_cases i <;> fin_cases j <;> simp [nambu3, pauli1, pauli2, pauli3] <;> ring
  have h2 : nambu3 pauli1 pauli2 pauli3 = (6 * Complex.I) • (1 : Matrix (Fin 2) (Fin 2) ℂ) := by
    ext i j; fin_cases i <;> fin_cases j <;> simp [nambu3, pauli1, pauli2, pauli3] <;> ring
  have h3 : nambu3 pauli2 pauli2 pauli3 = 0 := by
    ext i j; fin_cases i <;> fin_cases j <;> simp [nambu3, pauli2, pauli3]
  have h4 : nambu3 pauli3 pauli2 pauli3 = 0 := by
    ext i j; fin_cases i <;> fin_cases j <;> simp [nambu3, pauli2, pauli3]
  simp only [nambu3_add_left, nambu3_smul_left, h1, h2, h3, h4, smul_zero, add_zero, smul_smul]
  congr 1 <;> ring

theorem nambu3_pauliLinear_31 (μ₀ μ₁ μ₂ μ₃ : ℂ) :
    nambu3 (μ₀ • (1 : Matrix (Fin 2) (Fin 2) ℂ) + μ₁ • pauli1 + μ₂ • pauli2 + μ₃ • pauli3)
        pauli3 pauli1 =
      (2 * Complex.I * μ₀) • pauli2 +
        (6 * Complex.I * μ₂) • (1 : Matrix (Fin 2) (Fin 2) ℂ) := by
  have h1 : nambu3 (1 : Matrix (Fin 2) (Fin 2) ℂ) pauli3 pauli1 = (2 * Complex.I) • pauli2 := by
    ext i j; fin_cases i <;> fin_cases j <;>
      simp [nambu3, pauli1, pauli2, pauli3] <;>
      ring_nf <;>
      try simp [Complex.I_sq]
  have h2 : nambu3 pauli1 pauli3 pauli1 = 0 := by
    ext i j; fin_cases i <;> fin_cases j <;> simp [nambu3, pauli1, pauli3]
  have h3 : nambu3 pauli2 pauli3 pauli1 = (6 * Complex.I) • (1 : Matrix (Fin 2) (Fin 2) ℂ) := by
    ext i j; fin_cases i <;> fin_cases j <;> simp [nambu3, pauli1, pauli2, pauli3] <;> ring
  have h4 : nambu3 pauli3 pauli3 pauli1 = 0 := by
    ext i j; fin_cases i <;> fin_cases j <;> simp [nambu3, pauli1, pauli3]
  simp only [nambu3_add_left, nambu3_smul_left, h1, h2, h3, h4, smul_zero, add_zero, smul_smul]
  congr 1 <;> ring

private lemma nambu3_mat2c_scale_two (c : ℂ) (A B C : Matrix (Fin 2) (Fin 2) ℂ) :
    nambu3 A (c • B) (c • C) = (c ^ 2) • nambu3 A B C := by
  unfold nambu3
  simp only [smul_mul_assoc, mul_smul_comm, smul_smul, ← smul_add, ← smul_sub, ← sq]

private lemma complex_mul_cube (c : ℂ) : c * (c * c) = c ^ 3 := by ring

private lemma nambu3_mat2c_scale_three (c : ℂ) (A B C : Matrix (Fin 2) (Fin 2) ℂ) :
    nambu3 (c • A) (c • B) (c • C) = (c ^ 3) • nambu3 A B C := by
  unfold nambu3
  simp only [smul_mul_assoc, mul_smul_comm, smul_smul, ← smul_add, ← smul_sub]
  congr 1
  exact complex_mul_cube c

/-- **Nonconstant `T₄` Rigidity Theorem (`Section 2.4`, Eqs. 2.21–2.29)**:
For `T_k = c • pauli_k` (`c ≠ 0`) and `T₄ = μ₀·1 + μ₁·σ₁ + μ₂·σ₂ + μ₃·σ₃` on `M₂(ℂ)`, the
Euclidean `A₄` brackets `[T₄, Tᵢ, Tⱼ]_N = -i ε_{ijk} T_k` and `[T₁, T₂, T₃]_N = +i T₄` force `T₄`
to be scalar (`μ₁ = μ₂ = μ₃ = 0`), with `c = -(2 μ₀)⁻¹` and `μ₀^4 = -3/4`. -/
theorem sochichiu_nonconstant_T4_M2C_rigidity (μ₀ μ₁ μ₂ μ₃ c : ℂ) (hc : c ≠ 0)
    (h12 : nambu3 (μ₀ • 1 + μ₁ • pauli1 + μ₂ • pauli2 + μ₃ • pauli3) (c • pauli1) (c • pauli2) =
      (-Complex.I) • (c • pauli3))
    (h23 : nambu3 (μ₀ • 1 + μ₁ • pauli1 + μ₂ • pauli2 + μ₃ • pauli3) (c • pauli2) (c • pauli3) =
      (-Complex.I) • (c • pauli1))
    (h31 : nambu3 (μ₀ • 1 + μ₁ • pauli1 + μ₂ • pauli2 + μ₃ • pauli3) (c • pauli3) (c • pauli1) =
      (-Complex.I) • (c • pauli2))
    (h123 : nambu3 (c • pauli1) (c • pauli2) (c • pauli3) =
      Complex.I • (μ₀ • 1 + μ₁ • pauli1 + μ₂ • pauli2 + μ₃ • pauli3)) :
    μ₁ = 0 ∧ μ₂ = 0 ∧ μ₃ = 0 ∧ c = -(2 * μ₀)⁻¹ ∧ μ₀ ^ 4 = -(3 / 4 : ℂ) := by
  have hp123 : nambu3 pauli1 pauli2 pauli3 =
      (6 * Complex.I) • (1 : Matrix (Fin 2) (Fin 2) ℂ) := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [nambu3, pauli1, pauli2, pauli3] <;>
      ring
  rw [nambu3_mat2c_scale_two, nambu3_pauliLinear_12] at h12
  rw [nambu3_mat2c_scale_two, nambu3_pauliLinear_23] at h23
  rw [nambu3_mat2c_scale_two, nambu3_pauliLinear_31] at h31
  rw [nambu3_mat2c_scale_three, hp123] at h123
  have h6c2 : c ^ 2 * (6 * Complex.I) ≠ 0 :=
    mul_ne_zero (pow_ne_zero 2 hc) (mul_ne_zero (by norm_num) Complex.I_ne_zero)
  have hμ₁ : μ₁ = 0 := by
    have h00 := congrFun (congrFun h23 0) 0
    simp [pauli1] at h00
    exact h00.resolve_left hc
  have hμ₂ : μ₂ = 0 := by
    have h00 := congrFun (congrFun h31 0) 0
    simp [pauli2] at h00
    exact h00.resolve_left hc
  have hμ₃ : μ₃ = 0 := by
    have h00 := congrFun (congrFun h12 0) 0
    have h11 := congrFun (congrFun h12 1) 1
    simp [pauli3] at h00 h11
    have hEq : c ^ 2 * (6 * Complex.I) * μ₃ = 0 := by linear_combination (h00 + h11) / 2
    exact (mul_eq_zero.mp hEq).resolve_left h6c2
  have hc_rel : 2 * c * μ₀ = -1 := by
    have h00 := congrFun (congrFun h12 0) 0
    simp [pauli3, hμ₃] at h00
    have hSub : c * Complex.I * (2 * c * μ₀ + 1) = 0 := by linear_combination h00
    have hcI : c * Complex.I ≠ 0 := mul_ne_zero hc Complex.I_ne_zero
    exact eq_neg_of_add_eq_zero_left ((mul_eq_zero.mp hSub).resolve_left hcI)
  have hμ₀ : μ₀ ≠ 0 := by
    intro h0
    rw [h0, mul_zero] at hc_rel
    norm_num at hc_rel
  have hc_eq : c = -(2 * μ₀)⁻¹ := by
    field_simp [hμ₀]
    linear_combination hc_rel
  have hμ0_4 : μ₀ ^ 4 = -(3 / 4 : ℂ) := by
    have h00 := congrFun (congrFun h123 0) 0
    simp [pauli1, pauli2, pauli3, hμ₁, hμ₂, hμ₃] at h00
    rw [hc_eq] at h00
    have hMul := congrArg (fun z => z * μ₀ ^ 3 * (-Complex.I)) h00
    field_simp [hμ₀] at hMul
    linear_combination hMul / 8
  exact ⟨hμ₁, hμ₂, hμ₃, hc_eq, hμ0_4⟩

/-- Degenerate boundary complementary to `sochichiu_nonconstant_T4_M2C_rigidity`:
at zero spatial scale `c = 0`, the last Euclidean `A₄` equation forces the
entire affine Pauli expansion of `T₄` to vanish.  Thus the `c = 0` branch
contains only the zero four-tuple. -/
theorem sochichiu_nonconstant_T4_M2C_zero_scale
    (μ₀ μ₁ μ₂ μ₃ : ℂ)
    (h123 : nambu3 (0 : Matrix (Fin 2) (Fin 2) ℂ)
      (0 • pauli1) (0 • pauli2) = Complex.I •
        (μ₀ • (1 : Matrix (Fin 2) (Fin 2) ℂ) + μ₁ • pauli1 + μ₂ • pauli2 + μ₃ • pauli3)) :
    μ₀ = 0 ∧ μ₁ = 0 ∧ μ₂ = 0 ∧ μ₃ = 0 := by
  let T₄ : Matrix (Fin 2) (Fin 2) ℂ :=
    μ₀ • (1 : Matrix (Fin 2) (Fin 2) ℂ) + μ₁ • pauli1 + μ₂ • pauli2 + μ₃ • pauli3
  have hzero : nambu3 (0 : Matrix (Fin 2) (Fin 2) ℂ) 0 0 = Complex.I • T₄ := by
    simpa [T₄, nambu3] using h123
  have hT₄ : T₄ = 0 := (euclidean_A4_zero_triple_forces_zero_fourth T₄).mp hzero
  have h00 : μ₀ + μ₃ = 0 := by
    have h := congrArg (fun M : Matrix (Fin 2) (Fin 2) ℂ => M 0 0) hT₄
    simpa [T₄, pauli1, pauli2, pauli3] using h
  have h11 : μ₀ - μ₃ = 0 := by
    have h := congrArg (fun M : Matrix (Fin 2) (Fin 2) ℂ => M 1 1) hT₄
    simpa [T₄, pauli1, pauli2, pauli3, sub_eq_add_neg] using h
  have h01 : μ₁ - Complex.I * μ₂ = 0 := by
    have h := congrArg (fun M : Matrix (Fin 2) (Fin 2) ℂ => M 0 1) hT₄
    simpa [T₄, pauli1, pauli2, pauli3, mul_comm, sub_eq_add_neg] using h
  have h10 : μ₁ + Complex.I * μ₂ = 0 := by
    have h := congrArg (fun M : Matrix (Fin 2) (Fin 2) ℂ => M 1 0) hT₄
    simpa [T₄, pauli1, pauli2, pauli3, mul_comm] using h
  have hsum : 2 * μ₀ = 0 := by
    calc
      2 * μ₀ = (μ₀ + μ₃) + (μ₀ - μ₃) := by ring
      _ = 0 := by rw [h00, h11]; ring
  have hμ₀ : μ₀ = 0 := (mul_eq_zero.mp hsum).resolve_left (by norm_num)
  have hμ₃ : μ₃ = 0 := by
    calc
      μ₃ = (μ₀ + μ₃) - μ₀ := by ring
      _ = 0 := by rw [h00, hμ₀]; ring
  have hsum₁ : 2 * μ₁ = 0 := by
    calc
      2 * μ₁ = (μ₁ - Complex.I * μ₂) + (μ₁ + Complex.I * μ₂) := by ring
      _ = 0 := by rw [h01, h10]; ring
  have hμ₁ : μ₁ = 0 := (mul_eq_zero.mp hsum₁).resolve_left (by norm_num)
  have hIμ₂ : (2 * Complex.I) * μ₂ = 0 := by
    calc
      (2 * Complex.I) * μ₂ = (μ₁ + Complex.I * μ₂) - (μ₁ - Complex.I * μ₂) := by ring
      _ = 0 := by rw [h10, h01]; ring
  have hμ₂ : μ₂ = 0 := (mul_eq_zero.mp hIμ₂).resolve_left (by norm_num)
  exact ⟨hμ₀, hμ₁, hμ₂, hμ₃⟩

end PauliLinearAndRigidity

/-! ### Part 2: Parametric Spin-1/2 Euclidean `A₄` & Strictly Hermitian Lorentzian `M₂(ℂ)` Families -/

section ParametricSpinHalfFamilies

/-- **Parametric Spin-1/2 Euclidean `A₄` Realization (`t₄^4 = -3/4`)**:
For every complex `t₄` with `t₄^4 = -3/4`, `T_k = -(1 / (2 t₄)) • pauli_k` and `T₄ = t₄ • 1` satisfy
all four Euclidean `A₄` brackets (stated simultaneously for `nambu3` and `alternatingProduct3`),
together with the `M₂(ℂ)` noncommutativity witness reused from `SochichiuPeirceNambuBridge`. -/
theorem sochichiu_spin_half_parametric_euclidean (t₄ : ℂ) (ht₄ : t₄ ^ 4 = -(3 / 4 : ℂ)) :
    (∃ A B : Matrix (Fin 2) (Fin 2) ℂ, A * B ≠ B * A) ∧
    let T₁ : Matrix (Fin 2) (Fin 2) ℂ := -(1 / (2 * t₄)) • pauli1
    let T₂ : Matrix (Fin 2) (Fin 2) ℂ := -(1 / (2 * t₄)) • pauli2
    let T₃ : Matrix (Fin 2) (Fin 2) ℂ := -(1 / (2 * t₄)) • pauli3
    let T₄ : Matrix (Fin 2) (Fin 2) ℂ := t₄ • (1 : Matrix (Fin 2) (Fin 2) ℂ)
    nambu3 T₄ T₁ T₂ = (-Complex.I) • T₃ ∧
    nambu3 T₄ T₂ T₃ = (-Complex.I) • T₁ ∧
    nambu3 T₄ T₃ T₁ = (-Complex.I) • T₂ ∧
    nambu3 T₁ T₂ T₃ = Complex.I • T₄ ∧
    alternatingProduct3 T₁ T₂ T₃ = Complex.I • T₄ := by
  have ht₄0 : t₄ ≠ 0 := by
    intro h
    rw [h] at ht₄
    norm_num at ht₄
  have hp12 : lieComm pauli1 pauli2 = (2 * Complex.I) • pauli3 := by
    ext i j; fin_cases i <;> fin_cases j <;> simp [lieComm, pauli1, pauli2, pauli3] <;> ring
  have hp23 : lieComm pauli2 pauli3 = (2 * Complex.I) • pauli1 := by
    ext i j; fin_cases i <;> fin_cases j <;> simp [lieComm, pauli1, pauli2, pauli3] <;> ring
  have hp31 : lieComm pauli3 pauli1 = (2 * Complex.I) • pauli2 := by
    ext i j; fin_cases i <;> fin_cases j <;>
      simp [lieComm, pauli1, pauli2, pauli3] <;>
      ring_nf <;>
      try simp [Complex.I_sq]
  have hp123 : nambu3 pauli1 pauli2 pauli3 =
      (6 * Complex.I) • (1 : Matrix (Fin 2) (Fin 2) ℂ) := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [nambu3, pauli1, pauli2, pauli3] <;>
      ring
  refine ⟨exists_noncomm_mat2_complex, ?_⟩
  dsimp
  have hN123 : nambu3 (-(1 / (2 * t₄)) • pauli1) (-(1 / (2 * t₄)) • pauli2)
      (-(1 / (2 * t₄)) • pauli3) = Complex.I • (t₄ • (1 : Matrix (Fin 2) (Fin 2) ℂ)) := by
    rw [nambu3_mat2c_scale_three, hp123, smul_smul, smul_smul]
    congr 1
    calc (-(1 / (2 * t₄))) ^ 3 * (6 * Complex.I)
        = -(3 * Complex.I * t₄) / (4 * t₄ ^ 4) := by field_simp [ht₄0]; ring
      _ = -(3 * Complex.I * t₄) / (4 * (-(3 / 4 : ℂ))) := by rw [ht₄]
      _ = Complex.I * t₄ := by ring
  refine ⟨?_, ?_, ?_, hN123, ?_⟩
  · rw [nambu3_mat2c_scale_two, nambu3_smul_one_left, hp12, smul_smul, smul_smul, smul_smul]
    congr 1
    field_simp [ht₄0]
  · rw [nambu3_mat2c_scale_two, nambu3_smul_one_left, hp23, smul_smul, smul_smul, smul_smul]
    congr 1
    field_simp [ht₄0]
  · rw [nambu3_mat2c_scale_two, nambu3_smul_one_left, hp31, smul_smul, smul_smul, smul_smul]
    congr 1
    field_simp [ht₄0]
  · rw [← nambu3_eq_alternatingProduct3]
    exact hN123

/-- **Parametric Strictly Hermitian Spin-1/2 Lorentzian `A_{3,1}` Family (`t₄^4 = +3/4`)**:
For every real fourth root `t₄ : ℝ` satisfying `t₄^4 = 3/4`, flipping the sign of `[T₁, T₂, T₃]_N`
to `-I • T₄` gives genuinely Hermitian nonzero `2 × 2` complex matrices satisfying all four
Lorentzian `A_{3,1}` Nambu brackets (sharply contrasting with `euclidean_A4_hermitian_matrix_rep_trivial`). -/
theorem sochichiu_spin_half_parametric_lorentzian_hermitian (t₄ : ℝ) (ht₄ : t₄ ^ 4 = (3 / 4 : ℝ)) :
    let T₁ : Matrix (Fin 2) (Fin 2) ℂ := -((1 / (2 * t₄) : ℝ) : ℂ) • pauli1
    let T₂ : Matrix (Fin 2) (Fin 2) ℂ := -((1 / (2 * t₄) : ℝ) : ℂ) • pauli2
    let T₃ : Matrix (Fin 2) (Fin 2) ℂ := -((1 / (2 * t₄) : ℝ) : ℂ) • pauli3
    let T₄ : Matrix (Fin 2) (Fin 2) ℂ := (t₄ : ℂ) • (1 : Matrix (Fin 2) (Fin 2) ℂ)
    T₁.IsHermitian ∧ T₂.IsHermitian ∧ T₃.IsHermitian ∧ T₄.IsHermitian ∧
    nambu3 T₄ T₁ T₂ = (-Complex.I) • T₃ ∧
    nambu3 T₄ T₂ T₃ = (-Complex.I) • T₁ ∧
    nambu3 T₄ T₃ T₁ = (-Complex.I) • T₂ ∧
    nambu3 T₁ T₂ T₃ = (-Complex.I) • T₄ := by
  have ht₄0 : t₄ ≠ 0 := by
    intro h
    rw [h] at ht₄
    norm_num at ht₄
  have ht₄C0 : (t₄ : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr ht₄0
  have hpHerm1 : pauli1.IsHermitian := by
    rw [Matrix.IsHermitian]; ext i j; fin_cases i <;> fin_cases j <;> simp [pauli1]
  have hpHerm2 : pauli2.IsHermitian := by
    rw [Matrix.IsHermitian]; ext i j; fin_cases i <;> fin_cases j <;> simp [pauli2]
  have hpHerm3 : pauli3.IsHermitian := by
    rw [Matrix.IsHermitian]; ext i j; fin_cases i <;> fin_cases j <;> simp [pauli3]
  have scaleHerm : ∀ {r : ℝ} {M : Matrix (Fin 2) (Fin 2) ℂ},
      M.IsHermitian → ((r : ℂ) • M).IsHermitian := by
    intro r M hM
    rw [Matrix.IsHermitian]
    ext i j
    have hij := congrArg (fun A : Matrix (Fin 2) (Fin 2) ℂ => A i j) hM.eq
    simp only [Matrix.conjTranspose_apply, Matrix.smul_apply, star_smul, RCLike.star_def,
      Complex.conj_ofReal] at hij ⊢
    rw [← hij]
  have hp12 : lieComm pauli1 pauli2 = (2 * Complex.I) • pauli3 := by
    ext i j; fin_cases i <;> fin_cases j <;> simp [lieComm, pauli1, pauli2, pauli3] <;> ring
  have hp23 : lieComm pauli2 pauli3 = (2 * Complex.I) • pauli1 := by
    ext i j; fin_cases i <;> fin_cases j <;> simp [lieComm, pauli1, pauli2, pauli3] <;> ring
  have hp31 : lieComm pauli3 pauli1 = (2 * Complex.I) • pauli2 := by
    ext i j; fin_cases i <;> fin_cases j <;>
      simp [lieComm, pauli1, pauli2, pauli3] <;>
      ring_nf <;>
      try simp [Complex.I_sq]
  have hp123 : nambu3 pauli1 pauli2 pauli3 =
      (6 * Complex.I) • (1 : Matrix (Fin 2) (Fin 2) ℂ) := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [nambu3, pauli1, pauli2, pauli3] <;>
      ring
  have hRsmul : ∀ (r : ℝ) (M : Matrix (Fin 2) (Fin 2) ℂ), r • M = (r : ℂ) • M := fun r M => by
    ext i j; simp [Complex.real_smul]
  have hnegReal : -((1 / (2 * t₄) : ℝ) : ℂ) = ((-(1 / (2 * t₄)) : ℝ) : ℂ) := by
    push_cast
    rfl
  have hcEq : -((1 / (2 * t₄) : ℝ) : ℂ) = -(1 / (2 * (t₄ : ℂ))) := by
    push_cast
    ring
  dsimp
  refine ⟨?_, ?_, ?_, scaleHerm Matrix.isHermitian_one, ?_, ?_, ?_, ?_⟩
  · rw [hnegReal]; exact scaleHerm hpHerm1
  · rw [hnegReal]; exact scaleHerm hpHerm2
  · rw [hnegReal]; exact scaleHerm hpHerm3
  · rw [hcEq, nambu3_mat2c_scale_two, nambu3_smul_one_left, hp12, hRsmul, smul_smul, smul_smul,
      smul_smul]
    congr 1
    field_simp [ht₄C0]
  · rw [hcEq, nambu3_mat2c_scale_two, nambu3_smul_one_left, hp23, hRsmul, smul_smul, smul_smul,
      smul_smul]
    congr 1
    field_simp [ht₄C0]
  · rw [hcEq, nambu3_mat2c_scale_two, nambu3_smul_one_left, hp31, hRsmul, smul_smul, smul_smul,
      smul_smul]
    congr 1
    field_simp [ht₄C0]
  · rw [hcEq, nambu3_mat2c_scale_three, hp123, hRsmul, smul_smul, smul_smul]
    congr 1
    have ht₄C4 : (t₄ : ℂ) ^ 4 = (3 / 4 : ℂ) := by
      calc (t₄ : ℂ) ^ 4 = ((t₄ ^ 4 : ℝ) : ℂ) := by push_cast; rfl
        _ = ((3 / 4 : ℝ) : ℂ) := by rw [ht₄]
        _ = (3 / 4 : ℂ) := by push_cast; rfl
    calc (-(1 / (2 * (t₄ : ℂ)))) ^ 3 * (6 * Complex.I)
        = -(3 * Complex.I * (t₄ : ℂ)) / (4 * (t₄ : ℂ) ^ 4) := by field_simp [ht₄C0]; ring
      _ = -(3 * Complex.I * (t₄ : ℂ)) / (4 * (3 / 4 : ℂ)) := by rw [ht₄C4]
      _ = (-Complex.I) * (t₄ : ℂ) := by ring

end ParametricSpinHalfFamilies

/-! ### Part 3: Real `Cl(1,1) ≅ M₂(ℝ)` Eighth-Root Operator (`R₈⁴ = -I₂`, Zero Complex `i`) -/

section RealCl11EighthRoot

/-- Purely real eighth-root rotation `R₈ = (1 / √2) • (I₂ + ε)` on `Cl(1,1) ≅ M₂(ℝ)`, reusing
`DoubledMinkowskiRotatingSpinInstability.eps2` (`eps2² = -I₂`). -/
def realEighthRoot2 : Matrix (Fin 2) (Fin 2) ℝ :=
  (1 / Real.sqrt 2) • ((1 : Matrix (Fin 2) (Fin 2) ℝ) + eps2)

theorem realEighthRoot2_sq :
    realEighthRoot2 * realEighthRoot2 = eps2 := by
  have h2 : Real.sqrt 2 * Real.sqrt 2 = 2 := Real.mul_self_sqrt (by norm_num)
  have hsqrt0 : Real.sqrt 2 ≠ 0 := Real.sqrt_ne_zero'.mpr (by norm_num)
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [realEighthRoot2, eps2, Matrix.mul_apply, Fin.sum_univ_two] <;>
    field_simp [hsqrt0] <;>
    nlinarith [h2]

theorem realEighthRoot2_pow_four :
    realEighthRoot2 ^ 4 = -(1 : Matrix (Fin 2) (Fin 2) ℝ) := by
  have heps2 : eps2 * eps2 = -(1 : Matrix (Fin 2) (Fin 2) ℝ) := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [eps2, Matrix.mul_apply, Fin.sum_univ_two]
  calc realEighthRoot2 ^ 4
      = (realEighthRoot2 * realEighthRoot2) * (realEighthRoot2 * realEighthRoot2) := by
          simp only [pow_succ, pow_zero, one_mul, Matrix.mul_assoc]
    _ = eps2 * eps2 := by rw [realEighthRoot2_sq]
    _ = -(1 : Matrix (Fin 2) (Fin 2) ℝ) := heps2

/-- Purely real `M₂(ℝ)` solution to the Euclidean quartic constraint `T⁴ = -(3/4) • I₂` without
complex `i`, scaling `realEighthRoot2` by `(3/4)^{1/4} = √(√(3/4))`. -/
theorem realQuarticNegThreeFourths_pow_four :
    let r : ℝ := Real.sqrt (Real.sqrt (3 / 4 : ℝ))
    (r • realEighthRoot2) ^ 4 = -(3 / 4 : ℝ) • (1 : Matrix (Fin 2) (Fin 2) ℝ) := by
  intro r
  have hr2 : r ^ 2 = Real.sqrt (3 / 4 : ℝ) := Real.sq_sqrt (Real.sqrt_nonneg _)
  have hr4 : r ^ 4 = (3 / 4 : ℝ) := by
    calc r ^ 4 = (r ^ 2) ^ 2 := by ring
      _ = Real.sqrt (3 / 4 : ℝ) ^ 2 := by rw [hr2]
      _ = 3 / 4 := Real.sq_sqrt (by norm_num)
  have hPowScale : (r • realEighthRoot2) ^ 4 = (r ^ 4) • (realEighthRoot2 ^ 4) := by
    simp only [pow_succ, pow_zero, one_mul, smul_mul_assoc, mul_smul_comm, smul_smul]
    congr 1
    ring
  rw [hPowScale, hr4, realEighthRoot2_pow_four, smul_neg, neg_smul]

end RealCl11EighthRoot

end InfoGeometry.Canonical.SochichiuComplexRigidityAndRealEighthRootBridge
