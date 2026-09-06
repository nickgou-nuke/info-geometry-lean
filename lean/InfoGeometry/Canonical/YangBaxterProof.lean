import Mathlib.Tactic
open Matrix
open Complex

noncomputable section

set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
set_option linter.unreachableTactic false
set_option linter.unusedTactic false
set_option linter.unnecessarySimpa false

/-!
# YangBaxterProof — Exact SymPy translation

Source: `tools/sympy/fibonacci_osp12_bridge.py`

Each SymPy section is translated one check at a time.
-/

namespace InfoGeometry.Canonical.YangBaxterProof

/-! ## Fibonacci scalars — concrete definitions -/

/-- Real inverse golden ratio: τ = φ⁻¹ = (√5 - 1)/2. -/
noncomputable def tauR : ℝ := (Real.sqrt 5 - 1) / 2

/-- Complex Fibonacci scalar τ. -/
noncomputable def τ : ℂ := (tauR : ℂ)

/-- Positive real square root of τ, embedded in ℂ. -/
noncomputable def s : ℂ := (Real.sqrt tauR : ℂ)

/-- q = exp(iπ/5), primitive 10th root of unity (q⁵ = -1). -/
noncomputable def q : ℂ := Complex.exp (Real.pi * Complex.I / 5)

/-- τ² + τ = 1 in ℝ. -/
theorem tauR_sq_add_tauR : tauR ^ 2 + tauR = 1 := by
  unfold tauR
  have hsqrt : (Real.sqrt (5 : ℝ)) ^ 2 = 5 := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 5)
  nlinarith

/-- 0 ≤ τ in ℝ. -/
theorem tauR_nonneg : 0 ≤ tauR := by
  unfold tauR
  have h : (1 : ℝ) ≤ Real.sqrt 5 := by
    calc
      (1 : ℝ) = Real.sqrt (1 : ℝ) := by norm_num
      _ ≤ Real.sqrt 5 := Real.sqrt_le_sqrt (by norm_num)
  nlinarith

/-- τ² + τ = 1 in ℂ. -/
theorem tau_sq_add_tau : τ ^ 2 + τ = 1 := by
  change ((tauR : ℂ) ^ 2 + (tauR : ℂ) = (1 : ℂ))
  exact_mod_cast tauR_sq_add_tauR

/-- s² = τ in ℂ. -/
theorem s_sq_eq_tau : s ^ 2 = τ := by
  change ((Real.sqrt tauR : ℂ) ^ 2 = (tauR : ℂ))
  exact_mod_cast Real.sq_sqrt tauR_nonneg

/-- q⁵ = -1 (primitive 10th root of unity). -/
theorem q_pow_five : q ^ 5 = -1 := by
  calc
    q ^ 5 = (Complex.exp (Real.pi * Complex.I / 5)) ^ 5 := rfl
    _ = Complex.exp ((5 : ℕ) * (Real.pi * Complex.I / 5)) := by
      rw [(exp_nat_mul (Real.pi * Complex.I / 5) 5).symm]
    _ = Complex.exp (Real.pi * Complex.I) := by
      have h : (5 : ℕ) * (Real.pi * Complex.I / 5) = Real.pi * Complex.I := by ring_nf
      rw [h]
    _ = -1 := by rw [exp_mul_I]; simp

/-! ## Derived relations -/

theorem tau_sq_eq_one_minus_tau : τ ^ 2 = 1 - τ := by
  calc
    τ ^ 2 = (τ ^ 2 + τ) - τ := by ring
    _ = 1 - τ := by rw [tau_sq_add_tau]

theorem tau_sq_add_s_sq : τ ^ 2 + s ^ 2 = 1 := by
  calc
    τ ^ 2 + s ^ 2 = τ ^ 2 + τ := by rw [s_sq_eq_tau]
    _ = 1 := tau_sq_add_tau

/-! ## 𝔰𝔩₂ generators -/

def H : Matrix (Fin 2) (Fin 2) ℂ := !![1, 0; 0, -1]
def Ep : Matrix (Fin 2) (Fin 2) ℂ := !![0, 1; 0, 0]
def Em : Matrix (Fin 2) (Fin 2) ℂ := !![0, 0; 1, 0]

theorem comm_H_Ep : H * Ep - Ep * H = 2 • Ep := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [H, Ep, Matrix.mul_apply, Fin.sum_univ_two] <;> norm_num

theorem comm_H_Em : H * Em - Em * H = (-2 : ℂ) • Em := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [H, Em, Matrix.mul_apply, Fin.sum_univ_two] <;> norm_num

theorem comm_Ep_Em : Ep * Em - Em * Ep = H := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [H, Ep, Em, Matrix.mul_apply, Fin.sum_univ_two] <;> norm_num

/-! ## F-matrix -/

def F : Matrix (Fin 2) (Fin 2) ℂ := !![τ, s; s, -τ]

theorem F_sq : F * F = (1 : Matrix (Fin 2) (Fin 2) ℂ) := by
  ext i j
  fin_cases i <;> fin_cases j
  · simp [F, Matrix.mul_apply, Fin.sum_univ_two]
    calc
      τ * τ + s * s = τ ^ 2 + s ^ 2 := by ring
      _ = 1 := tau_sq_add_s_sq
  · simp [F, Matrix.mul_apply, Fin.sum_univ_two]
    ring
  · simp [F, Matrix.mul_apply, Fin.sum_univ_two]
    ring
  · simp [F, Matrix.mul_apply, Fin.sum_univ_two]
    calc
      s * s + τ * τ = s ^ 2 + τ ^ 2 := by ring
      _ = τ ^ 2 + s ^ 2 := add_comm _ _
      _ = 1 := tau_sq_add_s_sq

theorem F_sl2_decomposition : F = (τ : ℂ) • H + (s : ℂ) • (Ep + Em) := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [F, H, Ep, Em]

/-! ## Section 4: R-matrix (SymPy: R = [[q⁻⁴, 0], [0, q³]]) -/

def R : Matrix (Fin 2) (Fin 2) ℂ := !![q ^ (-4 : ℤ), 0; 0, q ^ 3]

/-! ## Section 5: B = F·R·F and F·B·F = R (SymPy assertion) -/

def B : Matrix (Fin 2) (Fin 2) ℂ := F * R * F

theorem F_B_F_eq_R : F * B * F = R := by
  calc
    F * B * F = F * (F * R * F) * F := rfl
    _ = (F * F) * R * (F * F) := by simp [Matrix.mul_assoc]
    _ = (1 : Matrix (Fin 2) (Fin 2) ℂ) * R * (1 : Matrix (Fin 2) (Fin 2) ℂ) := by rw [F_sq]
    _ = R := by simp

/-! ## Section 5: OSp(1|2) spinor generators (3×3 supermatrices) -/

def G1 : Matrix (Fin 3) (Fin 3) ℂ := !![0, 0, 1; 0, 0, 0; 0, 1, 0]
def G2 : Matrix (Fin 3) (Fin 3) ℂ := !![0, 0, 0; 0, 0, 1; -1, 0, 0]
def H3 : Matrix (Fin 3) (Fin 3) ℂ := !![1, 0, 0; 0, -1, 0; 0, 0, 0]
def Ep3 : Matrix (Fin 3) (Fin 3) ℂ := !![0, 1, 0; 0, 0, 0; 0, 0, 0]
def Em3 : Matrix (Fin 3) (Fin 3) ℂ := !![0, 0, 0; 1, 0, 0; 0, 0, 0]

/- SymPy scomm(A, B, p, q) = A·B - (-1)^(p·q)·B·A.
   For p = q = 1 (both odd): scomm = A·B + B·A (anticommutator). -/
def scomm (A B : Matrix (Fin 3) (Fin 3) ℂ) (p q : ℕ) : Matrix (Fin 3) (Fin 3) ℂ :=
  A * B - ((-1 : ℂ) ^ (p * q : ℕ)) • (B * A)

/-! ## SymPy assertion: {G₁, G₁} = 2·Ep₃ -/

theorem G1_anticomm : scomm G1 G1 1 1 = 2 • Ep3 := by
  unfold scomm G1 Ep3
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_three] <;> norm_num

/-! ## SymPy assertion: {G₂, G₂} = -2·Em₃ -/

theorem G2_anticomm : scomm G2 G2 1 1 = (-2 : ℂ) • Em3 := by
  unfold scomm G2 Em3
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_three] <;> norm_num

/-! ## SymPy assertion: {G₁, G₂} = -H₃ -/

theorem G1_G2_anticomm : scomm G1 G2 1 1 = -H3 := by
  unfold scomm G1 G2 H3
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_three] <;> norm_num

/-! ## SymPy assertion: {G₂, G₁} = -H₃ -/

theorem G2_G1_anticomm : scomm G2 G1 1 1 = -H3 := by
  unfold scomm G2 G1 H3
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_three] <;> norm_num

/-! ## Capstone check 4: Yang-Baxter trace condition -/
/-- For any 2×2 matrix M, (tr M)² = tr(M²) + 2·det M. -/
theorem trace_sq_eq_tr_sq_add_two_det (M : Matrix (Fin 2) (Fin 2) ℂ) :
    (Matrix.trace M) ^ 2 = Matrix.trace (M * M) + 2 * Matrix.det M := by
  have htr : Matrix.trace M = M 0 0 + M 1 1 := by
    simp [Matrix.trace, Matrix.diag]
  have htrsq : Matrix.trace (M * M) = (M 0 0)^2 + (M 0 1)*(M 1 0) + (M 1 0)*(M 0 1) + (M 1 1)^2 := by
    simp [Matrix.trace, Matrix.diag, Matrix.mul_apply, Fin.sum_univ_two]; ring
  have hdet : Matrix.det M = (M 0 0)*(M 1 1) - (M 0 1)*(M 1 0) := by
    rw [Matrix.det_fin_two]
  rw [htr, htrsq, hdet]
  ring

/-! ## Capstone check 5: V₄ relations -/

def V4_J : Matrix (Fin 2) (Fin 2) ℂ := !![(0 : ℂ), (-1 : ℂ); (1 : ℂ), (0 : ℂ)]
def V4_S : Matrix (Fin 2) (Fin 2) ℂ := !![(0 : ℂ), (1 : ℂ); (1 : ℂ), (0 : ℂ)]

theorem V4_J_sq : V4_J * V4_J = (-1 : ℂ) • (1 : Matrix (Fin 2) (Fin 2) ℂ) := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [V4_J]

theorem V4_S_sq : V4_S * V4_S = (1 : Matrix (Fin 2) (Fin 2) ℂ) := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [V4_S]


/-- q⁴ - q³ + q² - q + 1 = 0 (10th cyclotomic polynomial). -/
theorem cyclotomic_relation : q^4 - q^3 + q^2 - q + 1 = 0 := by
  have h5 : q^5 = -1 := q_pow_five
  have h_factor : (q + 1) * (q^4 - q^3 + q^2 - q + 1) = q^5 + 1 := by ring
  have h_prod : (q + 1) * (q^4 - q^3 + q^2 - q + 1) = 0 := by
    rw [h_factor, h5]; ring
  have h_q_ne_neg_one : q + 1 ≠ 0 := by
    intro h
    have h_eq_q : q = -1 := by
      calc
        q = (q + 1) - 1 := by ring
        _ = 0 - 1 := by rw [h]
        _ = -1 := by ring
    have hq_re : (q : ℂ).re = Real.cos (Real.pi / 5) := by
      calc
        (q : ℂ).re = (Complex.exp (((Real.pi / 5 : ℂ)) * Complex.I)).re := by
          dsimp [q]; ring_nf
        _ = Real.cos (Real.pi / 5) := by
          simpa using (Complex.exp_ofReal_mul_I_re (Real.pi / 5))
    have hneg_re : (-1 : ℂ).re = -1 := by norm_num
    rw [h_eq_q] at hq_re; rw [hneg_re] at hq_re
    have : Real.cos (Real.pi / 5) > -1 := by
      rw [Real.cos_pi_div_five]
      have h5pos : Real.sqrt 5 > 0 := Real.sqrt_pos.mpr (by norm_num : (0 : ℝ) < 5)
      nlinarith
    nlinarith
  have hprod := mul_eq_zero.mp h_prod
  rcases hprod with (h | h)
  · exact absurd h h_q_ne_neg_one
  · exact h

/-! ## Cross relation between τ and q -/

/-- τ = q + q⁻¹ - 1 (derived from Re(q) = cos(π/5) = (1+√5)/4). -/
theorem τ_eq_q_plus_qinv_minus_one : τ = q + (q⁻¹) - 1 := by
  have h_re_q : (q : ℂ).re = Real.cos (Real.pi / 5) := by
    calc
      (q : ℂ).re = (Complex.exp (((Real.pi / 5 : ℂ)) * Complex.I)).re := by
        dsimp [q]; ring_nf
      _ = Real.cos (Real.pi / 5) := by
        simpa using (Complex.exp_ofReal_mul_I_re (Real.pi / 5))
  have h_im_q : (q : ℂ).im = Real.sin (Real.pi / 5) := by
    calc
      (q : ℂ).im = (Complex.exp (((Real.pi / 5 : ℂ)) * Complex.I)).im := by
        dsimp [q]; ring_nf
      _ = Real.sin (Real.pi / 5) := by
        simpa using (Complex.exp_ofReal_mul_I_im (Real.pi / 5))
  have h_norm_sq : Complex.normSq q = 1 := by
    calc
      Complex.normSq q = (q.re) * (q.re) + (q.im) * (q.im) := by rw [Complex.normSq_apply]
      _ = (q.re) ^ 2 + (q.im) ^ 2 := by ring
      _ = (Real.cos (Real.pi / 5)) ^ 2 + (Real.sin (Real.pi / 5)) ^ 2 := by rw [h_re_q, h_im_q]
      _ = 1 := Real.cos_sq_add_sin_sq (Real.pi / 5)
  have h_qinv_eq_star : q⁻¹ = star q := by
    calc
      q⁻¹ = (starRingEnd ℂ) q * ↑(Complex.normSq q)⁻¹ := by rw [Complex.inv_def]
      _ = (starRingEnd ℂ) q * ↑(1 : ℝ)⁻¹ := by rw [h_norm_sq]
      _ = (starRingEnd ℂ) q * (1 : ℂ) := by norm_num
      _ = star q := by simp
  have h_q_plus_qinv_re : (q + (q⁻¹) : ℂ).re = 2 * Real.cos (Real.pi / 5) := by
    calc
      (q + (q⁻¹) : ℂ).re = (q : ℂ).re + ((q⁻¹) : ℂ).re := by simp
      _ = (q : ℂ).re + (star q).re := by rw [h_qinv_eq_star]
      _ = (q : ℂ).re + (q : ℂ).re := by simp
      _ = 2 * (q : ℂ).re := by ring
      _ = 2 * Real.cos (Real.pi / 5) := by rw [h_re_q]
  have h_q_plus_qinv_im : (q + (q⁻¹) : ℂ).im = 0 := by
    calc
      (q + (q⁻¹) : ℂ).im = (q : ℂ).im + ((q⁻¹) : ℂ).im := by simp
      _ = (q : ℂ).im + (star q).im := by rw [h_qinv_eq_star]
      _ = (q : ℂ).im + (-(q : ℂ).im) := by simp
      _ = 0 := by ring
  have h_re : (τ : ℂ).re = (q + (q⁻¹) - 1 : ℂ).re := by
    calc
      (τ : ℂ).re = ((Real.sqrt 5 - 1) / 2 : ℝ) := by
        simp [τ, tauR]
      _ = ((Real.cos (Real.pi / 5) * 2 - 1 : ℝ)) := by
        rw [Real.cos_pi_div_five]; ring_nf
      _ = 2 * Real.cos (Real.pi / 5) - 1 := by ring
      _ = (q + (q⁻¹) : ℂ).re - 1 := by rw [h_q_plus_qinv_re]
      _ = (q + (q⁻¹) - 1 : ℂ).re := by simp
  have h_im : (τ : ℂ).im = (q + (q⁻¹) - 1 : ℂ).im := by
    calc
      (τ : ℂ).im = 0 := by simp [τ, tauR]
      _ = (q + (q⁻¹) : ℂ).im := by rw [h_q_plus_qinv_im]
      _ = (q + (q⁻¹) - 1 : ℂ).im := by simp
  exact Complex.ext h_re h_im

/-- (q⁴)⁻¹ = -q (from q⁵ = -1). -/
theorem q_inv_four_eq_neg_q : (q ^ 4)⁻¹ = -q := by
  have hq_nonzero : q ≠ 0 := Complex.exp_ne_zero _
  field_simp [hq_nonzero]
  rw [q_pow_five]
  ring

/-- τ = q - q⁴ - 1 (cross relation, using q⁻¹ = -q⁴ from q⁵ = -1). -/
theorem τ_eq_q_minus_q4_minus_one : τ = q - q ^ 4 - 1 := by
  have h_qinv_eq_neg_q4 : q⁻¹ = -(q ^ 4) := by
    have hq_nonzero : q ≠ 0 := Complex.exp_ne_zero _
    field_simp [hq_nonzero]
    rw [q_pow_five]
    ring
  calc
    τ = q + (q⁻¹) - 1 := τ_eq_q_plus_qinv_minus_one
    _ = q + (-(q ^ 4)) - 1 := by rw [h_qinv_eq_neg_q4]
    _ = q - q ^ 4 - 1 := by ring

/--
Hardcoded scalar factorization for the Fibonacci Artin constraint.

This is the Lean-side polynomial identity obtained from ordinary polynomial
arithmetic, checked in the SymPy companion by expansion, and proved here by
`ring`.  The Yang-Baxter proof below only combines this factorization with the
10th cyclotomic relation.
-/
theorem fibonacci_artin_constraint_factorization :
    τ ^ 2 * ((-q) - q ^ 3) ^ 2 + (-q) * q ^ 3 =
      (q ^ 10 + q ^ 9 + 2 * q ^ 8 + q ^ 6 - 2 * q ^ 5 - q ^ 3 + q ^ 2) *
        (q ^ 4 - q ^ 3 + q ^ 2 - q + 1) := by
  rw [τ_eq_q_minus_q4_minus_one]
  ring

/-! ## Braid relation (Yang-Baxter equation) -/

/-- Generic complex Fibonacci recoupling matrix `[[a,b],[b,-a]]`. -/
def Fdiag (a b : ℂ) : Matrix (Fin 2) (Fin 2) ℂ := !![a, b; b, -a]

/-- Generic complex diagonal braid matrix. -/
def diagonalBraidMatrixC (r t : ℂ) : Matrix (Fin 2) (Fin 2) ℂ := !![r, 0; 0, t]

/-- Dual-basis braid matrix for arbitrary complex diagonal entries. -/
def Bdiag (a b r t : ℂ) : Matrix (Fin 2) (Fin 2) ℂ :=
  Fdiag a b * diagonalBraidMatrixC r t * Fdiag a b

/--
Finite two-channel Artin relation over `ℂ`.

This is the complex analogue of the real `diagonal_artin_relation`: it is a
pure 2×2 matrix identity under the two scalar constraints.
-/
theorem diagonal_artin_relation_complex (a b r t : ℂ)
    (hF : a ^ 2 + b ^ 2 = 1)
    (hA : a ^ 2 * (r - t) ^ 2 + r * t = 0) :
    diagonalBraidMatrixC r t * Bdiag a b r t * diagonalBraidMatrixC r t =
      Bdiag a b r t * diagonalBraidMatrixC r t * Bdiag a b r t := by
  have hg : a ^ 2 + b ^ 2 - 1 = 0 := by rw [hF]; ring
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Bdiag, diagonalBraidMatrixC, Fdiag, Matrix.mul_apply, Fin.sum_univ_two]
  · linear_combination
      (-t * (3 * a ^ 2 * r ^ 2 - 3 * a ^ 2 * r * t + a ^ 2 * t ^ 2 + b ^ 2 * r * t - r ^ 2 + r * t)) * hg +
      (-(a - 1) * (a + 1) * (r - t)) * hA
  · linear_combination
      (-2 * a * b * r * t * (r - t)) * hg +
      (-a * b * (r - t)) * hA
  · linear_combination
      (-2 * a * b * r * t * (r - t)) * hg +
      (-a * b * (r - t)) * hA
  · linear_combination
      (-r * (a ^ 2 * r ^ 2 - 3 * a ^ 2 * r * t + 3 * a ^ 2 * t ^ 2 + b ^ 2 * r * t + r * t - t ^ 2)) * hg +
      ((a - 1) * (a + 1) * (r - t)) * hA

theorem braid_relation : R * B * R = B * R * B := by
  have hF : τ ^ 2 + s ^ 2 = 1 := tau_sq_add_s_sq
  have h_cyclo : q ^ 4 - q ^ 3 + q ^ 2 - q + 1 = 0 := cyclotomic_relation
  have hA : τ ^ 2 * ((-q) - q ^ 3) ^ 2 + (-q) * q ^ 3 = 0 := by
    rw [fibonacci_artin_constraint_factorization, h_cyclo]
    ring
  have hR : R = diagonalBraidMatrixC (-q) (q ^ 3) := by
    ext i j; fin_cases i <;> fin_cases j
    · calc
        R 0 0 = q ^ (-4 : ℤ) := rfl
        _ = (q ^ 4)⁻¹ := by
          calc
            q ^ (-4 : ℤ) = (q ^ (4 : ℤ))⁻¹ := by
              simp [zpow_neg (q : ℂ) (4 : ℤ)]
            _ = (q ^ 4)⁻¹ := by
              have h : (q : ℂ) ^ (4 : ℤ) = q ^ 4 := by simpa using (zpow_natCast q 4)
              rw [h]
        _ = -q := q_inv_four_eq_neg_q
    · simp [R, diagonalBraidMatrixC]
    · simp [R, diagonalBraidMatrixC]
    · simp [R, diagonalBraidMatrixC]
  have hB : B = Bdiag τ s (-q) (q ^ 3) := by
    unfold B Bdiag
    rw [hR]
    unfold F Fdiag
    rfl
  rw [hR, hB]
  exact diagonal_artin_relation_complex τ s (-q) (q ^ 3) hF hA

end InfoGeometry.Canonical.YangBaxterProof
