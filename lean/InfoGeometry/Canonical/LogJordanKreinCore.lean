/-!
LogCFT–Krein Bridge Core
Rank-(1,1) Jordan–Krein bridge with genuine 2×2 matrix proofs.
This is the exact mathematical apex identified by the Socratic audit:
a non-diagonalizable Jordan operator is genuinely self-adjoint with respect
to an indefinite metric of signature (1,1).
-/

import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.LinearAlgebra.Matrix.Basic
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.Algebra.Module.End.Basic

open Matrix

namespace InfoGeometry.Canonical.LogJordanKreinCore

/-- The nilpotent Jordan cell N = [[0, 1], [0, 0]] -/
def N : Matrix (Fin 2) (Fin 2) ℝ :=
  !![0, 1; 0, 0]

/-- The Jordan operator L_Δ = Δ·I + N -/
def L0 (Δ : ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  !![Δ, 1; 0, Δ]

/-- The Krein metric G = [[0, 1], [1, 0]] of signature (1,1) -/
def kreinG : Matrix (Fin 2) (Fin 2) ℝ :=
  !![0, 1; 1, 0]

/-- The parity/chirality operator χ = diag(1, -1) -/
def parity : Matrix (Fin 2) (Fin 2) ℝ :=
  !![1, 0; 0, -1]

/-- 1. N² = 0, N ≠ 0 -/
theorem jordanNilpotent_sq :
    N * N = 0 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
  simp [N, Matrix.mul_apply, Fin.sum_univ_two]
  <;> norm_num

theorem jordanNilpotent_ne_zero :
    N ≠ 0 := by
  intro h
  have h₁ := congr_arg (fun M : Matrix (Fin 2) (Fin 2) ℝ => M 0 1) h
  norm_num [N] at h₁

/-- 2. L_Δ is Krein-self-adjoint: L_Δᵀ G = G L_Δ -/
theorem jordanCell_krein_selfAdjoint (Δ : ℝ) :
    (L0 Δ).transpose * kreinG = kreinG * L0 Δ := by
  ext i j
  fin_cases i <;> fin_cases j <;>
  simp [L0, kreinG, Matrix.transpose_apply, Matrix.mul_apply, Fin.sum_univ_two]
  <;> ring_nf
  <;> norm_num
  <;> linarith

/-- 3. L_Δ is not diagonalizable over ℝ -/
theorem jordanCell_not_diagonalizable (Δ : ℝ) :
    ¬ IsDiagonalizable ℝ (Matrix.toLin' (L0 Δ)) := by
  intro h
  -- The minimal polynomial of L_Δ is (x - Δ)², which has a double root
  -- but L_Δ is not a scalar multiple of identity
  have h₁ : Matrix.toLin' (L0 Δ) = Matrix.toLin' (!![Δ, 1; 0, Δ]) := by rfl
  rw [h₁] at h
  -- A 2×2 matrix with a double eigenvalue is diagonalizable iff it's already diagonal
  -- Since L_Δ has a 1 in the upper-right, it's not diagonal
  have h₂ := h
  simp [IsDiagonalizable, Matrix.toLin'_apply, Fin.sum_univ_two] at h₂
  -- Use the fact that the matrix is not a scalar multiple of identity
  have h₃ : ∃ (v : Fin 2 → ℝ), (Matrix.toLin' (!![Δ, 1; 0, Δ])) v = Δ • v := by
    use ![0, 1]
    ext i
    fin_cases i <;>
    simp [Matrix.toLin'_apply, Fin.sum_univ_two, Matrix.dotProduct, Fin.val_zero, Fin.val_one]
    <;> norm_num <;>
    (try ring_nf) <;>
    (try simp_all [Pi.smul_apply]) <;>
    (try norm_num) <;>
    (try linarith)
  -- The eigenspace is 1-dimensional, so not diagonalizable
  have h₄ : ¬ IsDiagonalizable ℝ (Matrix.toLin' (!![Δ, 1; 0, Δ])) := by
    intro h_diag
    -- If diagonalizable, there would be a basis of eigenvectors
    -- But the geometric multiplicity of eigenvalue Δ is 1
    have h₅ : FiniteDimensional.finrank ℝ (Fin 2 → ℝ) = 2 := by
      simp [FiniteDimensional.finrank_pi]
    have h₆ := h_diag
    simp [IsDiagonalizable, FiniteDimensional.finrank_pi] at h₆
    <;>
    (try contradiction) <;>
    (try
      {
        -- The eigenspace for Δ has dimension 1
        have h₇ : ∃ (v : Fin 2 → ℝ), v ≠ 0 ∧ (Matrix.toLin' (!![Δ, 1; 0, Δ])) v = Δ • v := by
          use ![0, 1]
          constructor
          · intro h_v
            have h₈ := congr_fun h_v 0
            norm_num [Matrix.toLin'_apply, Fin.sum_univ_two, Matrix.dotProduct, Fin.val_zero, Fin.val_one] at h₈ ⊢
            <;> simp_all [Pi.smul_apply]
            <;> norm_num at * <;> linarith
          · ext i
            fin_cases i <;>
            simp [Matrix.toLin'_apply, Fin.sum_univ_two, Matrix.dotProduct, Fin.val_zero, Fin.val_one]
            <;> norm_num <;>
            (try ring_nf) <;>
            (try simp_all [Pi.smul_apply]) <;>
            (try norm_num) <;>
            (try linarith)
        -- Cannot have 2 independent eigenvectors
        obtain ⟨v, hv₁, hv₂⟩ := h₇
        have h₈ : ¬ IsDiagonalizable ℝ (Matrix.toLin' (!![Δ, 1; 0, Δ])) := by
          intro h_diag'
          -- If diagonalizable over ℝ, the minimal polynomial would be (x - Δ)
          -- But (L_Δ - Δ·I) = N ≠ 0, so minimal polynomial is (x - Δ)²
          simp [IsDiagonalizable, Matrix.toLin'_apply, Fin.sum_univ_two] at h_diag'
          <;>
          (try contradiction) <;>
          (try
            {
              -- Use the fact that N ≠ 0
              have h₉ := congr_arg (fun M : Matrix (Fin 2) (Fin 2) ℝ => M 0 1) (by
                have h₁₀ : Matrix.toLin' (!![Δ, 1; 0, Δ]) - Δ • (1 : Matrix (Fin 2) (Fin 2) ℝ) = Matrix.toLin' N := by
                  ext i j
                  fin_cases i <;> fin_cases j <;>
                  simp [Matrix.toLin'_apply, Fin.sum_univ_two, Matrix.one_apply, Matrix.sub_apply, Matrix.smul_apply, N, L0]
                  <;> ring_nf
                  <;> norm_num
                  <;> linarith
                simpa [h₁₀] using h_diag')
              norm_num [N] at h₉
              <;> simp_all
            })
        exact h₈ h_diag'
      })
  exact h₄ h₂

/-- 4. exp(t L_Δ) = e^{tΔ} (I + t N) -/
theorem exp_jordanCell (t Δ : ℝ) :
    exp (t • L0 Δ) =
      Real.exp (t * Δ) • (1 + t • N) := by
  have h₁ : exp (t • L0 Δ) = exp (t • (!![Δ, 1; 0, Δ])) := by rfl
  rw [h₁]
  -- Use the fact that L_Δ = Δ·I + N and N commutes with I
  -- So exp(t(Δ·I + N)) = exp(tΔ·I) * exp(tN) = e^{tΔ}·I * (I + tN)
  have h₂ : exp (t • (!![Δ, 1; 0, Δ])) = Real.exp (t * Δ) • (1 + t • N) := by
    -- Compute the matrix exponential directly
    have h₃ : exp (t • (!![Δ, 1; 0, Δ])) = !![Real.exp (t * Δ), t * Real.exp (t * Δ); 0, Real.exp (t * Δ)] := by
      -- Use the formula for exponential of a Jordan block
      rw [Matrix.exp_apply]
      -- The series for exp(tL_Δ) can be computed directly
      have h₄ : ∀ n : ℕ, (t • (!![Δ, 1; 0, Δ] : Matrix (Fin 2) (Fin 2) ℝ)) ^ n = (t ^ n : ℝ) • (!![Δ, 1; 0, Δ] : Matrix (Fin 2) (Fin 2) ℝ) ^ n := by
        intro n
        simp [Matrix.smul_pow, Matrix.mul_smul, smul_mul_assoc]
        <;>
        (try ring_nf) <;>
        (try simp_all [Matrix.one_mul, Matrix.mul_one])
      -- Direct computation of the series
      have h₅ : exp (t • (!![Δ, 1; 0, Δ] : Matrix (Fin 2) (Fin 2) ℝ)) = !![Real.exp (t * Δ), t * Real.exp (t * Δ); 0, Real.exp (t * Δ)] := by
        -- Use the known formula for exponential of a 2×2 Jordan block
        rw [Matrix.exp_apply]
        -- Compute the series term by term
        have h₆ : ∀ (i j : Fin 2), (∑' n : ℕ, (1 / n.factorial : ℝ) • (t • (!![Δ, 1; 0, Δ] : Matrix (Fin 2) (Fin 2) ℝ)) ^ n) i j = (!![Real.exp (t * Δ), t * Real.exp (t * Δ); 0, Real.exp (t * Δ)] : Matrix (Fin 2) (Fin 2) ℝ) i j := by
          intro i j
          fin_cases i <;> fin_cases j <;>
          simp [Matrix.exp_apply, Matrix.one_apply, Matrix.add_apply, Matrix.smul_apply, Fin.sum_univ_two, pow_succ, Matrix.mul_apply, Fin.sum_univ_two]
          <;>
          (try norm_num) <;>
          (try
            {
              -- Compute the series for each entry
              have h₇ : ∑' n : ℕ, (1 / n.factorial : ℝ) * (t : ℝ) ^ n * (Δ : ℝ) ^ n = Real.exp (t * Δ) := by
                have h₈ : ∑' n : ℕ, (1 / n.factorial : ℝ) * (t * Δ : ℝ) ^ n = Real.exp (t * Δ) := by
                  rw [Real.exp_eq_tsum]
                  <;> simp [mul_pow]
                  <;> congr 1 <;> ext n <;> ring_nf
                calc
                  ∑' n : ℕ, (1 / n.factorial : ℝ) * (t : ℝ) ^ n * (Δ : ℝ) ^ n = ∑' n : ℕ, (1 / n.factorial : ℝ) * ((t : ℝ) * Δ) ^ n := by
                    congr with n
                    ring_nf
                  _ = Real.exp (t * Δ) := by rw [h₈]
              have h₉ : ∑' n : ℕ, (1 / n.factorial : ℝ) * (t : ℝ) ^ n * (n : ℝ) * (Δ : ℝ) ^ (n - 1) = t * Real.exp (t * Δ) := by
                have h₁₀ : ∑' n : ℕ, (1 / n.factorial : ℝ) * (t : ℝ) ^ n * (n : ℝ) * (Δ : ℝ) ^ (n - 1) = t * Real.exp (t * Δ) := by
                  -- Derivative of exp(tΔ) with respect to Δ
                  have h₁₁ : ∑' n : ℕ, (1 / n.factorial : ℝ) * (t * Δ : ℝ) ^ n = Real.exp (t * Δ) := by
                    rw [Real.exp_eq_tsum]
                    <;> simp [mul_pow]
                    <;> congr 1 <;> ext n <;> ring_nf
                  -- Use the fact that the series for the off-diagonal term is t * exp(tΔ)
                  have h₁₂ : ∑' n : ℕ, (1 / n.factorial : ℝ) * (t : ℝ) ^ n * (n : ℝ) * (Δ : ℝ) ^ (n - 1) = t * Real.exp (t * Δ) := by
                    -- This follows from differentiating the series
                    have h₁₃ : HasDerivAt (fun Δ : ℝ => Real.exp (t * Δ)) (t * Real.exp (t * Δ)) Δ := by
                      have h₁₄ : HasDerivAt (fun Δ : ℝ => Real.exp (t * Δ)) (Real.exp (t * Δ) * t) Δ := by
                        have h₁₅ : HasDerivAt (fun Δ : ℝ => (t * Δ : ℝ)) t Δ := by
                          simpa using (hasDerivAt_id Δ).const_mul t
                        have h₁₆ : HasDerivAt (fun x : ℝ => Real.exp x) (Real.exp (t * Δ)) (t * Δ) := Real.hasDerivAt_exp (t * Δ)
                        have h₁₇ : HasDerivAt (fun Δ : ℝ => Real.exp (t * Δ)) (Real.exp (t * Δ) * t) Δ := HasDerivAt.comp Δ h₁₆ h₁₅
                        exact h₁₇
                      convert h₁₄ using 1 <;> ring
                    -- The series derivative gives the off-diagonal term
                    have h₁₈ : ∑' n : ℕ, (1 / n.factorial : ℝ) * (t : ℝ) ^ n * (n : ℝ) * (Δ : ℝ) ^ (n - 1) = t * Real.exp (t * Δ) := by
                      -- This is a known result about the derivative of the exponential series
                      have h₁₉ : ∀ (n : ℕ), (1 / (n : ℕ).factorial : ℝ) * (t : ℝ) ^ n * (n : ℝ) * (Δ : ℝ) ^ (n - 1) = (1 / (n : ℕ).factorial : ℝ) * (t : ℝ) ^ n * (n : ℝ) * (Δ : ℝ) ^ (n - 1) := by rfl
                      -- Use the fact that the series for the derivative of exp(tΔ) is t * exp(tΔ)
                      have h₂₀ : ∑' n : ℕ, (1 / n.factorial : ℝ) * (t : ℝ) ^ n * (n : ℝ) * (Δ : ℝ) ^ (n - 1) = t * Real.exp (t * Δ) := by
                        -- This follows from term-by-term differentiation
                        have h₂₁ : ∑' n : ℕ, (1 / n.factorial : ℝ) * (t : ℝ) ^ n * (n : ℝ) * (Δ : ℝ) ^ (n - 1) = ∑' n : ℕ, (1 / n.factorial : ℝ) * (t : ℝ) ^ n * (n : ℝ) * (Δ : ℝ) ^ (n - 1) := rfl
                        -- For n=0, the term is 0
                        -- For n≥1, the term is (t^n / (n-1)!) * Δ^(n-1)
                        -- Sum = t * ∑_{k≥0} (tΔ)^k / k! = t * exp(tΔ)
                        have h₂₂ : ∑' n : ℕ, (1 / n.factorial : ℝ) * (t : ℝ) ^ n * (n : ℝ) * (Δ : ℝ) ^ (n - 1) = t * Real.exp (t * Δ) := by
                          -- Use the known series identity
                          have h₂₃ : ∑' n : ℕ, (1 / n.factorial : ℝ) * (t : ℝ) ^ n * (n : ℝ) * (Δ : ℝ) ^ (n - 1) = ∑' n : ℕ, (if n = 0 then 0 else (1 / (n - 1).factorial : ℝ) * (t : ℝ) ^ n * (Δ : ℝ) ^ (n - 1)) := by
                            apply tsum_congr
                            intro n
                            by_cases hn : n = 0
                            · simp [hn]
                            · have h₂₄ : (n : ℕ) ≠ 0 := hn
                              have h₂₅ : (n : ℝ) ≠ 0 := by norm_cast <;> intro h₂₆; apply h₂₄; simp_all
                              field_simp [Nat.factorial_succ, h₂₅]
                              <;> ring_nf
                              <;> field_simp [Nat.cast_add_one_ne_zero]
                              <;> ring_nf
                              <;> norm_cast
                              <;> simp_all [Nat.factorial_succ]
                              <;> field_simp [Nat.cast_add_one_ne_zero]
                              <;> ring_nf
                          rw [h₂₃]
                          have h₂₆ : ∑' n : ℕ, (if n = 0 then (0 : ℝ) else (1 / (n - 1).factorial : ℝ) * (t : ℝ) ^ n * (Δ : ℝ) ^ (n - 1)) = t * Real.exp (t * Δ) := by
                            have h₂₇ : ∑' n : ℕ, (if n = 0 then (0 : ℝ) else (1 / (n - 1).factorial : ℝ) * (t : ℝ) ^ n * (Δ : ℝ) ^ (n - 1)) = ∑' n : ℕ, (1 / n.factorial : ℝ) * (t : ℝ) ^ (n + 1) * (Δ : ℝ) ^ n := by
                              apply tsum_congr
                              intro n
                              cases n with
                              | zero => simp
                              | succ n =>
                                simp [Nat.factorial_succ, Nat.cast_add_one_ne_zero]
                                <;> field_simp [Nat.cast_add_one_ne_zero]
                                <;> ring_nf
                                <;> norm_num
                                <;> simp_all [pow_succ, mul_assoc]
                                <;> field_simp [Nat.cast_add_one_ne_zero]
                                <;> ring_nf
                            rw [h₂₇]
                            have h₂₈ : ∑' n : ℕ, (1 / n.factorial : ℝ) * (t : ℝ) ^ (n + 1) * (Δ : ℝ) ^ n = t * Real.exp (t * Δ) := by
                              calc
                                ∑' n : ℕ, (1 / n.factorial : ℝ) * (t : ℝ) ^ (n + 1) * (Δ : ℝ) ^ n = ∑' n : ℕ, (t : ℝ) * ((1 / n.factorial : ℝ) * (t * Δ : ℝ) ^ n) := by
                                  apply tsum_congr
                                  intro n
                                  ring_nf
                                  <;> field_simp [pow_succ, mul_assoc]
                                  <;> ring_nf
                                _ = (t : ℝ) * ∑' n : ℕ, (1 / n.factorial : ℝ) * (t * Δ : ℝ) ^ n := by
                                  rw [tsum_mul_left]
                                _ = (t : ℝ) * Real.exp (t * Δ) := by
                                  have h₂₉ : ∑' n : ℕ, (1 / n.factorial : ℝ) * (t * Δ : ℝ) ^ n = Real.exp (t * Δ) := by
                                    rw [Real.exp_eq_tsum]
                                    <;> simp [mul_pow]
                                    <;> congr 1 <;> ext n <;> ring_nf
                                  rw [h₂₉]
                                  <;> ring_nf
                            rw [h₂₈]
                            <;> ring_nf
                          rw [h₂₆]
                          <;> ring_nf
                        rw [h₂₂]
                      rw [h₂₀]
                    rw [h₁₈]
                  rw [h₁₂]
                <;>
                (try simp_all [tsum_mul_left, tsum_mul_right])
                <;>
                (try norm_num)
                <;>
                (try linarith)
              simp_all [tsum_mul_left, tsum_mul_right]
              <;>
              (try norm_num)
              <;>
              (try linarith)
            })
          <;>
          (try
            {
              -- The (1,1) entry is 0
              simp_all [tsum_mul_left, tsum_mul_right]
              <;> norm_num
              <;> linarith
            })
          <;>
          (try
            {
              -- The (2,2) entry is exp(tΔ)
              have h₇ : ∑' n : ℕ, (1 / n.factorial : ℝ) * (t : ℝ) ^ n * (Δ : ℝ) ^ n = Real.exp (t * Δ) := by
                have h₈ : ∑' n : ℕ, (1 / n.factorial : ℝ) * (t * Δ : ℝ) ^ n = Real.exp (t * Δ) := by
                  rw [Real.exp_eq_tsum]
                  <;> simp [mul_pow]
                  <;> congr 1 <;> ext n <;> ring_nf
                calc
                  ∑' n : ℕ, (1 / n.factorial : ℝ) * (t : ℝ) ^ n * (Δ : ℝ) ^ n = ∑' n : ℕ, (1 / n.factorial : ℝ) * ((t : ℝ) * Δ) ^ n := by
                    congr with n
                    ring_nf
                  _ = Real.exp (t * Δ) := by rw [h₈]
              simp_all [tsum_mul_left, tsum_mul_right]
              <;> norm_num
              <;> linarith
            })
        -- Use the computed series to get the matrix exponential
        have h₁₀ : (∑' n : ℕ, (1 / n.factorial : ℝ) • (t • (!![Δ, 1; 0, Δ] : Matrix (Fin 2) (Fin 2) ℝ)) ^ n) = !![Real.exp (t * Δ), t * Real.exp (t * Δ); 0, Real.exp (t * Δ)] := by
          ext i j
          rw [h₆ i j]
          <;> simp [Matrix.one_apply, Matrix.add_apply, Matrix.smul_apply]
          <;> aesop
        simp_all [Matrix.exp_apply]
        <;>
        (try aesop)
      rw [h₅]
      <;> simp [Matrix.exp_apply]
    rw [h₃]
    -- Now show this equals e^{tΔ} (I + tN)
    ext i j
    fin_cases i <;> fin_cases j <;>
    simp [N, Matrix.one_apply, Matrix.add_apply, Matrix.smul_apply, Fin.sum_univ_two]
    <;> ring_nf
    <;> field_simp [Real.exp_mul, Real.exp_log]
    <;> ring_nf
    <;> norm_num
    <;> linarith [Real.exp_pos (t * Δ)]
  rw [h₂]
  <;> simp [Matrix.exp_apply]

/-- 5. Tr(exp(t L_Δ)) = 2 e^{tΔ} -/
theorem trace_exp_jordanCell (t Δ : ℝ) :
    Matrix.trace (exp (t • L0 Δ)) =
      2 * Real.exp (t * Δ) := by
  rw [exp_jordanCell]
  simp [Matrix.trace, N, Matrix.one_apply, Matrix.add_apply, Matrix.smul_apply, Fin.sum_univ_two]
  <;> ring_nf
  <;> norm_num
  <;> field_simp [Real.exp_mul, Real.exp_log]
  <;> ring_nf
  <;> norm_num
  <;> linarith [Real.exp_pos (t * Δ)]

/-- 6. Tr(Nᵀ exp(t L_Δ)) = t e^{tΔ} -/
theorem detector_trace_jordanCell (t Δ : ℝ) :
    Matrix.trace (N.transpose * exp (t • L0 Δ)) =
      t * Real.exp (t * Δ) := by
  rw [exp_jordanCell]
  simp [Matrix.trace, N, Matrix.one_apply, Matrix.add_apply, Matrix.smul_apply, Matrix.mul_apply, Fin.sum_univ_two, Matrix.transpose_apply]
  <;> ring_nf
  <;> norm_num
  <;> field_simp [Real.exp_mul, Real.exp_log]
  <;> ring_nf
  <;> norm_num
  <;> linarith [Real.exp_pos (t * Δ)]

/-- 7. Tr(χ exp(t L_Δ)) = 0 -/
theorem parity_trace_jordanCell (t Δ : ℝ) :
    Matrix.trace (parity * exp (t • L0 Δ)) = 0 := by
  rw [exp_jordanCell]
  simp [Matrix.trace, parity, N, Matrix.one_apply, Matrix.add_apply, Matrix.smul_apply, Matrix.mul_apply, Fin.sum_univ_two]
  <;> ring_nf
  <;> norm_num
  <;> field_simp [Real.exp_mul, Real.exp_log]
  <;> ring_nf
  <;> norm_num
  <;> linarith [Real.exp_pos (t * Δ)]

/-- 8. The eigenspace of L_Δ for eigenvalue Δ is 1-dimensional -/
theorem jordanCell_eigenspace_dim_one (Δ : ℝ) :
    ∃ (v : Fin 2 → ℝ), v ≠ 0 ∧ (Matrix.toLin' (L0 Δ)) v = Δ • v ∧
    ∀ (w : Fin 2 → ℝ), (Matrix.toLin' (L0 Δ)) w = Δ • w → ∃ (c : ℝ), w = c • v := by
  use ![0, 1]
  constructor
  · -- v ≠ 0
    intro h
    have h₁ := congr_fun h 0
    norm_num [Matrix.toLin'_apply, Fin.sum_univ_two, Matrix.dotProduct, Fin.val_zero, Fin.val_one] at h₁ ⊢
    <;> simp_all [Pi.smul_apply]
    <;> norm_num at * <;> linarith
  constructor
  · -- L_Δ v = Δ v
    ext i
    fin_cases i <;>
    simp [Matrix.toLin'_apply, Fin.sum_univ_two, Matrix.dotProduct, Fin.val_zero, Fin.val_one, L0]
    <;> ring_nf
    <;> norm_num
    <;> simp_all [Pi.smul_apply]
    <;> norm_num at * <;> linarith
  · -- Any eigenvector is a scalar multiple of v
    intro w hw
    have h₁ := hw
    have h₂ : w 0 = 0 := by
      have h₃ := congr_fun h₁ 0
      have h₄ := congr_fun h₁ 1
      simp [Matrix.toLin'_apply, Fin.sum_univ_two, Matrix.dotProduct, Fin.val_zero, Fin.val_one, L0] at h₃ h₄
      simp [Pi.smul_apply] at h₃ h₄ ⊢
      <;>
      (try norm_num at h₃ h₄ ⊢) <;>
      (try linarith) <;>
      (try ring_nf at h₃ h₄ ⊢) <;>
      (try nlinarith)
      <;>
      (try
        {
          nlinarith
        })
    use w 1
    ext i
    fin_cases i <;>
    simp [h₂, Pi.smul_apply] at hw ⊢ <;>
    (try simp_all [Matrix.toLin'_apply, Fin.sum_univ_two, Matrix.dotProduct, Fin.val_zero, Fin.val_one, L0]) <;>
    (try ring_nf at * <;> nlinarith) <;>
    (try linarith)

end InfoGeometry.Canonical.LogJordanKreinCore