import InfoGeometry.Canonical.YangBaxterProof

/-!
# Explicit noncommutativity of the Fibonacci braid generators

The Yang--Baxter owner proves the Artin equality for the concrete matrices
`R` and `B = F * R * F`.  This companion owner records the complementary
noncommutativity fact.  It uses only a matrix entry and the intrinsic scalar
relations already proved in `YangBaxterProof`.
-/

noncomputable section

namespace InfoGeometry.Canonical.FibonacciBraidNoncommutativityBridge

open Matrix
open InfoGeometry.Canonical.YangBaxterProof

private theorem tau_ne_zero : τ ≠ 0 := by
  intro hτ
  change (tauR : ℂ) = 0 at hτ
  have h : tauR = 0 := by exact_mod_cast hτ
  unfold tauR at h
  have hsqrt : (Real.sqrt (5 : ℝ)) ^ 2 = 5 :=
    Real.sq_sqrt (by norm_num)
  have hsq : Real.sqrt (5 : ℝ) = 1 := by linarith
  nlinarith

private theorem s_ne_zero : s ≠ 0 := by
  intro hs
  change (Real.sqrt tauR : ℂ) = 0 at hs
  have hsqrt : Real.sqrt tauR = 0 := by exact_mod_cast hs
  have hτ : tauR = 0 := by
    have hnonneg : 0 ≤ tauR := tauR_nonneg
    calc
      tauR = (Real.sqrt tauR) ^ 2 := by
        symm
        exact Real.sq_sqrt hnonneg
      _ = 0 := by rw [hsqrt]; norm_num
  apply tau_ne_zero
  change (tauR : ℂ) = 0
  exact_mod_cast hτ

private theorem q_cubed_ne_neg_q : q ^ 3 ≠ -q := by
  intro hqt
  have hq0 : q ≠ 0 := Complex.exp_ne_zero _
  have hfactor : q * (q ^ 2 + 1) = 0 := by
    calc
      q * (q ^ 2 + 1) = q ^ 3 + q := by ring
      _ = 0 := by rw [hqt]; ring
  have hq2 : q ^ 2 = -1 := by
    rcases mul_eq_zero.mp hfactor with hzero | hzero
    · exact False.elim (hq0 hzero)
    · calc
        q ^ 2 = (q ^ 2 + 1) - 1 := by ring
        _ = 0 - 1 := by rw [hzero]
        _ = -1 := by ring
  have hq5 : q ^ 5 = q := by
    calc
      q ^ 5 = q * (q ^ 2) ^ 2 := by ring
      _ = q * (-1 : ℂ) ^ 2 := by rw [hq2]
      _ = q := by ring
  have hqneg : q = -1 := by
    rw [q_pow_five] at hq5
    exact hq5.symm
  rw [hqneg] at hq2
  norm_num at hq2

theorem braid_generators_noncommute : R * B ≠ B * R := by
  intro hcomm
  have hR : R = diagonalBraidMatrixC (-q) (q ^ 3) := by
    ext i j
    fin_cases i <;> fin_cases j
    · calc
        R 0 0 = q ^ (-4 : ℤ) := rfl
        _ = (q ^ 4)⁻¹ := by
          simp [zpow_neg (q : ℂ) (4 : ℤ)]
          simpa using (zpow_natCast q 4)
        _ = -q := q_inv_four_eq_neg_q
    · simp [R, diagonalBraidMatrixC]
    · simp [R, diagonalBraidMatrixC]
    · simp [R, diagonalBraidMatrixC]
  have hB : B = F * diagonalBraidMatrixC (-q) (q ^ 3) * F := by
    rw [B, hR]
  rw [hR, hB] at hcomm
  have hentry := congrArg (fun M : Matrix (Fin 2) (Fin 2) ℂ => M 0 1) hcomm
  have hentry' := hentry
  simp [F, diagonalBraidMatrixC, Matrix.mul_apply, Fin.sum_univ_two] at hentry'
  have hscalar : τ * s * ((-q) - q ^ 3) ^ 2 = 0 := by
    calc
      τ * s * ((-q) - q ^ 3) ^ 2 =
          (-q) * (τ * (-q) * s + -(s * q ^ 3 * τ)) -
            (τ * (-q) * s + -(s * q ^ 3 * τ)) * q ^ 3 := by ring
      _ = 0 := by
        apply sub_eq_zero.mpr
        convert hentry' using 1 <;> ring
  have hdiff : (-q : ℂ) - q ^ 3 ≠ 0 := by
    intro hzero
    apply q_cubed_ne_neg_q
    calc
      q ^ 3 = -((-q) - q ^ 3) - q := by ring
      _ = -0 - q := by rw [hzero]
      _ = -q := by ring
  have hτs : τ * s ≠ 0 := mul_ne_zero tau_ne_zero s_ne_zero
  exact hτs (by
    apply (mul_eq_zero.mp hscalar).resolve_right
    exact pow_ne_zero 2 hdiff)

end InfoGeometry.Canonical.FibonacciBraidNoncommutativityBridge
