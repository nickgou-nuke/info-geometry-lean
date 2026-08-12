import Mathlib
import proofs.CuntzEndomorphism
import proofs.CuntzMatrixCorner

noncomputable section

open Matrix Complex CuntzMatrixCorner

namespace CuntzWordTwoCorner

variable {A : Type*} [Ring A] [StarRing A] [Algebra ℂ A] [StarModule ℂ A]
variable (S : Fin 2 → A) [hC : CuntzO2 (S 0) (S 1)]

/-- Length-2 Cuntz words S_i S_j -/
def cuntzWordTwo (idx : Fin 2 × Fin 2) : A :=
  S idx.1 * S idx.2

/-- Matrix units constructed from length-2 words -/
def cuntzWordTwoMatrixUnit (row col : Fin 2 × Fin 2) : A :=
  cuntzWordTwo S row * star (cuntzWordTwo S col)

theorem cuntzWordTwo_star_mul_self (idx : Fin 2 × Fin 2) :
    star (cuntzWordTwo S idx) * cuntzWordTwo S idx = 1 := by
  dsimp [cuntzWordTwo]
  rw [StarMul.star_mul]
  have hiso (i : Fin 2) : star (S i) * S i = 1 := by
    fin_cases i <;> simp [hC.isom₁, hC.isom₂]
  have hortho (i j : Fin 2) (hij : i ≠ j) : star (S i) * S j = 0 := by
    fin_cases i <;> fin_cases j <;> simp_all [hC.ortho₁₂, hC.ortho₂₁]
  calc
    star (S idx.2) * star (S idx.1) * (S idx.1 * S idx.2)
      = star (S idx.2) * (star (S idx.1) * S idx.1) * S idx.2 := by noncomm_ring
    _ = star (S idx.2) * 1 * S idx.2 := by rw [hiso]
    _ = star (S idx.2) * S idx.2 := by rw [mul_one]
    _ = 1 := by rw [hiso]

theorem cuntzWordTwo_star_mul_diff {idx₁ idx₂ : Fin 2 × Fin 2} (h : idx₁ ≠ idx₂) :
    star (cuntzWordTwo S idx₁) * cuntzWordTwo S idx₂ = 0 := by
  dsimp [cuntzWordTwo]
  rw [StarMul.star_mul]
  have hiso (i : Fin 2) : star (S i) * S i = 1 := by
    fin_cases i <;> simp [hC.isom₁, hC.isom₂]
  have hortho (i j : Fin 2) (hij : i ≠ j) : star (S i) * S j = 0 := by
    fin_cases i <;> fin_cases j <;> simp_all [hC.ortho₁₂, hC.ortho₂₁]
  -- if idx1.1 ≠ idx2.1, then S idx1.1^H * S idx2.1 = 0
  by_cases h1 : idx₁.1 = idx₂.1
  · have h2 : idx₁.2 ≠ idx₂.2 := by
      intro hc
      apply h
      exact Prod.ext h1 hc
    -- if idx1.1 = idx2.1, then S idx1.1^H * S idx2.1 = 1
    calc
      star (S idx₁.2) * star (S idx₁.1) * (S idx₂.1 * S idx₂.2)
        = star (S idx₁.2) * (star (S idx₁.1) * S idx₂.1) * S idx₂.2 := by noncomm_ring
      _ = star (S idx₁.2) * (star (S idx₁.1) * S idx₁.1) * S idx₂.2 := by
        have hs := congrArg S h1
        rw [hs]
      _ = star (S idx₁.2) * 1 * S idx₂.2 := by rw [hiso]
      _ = star (S idx₁.2) * S idx₂.2 := by rw [mul_one]
      _ = 0 := by rw [hortho _ _ h2]
  · calc
      star (S idx₁.2) * star (S idx₁.1) * (S idx₂.1 * S idx₂.2)
        = star (S idx₁.2) * (star (S idx₁.1) * S idx₂.1) * S idx₂.2 := by noncomm_ring
      _ = star (S idx₁.2) * 0 * S idx₂.2 := by rw [hortho _ _ h1]
      _ = 0 := by simp

theorem cuntzWordTwo_star_mul (idx₁ idx₂ : Fin 2 × Fin 2) :
    star (cuntzWordTwo S idx₁) * cuntzWordTwo S idx₂ = if idx₁ = idx₂ then 1 else 0 := by
  split_ifs with h
  · rw [h, cuntzWordTwo_star_mul_self]
  · rw [cuntzWordTwo_star_mul_diff S h]

theorem cuntzWordTwoMatrixUnit_mul (a b c d : Fin 2 × Fin 2) :
    cuntzWordTwoMatrixUnit S a b * cuntzWordTwoMatrixUnit S c d =
      if b = c then cuntzWordTwoMatrixUnit S a d else 0 := by
  dsimp [cuntzWordTwoMatrixUnit]
  calc
    cuntzWordTwo S a * star (cuntzWordTwo S b) * (cuntzWordTwo S c * star (cuntzWordTwo S d))
      = cuntzWordTwo S a * (star (cuntzWordTwo S b) * cuntzWordTwo S c) * star (cuntzWordTwo S d) := by noncomm_ring
    _ = cuntzWordTwo S a * (if b = c then (1 : A) else 0) * star (cuntzWordTwo S d) := by rw [cuntzWordTwo_star_mul]
  split_ifs with h
  · simp only [mul_one]
  · simp only [mul_zero, zero_mul]

theorem cuntzWordTwoMatrixUnit_star (a b : Fin 2 × Fin 2) :
    star (cuntzWordTwoMatrixUnit S a b) = cuntzWordTwoMatrixUnit S b a := by
  dsimp [cuntzWordTwoMatrixUnit]
  simp only [StarMul.star_mul, star_star]

theorem cuntzWordTwoMatrixUnit_sum :
    ∑ idx : Fin 2 × Fin 2, cuntzWordTwoMatrixUnit S idx idx = 1 := by
  dsimp [cuntzWordTwoMatrixUnit, cuntzWordTwo]
  rw [Fintype.sum_prod_type, Fin.sum_univ_two, Fin.sum_univ_two, Fin.sum_univ_two]
  simp only [StarMul.star_mul]
  have step1 : (S 0 * S 0 * (star (S 0) * star (S 0)) + S 0 * S 1 * (star (S 1) * star (S 0))) = S 0 * (S 0 * star (S 0) + S 1 * star (S 1)) * star (S 0) := by noncomm_ring
  rw [step1, hC.cuntz_sum, mul_one]
  have step2 : (S 1 * S 0 * (star (S 0) * star (S 1)) + S 1 * S 1 * (star (S 1) * star (S 1))) = S 1 * (S 0 * star (S 0) + S 1 * star (S 1)) * star (S 1) := by noncomm_ring
  rw [step2, hC.cuntz_sum, mul_one]
  exact hC.cuntz_sum

/-- The level-two corner embedding -/
def cuntzWordTwoCornerMap (M : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ) : A :=
  ∑ i, ∑ j, (M i j) • cuntzWordTwoMatrixUnit S i j

-- Add, smul, one, mul, star proofs will mirror CuntzMatrixCorner precisely.
-- Once verified, this provides the required map Φ.

end CuntzWordTwoCorner
