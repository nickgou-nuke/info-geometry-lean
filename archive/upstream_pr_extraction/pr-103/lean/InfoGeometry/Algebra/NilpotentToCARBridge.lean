import Mathlib.Algebra.Ring.Basic
import Mathlib.Algebra.Algebra.Basic
import Mathlib.Tactic

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

noncomputable section

namespace InfoGeometry.Algebra.NilpotentToCARBridge

variable {K A : Type*} [Field K] [Ring A] [Algebra K A]

/-- Split triad generators (I, j) with I² = 1, j² = -1, and anticommutator Ij + jI = 0. -/
structure SplitTriad (A : Type*) [Ring A] where
  I : A
  j : A
  I_sq : I * I = 1
  j_sq : j * j = -1
  anticomm : I * j + j * I = 0

variable (T : SplitTriad A)

/-- Positive nilpotent mode G+ = 1/2 (I + j). -/
def GPlus (h2 : (2 : K) ≠ 0) : A :=
  (2 : K)⁻¹ • (T.I + T.j)

/-- Negative nilpotent mode G- = 1/2 (I - j). -/
def GMinus (h2 : (2 : K) ≠ 0) : A :=
  (2 : K)⁻¹ • (T.I - T.j)

private theorem smul_mul_smul
    (r s : K) (x y : A) :
    (r • x) * (s • y) = (r * s) • (x * y) := by
  rw [Algebra.smul_mul_assoc, Algebra.mul_smul_comm, smul_smul]

/-- 🏆 THEOREM: G+ is strictly nilpotent: (G+)² = 0. -/
@[simp]
theorem GPlus_sq_zero (h2 : (2 : K) ≠ 0) :
    GPlus (K := K) T h2 * GPlus (K := K) T h2 = 0 := by
  unfold GPlus
  rw [smul_mul_smul]
  have hsq : (T.I + T.j) * (T.I + T.j) = 0 := by
    calc
      (T.I + T.j) * (T.I + T.j) = T.I * T.I + T.I * T.j + T.j * T.I + T.j * T.j := by
        noncomm_ring
      _ = 1 + (T.I * T.j + T.j * T.I) - 1 := by
        rw [T.I_sq, T.j_sq]
        abel
      _ = 0 := by
        rw [T.anticomm]
        abel
  rw [hsq, smul_zero]

/-- 🏆 THEOREM: G- is strictly nilpotent: (G-)² = 0. -/
@[simp]
theorem GMinus_sq_zero (h2 : (2 : K) ≠ 0) :
    GMinus (K := K) T h2 * GMinus (K := K) T h2 = 0 := by
  unfold GMinus
  rw [smul_mul_smul]
  have hsq : (T.I - T.j) * (T.I - T.j) = 0 := by
    calc
      (T.I - T.j) * (T.I - T.j) = T.I * T.I - T.I * T.j - T.j * T.I + T.j * T.j := by
        noncomm_ring
      _ = 1 - (T.I * T.j + T.j * T.I) - 1 := by
        rw [T.I_sq, T.j_sq]
        abel
      _ = 0 := by
        rw [T.anticomm]
        abel
  rw [hsq, smul_zero]

/-- 🏆 MASTER THEOREM: Canonical Anticommutation Relation (CAR) {G+, G-} = 1. -/
theorem CAR_anticommutation (h2 : (2 : K) ≠ 0) :
    GPlus (K := K) T h2 * GMinus (K := K) T h2 +
    GMinus (K := K) T h2 * GPlus (K := K) T h2 = 1 := by
  unfold GPlus GMinus
  rw [smul_mul_smul, smul_mul_smul, ← smul_add]
  have hsum : (T.I + T.j) * (T.I - T.j) + (T.I - T.j) * (T.I + T.j) = (4 : K) • (1 : A) := by
    calc
      (T.I + T.j) * (T.I - T.j) + (T.I - T.j) * (T.I + T.j)
        = 2 • (T.I * T.I - T.j * T.j) := by
            noncomm_ring
      _ = 2 • ((1 : A) - (-1 : A)) := by
            rw [T.I_sq, T.j_sq]
      _ = (4 : K) • (1 : A) := by
            simp only [sub_neg_eq_add]
            rw [two_smul, show (1 : A) + 1 + ((1 : A) + 1) = (4 : K) • (1 : A) by
              rw [show (4 : K) = 1 + 1 + 1 + 1 by ring, add_smul, add_smul, add_smul, one_smul]; abel]
  rw [hsum, smul_smul]
  have h4 : (2 : K)⁻¹ * (2 : K)⁻¹ * (4 : K) = 1 := by
    calc
      (2 : K)⁻¹ * (2 : K)⁻¹ * (4 : K)
        = ((2 : K)⁻¹ * 2) * ((2 : K)⁻¹ * 2) := by
            ring
      _ = 1 * 1 := by
            rw [inv_mul_cancel₀ h2]
      _ = 1 := by
            ring
  rw [h4, one_smul]

end InfoGeometry.Algebra.NilpotentToCARBridge

end noncomputable section
