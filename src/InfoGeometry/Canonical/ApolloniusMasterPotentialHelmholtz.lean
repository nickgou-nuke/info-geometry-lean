import Mathlib.Tactic
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Arithmetic.RiemannApolloniusMasterPotential

namespace InfoGeometry.Canonical.ApolloniusMasterPotentialHelmholtz

noncomputable section

open InfoGeometry.Arithmetic.RiemannApolloniusMasterPotential

def scalarPotential (sigma t : ℝ) : ℝ :=
  InfoGeometry.Arithmetic.RiemannApolloniusMasterPotential.masterPotential sigma t

def scaleA (sigma t : ℝ) : ℝ := sigma * (1 - sigma) + t ^ 2

def scaleB (sigma t : ℝ) : ℝ := (1 - 2 * sigma) * t

def dilationField (sigma t : ℝ) : ℝ × ℝ := (-scaleA sigma t, -scaleB sigma t)

def quarterTurn (v : ℝ × ℝ) : ℝ × ℝ := (v.2, -v.1)

def rotationalField (sigma t : ℝ) : ℝ × ℝ :=
  quarterTurn (dilationField sigma t)

def unifiedField (gamma sigma t : ℝ) : ℝ × ℝ :=
  (-gamma * scaleA sigma t - scaleB sigma t,
    -gamma * scaleB sigma t + scaleA sigma t)

theorem scalarPotential_centralLeaf (t : ℝ) :
    scalarPotential (1 / 2) t = 0 := by
  simpa [scalarPotential] using
    (masterPotential_eq_zero_on_criticalLine t)

theorem scaleA_centered (sigma t : ℝ) :
    scaleA sigma t = 1 / 4 - (sigma - 1 / 2) ^ 2 + t ^ 2 := by
  unfold scaleA
  ring

theorem scaleB_centered (sigma t : ℝ) :
    scaleB sigma t = -2 * (sigma - 1 / 2) * t := by
  unfold scaleB
  ring

theorem scaleNorm_factorization (sigma t : ℝ) :
    scaleA sigma t ^ 2 + scaleB sigma t ^ 2 =
      (sigma ^ 2 + t ^ 2) * ((1 - sigma) ^ 2 + t ^ 2) := by
  unfold scaleA scaleB
  ring

theorem scaleNorm_pos_of_focus_nonzero (sigma t : ℝ)
    (h₀ : 0 < sigma ^ 2 + t ^ 2)
    (h₁ : 0 < (1 - sigma) ^ 2 + t ^ 2) :
    0 < scaleA sigma t ^ 2 + scaleB sigma t ^ 2 := by
  rw [scaleNorm_factorization]
  exact mul_pos h₀ h₁

theorem scaleNorm_eq_zero_iff_focus (sigma t : ℝ) :
    scaleA sigma t ^ 2 + scaleB sigma t ^ 2 = 0 ↔
      (sigma = 0 ∧ t = 0) ∨ (sigma = 1 ∧ t = 0) := by
  rw [scaleNorm_factorization]
  constructor
  · intro h
    rcases mul_eq_zero.mp h with h₀ | h₁
    · have hs : sigma = 0 := by nlinarith [sq_nonneg sigma, sq_nonneg t]
      have ht : t = 0 := by nlinarith [sq_nonneg sigma, sq_nonneg t]
      exact Or.inl ⟨hs, ht⟩
    · have hs : sigma = 1 := by nlinarith [sq_nonneg (1 - sigma), sq_nonneg t]
      have ht : t = 0 := by nlinarith [sq_nonneg (1 - sigma), sq_nonneg t]
      exact Or.inr ⟨hs, ht⟩
  · rintro (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)
    · norm_num
    · norm_num

theorem quarterTurn_sq (v : ℝ × ℝ) :
    quarterTurn (quarterTurn v) = (-v.1, -v.2) := by
  cases v
  rfl

theorem potential_unitary_orthogonal (sigma t : ℝ) :
    (dilationField sigma t).1 * (rotationalField sigma t).1 +
      (dilationField sigma t).2 * (rotationalField sigma t).2 = 0 := by
  unfold rotationalField quarterTurn dilationField
  ring

theorem unifiedField_eq_sum (gamma sigma t : ℝ) :
    unifiedField gamma sigma t =
      (gamma * (dilationField sigma t).1 + (rotationalField sigma t).1,
       gamma * (dilationField sigma t).2 + (rotationalField sigma t).2) := by
  unfold unifiedField rotationalField quarterTurn dilationField
  ext <;> simp [sub_eq_add_neg]

/-! ### Exact energy readout of the unified field -/

theorem unifiedField_normSq (gamma sigma t : ℝ) :
    (unifiedField gamma sigma t).1 ^ 2 + (unifiedField gamma sigma t).2 ^ 2 =
      (gamma ^ 2 + 1) *
        ((dilationField sigma t).1 ^ 2 + (dilationField sigma t).2 ^ 2) := by
  rw [unifiedField_eq_sum]
  unfold rotationalField quarterTurn
  ring

theorem unifiedField_normSq_eq_scaleNorm (gamma sigma t : ℝ) :
    (unifiedField gamma sigma t).1 ^ 2 + (unifiedField gamma sigma t).2 ^ 2 =
      (gamma ^ 2 + 1) * (scaleA sigma t ^ 2 + scaleB sigma t ^ 2) := by
  rw [unifiedField_normSq]
  unfold dilationField
  ring

theorem unifiedField_normSq_factorized (gamma sigma t : ℝ) :
    (unifiedField gamma sigma t).1 ^ 2 + (unifiedField gamma sigma t).2 ^ 2 =
      (gamma ^ 2 + 1) * (sigma ^ 2 + t ^ 2) *
        ((1 - sigma) ^ 2 + t ^ 2) := by
  rw [unifiedField_normSq_eq_scaleNorm, scaleNorm_factorization]
  ring_nf

theorem unifiedField_normSq_pos_of_focus_nonzero (gamma sigma t : ℝ)
    (h₀ : 0 < sigma ^ 2 + t ^ 2)
    (h₁ : 0 < (1 - sigma) ^ 2 + t ^ 2) :
    0 < (unifiedField gamma sigma t).1 ^ 2 +
        (unifiedField gamma sigma t).2 ^ 2 := by
  rw [unifiedField_normSq_factorized]
  positivity

theorem unifiedField_eq_zero_iff_focus (gamma sigma t : ℝ) :
    unifiedField gamma sigma t = (0, 0) ↔
      (sigma = 0 ∧ t = 0) ∨ (sigma = 1 ∧ t = 0) := by
  constructor
  · intro h
    have h_norm : (unifiedField gamma sigma t).1 ^ 2 +
        (unifiedField gamma sigma t).2 ^ 2 = 0 := by simp [h]
    rw [unifiedField_normSq_eq_scaleNorm] at h_norm
    have h_factor : gamma ^ 2 + 1 ≠ 0 := by positivity
    have h_scale : scaleA sigma t ^ 2 + scaleB sigma t ^ 2 = 0 := by
      rcases mul_eq_zero.mp h_norm with hzero | hzero
      · exact False.elim (h_factor hzero)
      · exact hzero
    exact (scaleNorm_eq_zero_iff_focus sigma t).mp h_scale
  · rintro (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)
    · simp [unifiedField, scaleA, scaleB]
    · simp [unifiedField, scaleA, scaleB]

theorem criticalLine_dilationField (t : ℝ) :
    dilationField (1 / 2) t = (-(1 / 4 + t ^ 2), 0) := by
  unfold dilationField scaleA scaleB
  norm_num

theorem criticalLine_rotationalField (t : ℝ) :
    rotationalField (1 / 2) t = (0, 1 / 4 + t ^ 2) := by
  unfold rotationalField quarterTurn
  rw [criticalLine_dilationField]
  norm_num

theorem criticalLine_unifiedField (gamma t : ℝ) :
    unifiedField gamma (1 / 2) t =
      (-gamma * (1 / 4 + t ^ 2), 1 / 4 + t ^ 2) := by
  rw [unifiedField_eq_sum, criticalLine_dilationField,
    criticalLine_rotationalField]
  simp
  ring

theorem criticalLine_unifiedField_ne_zero (gamma t : ℝ) :
    unifiedField gamma (1 / 2) t ≠ (0, 0) := by
  rw [criticalLine_unifiedField]
  intro h
  have h_second := congrArg Prod.snd h
  have h_pos : 0 < 1 / 4 + t ^ 2 := by positivity
  exact (ne_of_gt h_pos) (by simpa using h_second)

theorem criticalLine_unifiedField_normSq (gamma t : ℝ) :
    (unifiedField gamma (1 / 2) t).1 ^ 2 +
        (unifiedField gamma (1 / 2) t).2 ^ 2 =
      (gamma ^ 2 + 1) * (1 / 4 + t ^ 2) ^ 2 := by
  rw [unifiedField_normSq_eq_scaleNorm]
  unfold scaleA scaleB
  norm_num

theorem criticalLine_unifiedField_normSq_pos (gamma t : ℝ) :
    0 < (unifiedField gamma (1 / 2) t).1 ^ 2 +
        (unifiedField gamma (1 / 2) t).2 ^ 2 := by
  rw [criticalLine_unifiedField_normSq]
  positivity

end

end InfoGeometry.Canonical.ApolloniusMasterPotentialHelmholtz
