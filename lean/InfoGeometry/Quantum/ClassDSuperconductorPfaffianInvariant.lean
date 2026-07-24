import Mathlib
import InfoGeometry.Quantum.MajoranaPfaffianNaturalClosure

open InfoGeometry.MajoranaPfaffianNaturalClosure

namespace InfoGeometry.Quantum.ClassDSuperconductorPfaffianInvariant

/-- Particle-Hole Operator Matrix C = τ_x = (0 1; 1 0) -/
def PHS_C : M2R :=
  !![0, 1; 1, 0]

theorem PHS_C_sq : PHS_C * PHS_C = (1 : M2R) := splitPos_sq

/-- 1D Class-D BdG Hamiltonian at momentum k for toy model parameters (μ, t, Δ_k) -/
def H_BdG_1D (xi Delta : ℝ) : M2R :=
  !![xi, Delta; Delta, -xi]

/-- High-Symmetry Momentum Points k = 0 and k = π where Δ(0) = Δ(π) = 0 -/
def H_BdG_high_symm (xi : ℝ) : M2R :=
  H_BdG_1D xi 0

theorem H_BdG_high_symm_explicit (xi : ℝ) :
    H_BdG_high_symm xi = !![xi, 0; 0, -xi] := by
  dsimp [H_BdG_high_symm, H_BdG_1D]

/-- Particle-Hole Symmetry Relation at High-Symmetry Points: C H(k) C⁻¹ = -H(k) when Δ(k) = 0 -/
theorem PHS_high_symm (xi : ℝ) :
    PHS_C * H_BdG_high_symm xi * PHS_C = -H_BdG_high_symm xi := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [PHS_C, H_BdG_high_symm, H_BdG_1D, Matrix.mul_apply, Fin.sum_univ_two]

/-- Skew-Symmetric Majorana Basis Matrix A(k) = (0 xi; -xi 0) at high-symmetry points -/
def A_Majorana_high_symm (xi : ℝ) : M2R :=
  bdg2 xi

theorem A_Majorana_high_symm_skew (xi : ℝ) :
    Matrix.transpose (A_Majorana_high_symm xi) = -A_Majorana_high_symm xi := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [A_Majorana_high_symm, bdg2, Matrix.transpose_apply]

/-- Pfaffian of the high-symmetry Majorana matrix A(k) -/
def pfaffian_high_symm (xi : ℝ) : ℝ :=
  pfaffian2 xi

theorem det_A_eq_pfaffian_sq (xi : ℝ) :
    (A_Majorana_high_symm xi).det = (pfaffian_high_symm xi)^2 := by
  dsimp [A_Majorana_high_symm, pfaffian_high_symm]
  exact det_bdg2 xi

theorem det_H_high_symm (xi : ℝ) :
    (H_BdG_high_symm xi).det = -(xi^2) := by
  dsimp [H_BdG_high_symm, H_BdG_1D]
  simp [Matrix.det_fin_two]
  ring

/-- Bulk Gap Condition: H(k) is gapped (det H(k) ≠ 0) iff xi ≠ 0 -/
theorem bulk_gap_iff (xi : ℝ) :
    (H_BdG_high_symm xi).det ≠ 0 ↔ xi ≠ 0 := by
  rw [det_H_high_symm]
  constructor
  · intro h hz
    subst hz
    norm_num at h
  · intro h hz
    have : xi^2 = 0 := by linarith
    exact h (sq_eq_zero_iff.mp this)

/-- Kitaev ℤ₂ Topological Pfaffian Invariant Product ν = Pf A(0) * Pf A(π) = (μ + t)(μ - t) = μ² - t² -/
def kitaevPfaffianProduct (mu t : ℝ) : ℝ :=
  (pfaffian_high_symm (mu + t)) * (pfaffian_high_symm (mu - t))

theorem kitaev_pfaffian_product_eq (mu t : ℝ) :
    kitaevPfaffianProduct mu t = mu^2 - t^2 := by
  dsimp [kitaevPfaffianProduct, pfaffian_high_symm, pfaffian2]
  ring

/-- Topological Phase Criterion: When |μ| < |t|, the Pfaffian product is strictly negative (ν < 0) -/
theorem topological_phase_pfaffian_neg (mu t : ℝ) (h : mu^2 < t^2) :
    kitaevPfaffianProduct mu t < 0 := by
  rw [kitaev_pfaffian_product_eq]
  linarith

/-- Trivial Phase Criterion: When |μ| > |t|, the Pfaffian product is strictly positive (ν > 0) -/
theorem trivial_phase_pfaffian_pos (mu t : ℝ) (h : t^2 < mu^2) :
    kitaevPfaffianProduct mu t > 0 := by
  rw [kitaev_pfaffian_product_eq]
  linarith

/-- Bulk Gap Closing at Phase Transition: When |μ| = |t|, the gap closes at k = 0 or k = π -/
theorem gap_closing_at_transition (mu t : ℝ) (h : mu^2 = t^2) :
    (H_BdG_high_symm (mu + t)).det = 0 ∨ (H_BdG_high_symm (mu - t)).det = 0 := by
  have h_diff : (mu + t) * (mu - t) = 0 := by linarith
  cases mul_eq_zero.mp h_diff with
  | inl h1 =>
    left
    rw [det_H_high_symm, h1]
    ring
  | inr h2 =>
    right
    rw [det_H_high_symm, h2]
    ring

/-- Certified Native Mathlib Class-D Topological Phase Structure -/
structure ClassDTopologicalPhasePacket where
  mu : ℝ
  t : ℝ
  h_topological : mu^2 < t^2
  pfaffianProduct : ℝ
  h_pfaffian_eq : pfaffianProduct = mu^2 - t^2
  h_pfaffian_neg : pfaffianProduct < 0
  bulkGapZero : (H_BdG_high_symm (mu + t)).det ≠ 0
  bulkGapPi : (H_BdG_high_symm (mu - t)).det ≠ 0

theorem class_D_topological_phase_exists :
    Nonempty ClassDTopologicalPhasePacket := by
  refine ⟨⟨0, 1, by norm_num, -1, by norm_num, by norm_num, ?_, ?_⟩⟩
  · rw [det_H_high_symm]; norm_num
  · rw [det_H_high_symm]; norm_num

end InfoGeometry.Quantum.ClassDSuperconductorPfaffianInvariant
