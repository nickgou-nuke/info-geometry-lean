import Mathlib.Tactic
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
  twoMajoranaCoupling xi

theorem A_Majorana_high_symm_skew (xi : ℝ) :
    Matrix.transpose (A_Majorana_high_symm xi) = -A_Majorana_high_symm xi := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [A_Majorana_high_symm, twoMajoranaCoupling, Matrix.transpose_apply]

/-- Pfaffian of the high-symmetry Majorana matrix A(k) -/
def pfaffian_high_symm (xi : ℝ) : ℝ :=
  twoMajoranaPfaffian xi

theorem det_A_eq_pfaffian_sq (xi : ℝ) :
    (A_Majorana_high_symm xi).det = (pfaffian_high_symm xi)^2 := by
  dsimp [A_Majorana_high_symm, pfaffian_high_symm]
  exact det_twoMajoranaCoupling xi

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

/-- At a particle-hole invariant momentum, the explicit Pfaffian is nonzero
exactly when the corresponding finite Hamiltonian is gapped. -/
theorem pfaffian_high_symm_ne_zero_iff_bulk_gap (xi : ℝ) :
    pfaffian_high_symm xi ≠ 0 ↔ (H_BdG_high_symm xi).det ≠ 0 := by
  rw [bulk_gap_iff]
  rfl

/-- Bulk gaps at both particle-hole invariant momenta force both explicit
Pfaffians to be nonzero. -/
theorem highSymmetryPfaffians_nonzero_of_bulk_gaps
    (mu t : ℝ)
    (hzero : (H_BdG_high_symm (mu + t)).det ≠ 0)
    (hpi : (H_BdG_high_symm (mu - t)).det ≠ 0) :
    pfaffian_high_symm (mu + t) ≠ 0 ∧
      pfaffian_high_symm (mu - t) ≠ 0 := by
  exact ⟨(pfaffian_high_symm_ne_zero_iff_bulk_gap _).2 hzero,
    (pfaffian_high_symm_ne_zero_iff_bulk_gap _).2 hpi⟩

/-- Kitaev ℤ₂ Topological Pfaffian Invariant Product ν = Pf A(0) * Pf A(π) = (μ + t)(μ - t) = μ² - t² -/
def kitaevPfaffianProduct (mu t : ℝ) : ℝ :=
  (pfaffian_high_symm (mu + t)) * (pfaffian_high_symm (mu - t))

/-- Under both finite bulk-gap hypotheses, the explicit Pfaffian product cannot
vanish. -/
theorem kitaevPfaffianProduct_ne_zero_of_bulk_gaps
    (mu t : ℝ)
    (hzero : (H_BdG_high_symm (mu + t)).det ≠ 0)
    (hpi : (H_BdG_high_symm (mu - t)).det ≠ 0) :
    kitaevPfaffianProduct mu t ≠ 0 := by
  rcases highSymmetryPfaffians_nonzero_of_bulk_gaps mu t hzero hpi with ⟨h0, hπ⟩
  exact mul_ne_zero h0 hπ

theorem kitaev_pfaffian_product_eq (mu t : ℝ) :
    kitaevPfaffianProduct mu t = mu^2 - t^2 := by
  dsimp [kitaevPfaffianProduct, pfaffian_high_symm, twoMajoranaPfaffian]
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

/--
Finite Class-D parameters in the topological regime.

The Pfaffian product, its sign, and both high-symmetry bulk gaps are derived
below; they are not stored as independent evidence.
-/
abbrev FiniteClassDParameters : Type :=
  Σ' mu : ℝ, Σ' t : ℝ, mu^2 < t^2

namespace FiniteClassDParameters

variable (W : FiniteClassDParameters)

abbrev mu : ℝ := W.1

abbrev t : ℝ := W.2.1

abbrev h_topological : W.mu^2 < W.t^2 := W.2.2

/-- The property's Pfaffian product is the canonical finite Kitaev product. -/
def pfaffianProduct : ℝ :=
  kitaevPfaffianProduct W.mu W.t

/-- The canonical product is the difference of squares. -/
theorem h_pfaffian_eq :
    W.pfaffianProduct = W.mu^2 - W.t^2 :=
  kitaev_pfaffian_product_eq W.mu W.t

/-- Topological parameters force a negative Pfaffian product. -/
theorem h_pfaffian_neg : W.pfaffianProduct < 0 :=
  topological_phase_pfaffian_neg W.mu W.t W.h_topological

/-- The `k = 0` finite Hamiltonian is gapped in the strict topological regime. -/
theorem bulkGapZero :
    (H_BdG_high_symm (W.mu + W.t)).det ≠ 0 := by
  rw [bulk_gap_iff]
  intro hzero
  have hmu : W.mu = -W.t := by
    linarith
  have hsquares : W.mu^2 = W.t^2 := by
    calc
      W.mu^2 = (-W.t)^2 := congrArg (fun x : ℝ => x^2) hmu
      _ = W.t^2 := by ring
  exact (ne_of_lt W.h_topological) hsquares

/-- The `k = π` finite Hamiltonian is gapped in the strict topological regime. -/
theorem bulkGapPi :
    (H_BdG_high_symm (W.mu - W.t)).det ≠ 0 := by
  rw [bulk_gap_iff]
  intro hpi
  have hmu : W.mu = W.t := by
    linarith
  have hsquares : W.mu^2 = W.t^2 := by
    exact congrArg (fun x : ℝ => x^2) hmu
  exact (ne_of_lt W.h_topological) hsquares

end FiniteClassDParameters

theorem finiteClassDPfaffianWitness_exists :
    Nonempty FiniteClassDParameters := by
  exact ⟨⟨0, 1, by norm_num⟩⟩

end InfoGeometry.Quantum.ClassDSuperconductorPfaffianInvariant
