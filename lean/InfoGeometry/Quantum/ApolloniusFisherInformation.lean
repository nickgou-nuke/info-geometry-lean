import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Data.Complex.Basic
import Mathlib.Data.Matrix.Basic
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Topology.Order.Basic
import Mathlib.Tactic

namespace InfoGeometry.Quantum.ApolloniusFisherInformation

open Real Matrix

noncomputable section

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

/-- Local coordinates on the Apollonian statistical parameter space:
    $(\sigma, t)$ with the critical boundary avoided for regularity. -/
structure ApolloniusState where
  sigma : ℝ
  t : ℝ
  h_non_sing : 0 < (sigma - 1 / 2) ^ 2 + t ^ 2

/-- The $2 \times 2$ Fisher information metric matrix on Apollonius leaves:
    $g(\sigma, t) = \frac{1}{(\sigma - 1/2)^2 + t^2} I_2$. -/
def apolloniusFisherMatrix (st : ApolloniusState) : Matrix (Fin 2) (Fin 2) ℝ :=
  let scale := 1 / ((st.sigma - 1 / 2) ^ 2 + st.t ^ 2)
  !![scale, 0; 0, scale]

/-- Quadratic line element: $ds^2 = g(v, v) = \frac{v_\sigma^2 + v_t^2}{(\sigma - 1/2)^2 + t^2}$. -/
def apolloniusLineElement (st : ApolloniusState) (v_sigma v_t : ℝ) : ℝ :=
  (v_sigma ^ 2 + v_t ^ 2) / ((st.sigma - 1 / 2) ^ 2 + st.t ^ 2)

/-- Quadratic form of the Fisher metric on a tangent vector v: Fin 2 → ℝ. -/
def apolloniusFisherQuadraticForm (st : ApolloniusState) (v : Fin 2 → ℝ) : ℝ :=
  (v 0) * (apolloniusFisherMatrix st 0 0 * v 0) + (v 1) * (apolloniusFisherMatrix st 1 1 * v 1)

/-!
### 1. Matrix Representation and Strict Positive Definiteness
-/

/-- 🏆 THEOREM 1: Diagonal components of the Apollonius Fisher information metric. -/
theorem apollonius_fisher_components (st : ApolloniusState) :
    apolloniusFisherMatrix st 0 0 = 1 / ((st.sigma - 1 / 2) ^ 2 + st.t ^ 2) ∧
    apolloniusFisherMatrix st 1 1 = 1 / ((st.sigma - 1 / 2) ^ 2 + st.t ^ 2) ∧
    apolloniusFisherMatrix st 0 1 = 0 ∧
    apolloniusFisherMatrix st 1 0 = 0 := by
  unfold apolloniusFisherMatrix
  refine ⟨rfl, rfl, rfl, rfl⟩

/-- 🏆 THEOREM 2: Quadratic form evaluation matches the line element. -/
theorem apollonius_quadratic_form_eval (st : ApolloniusState) (v : Fin 2 → ℝ) :
    apolloniusFisherQuadraticForm st v = apolloniusLineElement st (v 0) (v 1) := by
  unfold apolloniusFisherQuadraticForm apolloniusFisherMatrix apolloniusLineElement
  dsimp
  ring

/-- 🏆 THEOREM 3: Strict positive definiteness of the metric tensor for non-zero vectors. -/
theorem apollonius_fisher_pos_def (st : ApolloniusState) (v : Fin 2 → ℝ) (hv : v ≠ 0) :
    0 < apolloniusFisherQuadraticForm st v := by
  rw [apollonius_quadratic_form_eval]
  unfold apolloniusLineElement
  have h_den_pos : 0 < (st.sigma - 1 / 2) ^ 2 + st.t ^ 2 := st.h_non_sing
  have h_num_pos : 0 < (v 0) ^ 2 + (v 1) ^ 2 := by
    have h_not_both_zero : v 0 ≠ 0 ∨ v 1 ≠ 0 := by
      by_contra h_all_zero
      push_neg at h_all_zero
      apply hv
      ext i
      fin_cases i <;> simp [h_all_zero.1, h_all_zero.2]
    cases h_not_both_zero with
    | inl h0 =>
      have : 0 < (v 0) ^ 2 := sq_pos_of_ne_zero h0
      have : 0 ≤ (v 1) ^ 2 := sq_nonneg (v 1)
      linarith
    | inr h1 =>
      have : 0 ≤ (v 0) ^ 2 := sq_nonneg (v 0)
      have : 0 < (v 1) ^ 2 := sq_pos_of_ne_zero h1
      linarith
  exact div_pos h_num_pos h_den_pos

/-!
### 2. Volume Form and Log-Determinant Potential
-/

/-- Determinant of the metric tensor: $\det g = \frac{1}{((\sigma - 1/2)^2 + t^2)^2}$. -/
theorem apollonius_fisher_det (st : ApolloniusState) :
    (apolloniusFisherMatrix st).det = 1 / ((st.sigma - 1 / 2) ^ 2 + st.t ^ 2) ^ 2 := by
  unfold apolloniusFisherMatrix
  rw [Matrix.det_fin_two]
  dsimp
  rw [mul_zero, sub_zero, ← sq, one_div_pow]

/-- Log-determinant curvature potential:
    $\Phi_g(\sigma, t) = \ln \det g(\sigma, t) = -2 \ln((\sigma - 1/2)^2 + t^2)$. -/
theorem apollonius_fisher_log_det (st : ApolloniusState) :
    Real.log (apolloniusFisherMatrix st).det = -2 * Real.log ((st.sigma - 1 / 2) ^ 2 + st.t ^ 2) := by
  rw [apollonius_fisher_det]
  have h_den_pos : 0 < (st.sigma - 1 / 2) ^ 2 + st.t ^ 2 := st.h_non_sing
  have h_den_sq_pos : 0 < ((st.sigma - 1 / 2) ^ 2 + st.t ^ 2) ^ 2 := sq_pos_of_ne_zero (ne_of_gt h_den_pos)
  rw [one_div, Real.log_inv, Real.log_pow ((st.sigma - 1 / 2) ^ 2 + st.t ^ 2) 2]
  push_cast
  ring

/-!
### 3. Critical Leaf Reduction ($\sigma = 1/2 \implies g(t) = 1/t^2 I_2$)
-/

/-- 🏆 THEOREM 4 (Poincaré Reduction on the Critical Line):
    Along the critical leaf $\sigma = 1/2$, the Apollonius Fisher metric
    collapses identically to the hyperbolic Poincaré Fisher metric $1/t^2 I_2$. -/
theorem apollonius_fisher_critical_line_reduction (t : ℝ) (ht : t ≠ 0) :
    let st : ApolloniusState := ⟨1 / 2, t, by
      have : (1 / 2 - 1 / 2 : ℝ) ^ 2 + t ^ 2 = t ^ 2 := by ring
      rw [this]
      exact sq_pos_of_ne_zero ht⟩
    apolloniusFisherMatrix st 0 0 = 1 / t ^ 2 ∧
    apolloniusFisherMatrix st 1 1 = 1 / t ^ 2 := by
  intro st
  unfold apolloniusFisherMatrix
  have : (st.sigma - 1 / 2) ^ 2 + st.t ^ 2 = t ^ 2 := by
    change (1 / 2 - 1 / 2 : ℝ) ^ 2 + t ^ 2 = t ^ 2
    ring
  dsimp
  rw [this]
  exact ⟨rfl, rfl⟩

/-!
### 4. Master Capstone Synthesis
-/

/-- 🏆 GRAND CAPSTONE: Synthesis of Apollonius Fisher Information,
    Strict Positive Definiteness, Log-Determinant Curvature, and Poincaré Reduction -/
theorem grand_apollonius_fisher_information_synthesis
    (st : ApolloniusState) (v : Fin 2 → ℝ) (hv : v ≠ 0)
    (t : ℝ) (ht : t ≠ 0) :
    (0 < apolloniusFisherQuadraticForm st v) ∧
    ((apolloniusFisherMatrix st).det = 1 / ((st.sigma - 1 / 2) ^ 2 + st.t ^ 2) ^ 2) ∧
    (Real.log (apolloniusFisherMatrix st).det = -2 * Real.log ((st.sigma - 1 / 2) ^ 2 + st.t ^ 2)) ∧
    (let st_crit : ApolloniusState := ⟨1 / 2, t, by
       have : (1 / 2 - 1 / 2 : ℝ) ^ 2 + t ^ 2 = t ^ 2 := by ring
       rw [this]
       exact sq_pos_of_ne_zero ht⟩
     apolloniusFisherMatrix st_crit 0 0 = 1 / t ^ 2) :=
  ⟨apollonius_fisher_pos_def st v hv,
   apollonius_fisher_det st,
   apollonius_fisher_log_det st,
   (apollonius_fisher_critical_line_reduction t ht).1⟩
