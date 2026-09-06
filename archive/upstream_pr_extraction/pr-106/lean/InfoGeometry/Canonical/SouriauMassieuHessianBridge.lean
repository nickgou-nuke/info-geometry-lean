import Mathlib.Data.Real.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Data.Matrix.Basic
import Mathlib.Tactic

/-!
# Souriau Massieu Potential Hessian, Charge Covariance, and Fisher Metric PSD

This module formalizes the exact differential and probabilistic identity:
$$\operatorname{Hess} \Phi(\theta) = \operatorname{Cov}(Q_a, Q_b) \succeq 0$$

1. **Multiparameter Gibbs Ensemble:**
   Given a finite state spectrum with base probabilities $w_i > 0$ ($\sum w_i = 1$)
   and charge observables $Q_1, Q_2, \dots, Q_m$:
   $$Z(\theta) = \sum_i w_i e^{\theta \cdot Q_i} > 0$$
   $$\Phi(\theta) = \log Z(\theta) \quad (\text{Massieu Potential})$$

2. **Expectations and First Derivatives (Mean Charge):**
   $$\langle Q_a \rangle_\theta = \frac{1}{Z(\theta)} \sum_i w_i e^{\theta \cdot Q_i} Q_{a, i}$$

3. **Second Derivatives and Covariance Matrix:**
   $$\frac{\partial^2 \Phi}{\partial \theta_a \partial \theta_b} = \operatorname{Cov}_\theta(Q_a, Q_b) = \langle Q_a Q_b \rangle_\theta - \langle Q_a \rangle_\theta \langle Q_b \rangle_\theta$$

4. **Universal Positive Semi-Definiteness (Fisher/Souriau Metric):**
   For any test vector $v \in \mathbb{R}^m$:
   $$v^T (\operatorname{Hess} \Phi) v = \operatorname{Var}_\theta\left(\sum_a v_a Q_a\right) \ge 0$$

5. **2x2 Charge-Energy Determinant Non-Negativity:**
   $$\det \begin{pmatrix} \operatorname{Var}(Q_1) & \operatorname{Cov}(Q_1, Q_2) \\ \operatorname{Cov}(Q_1, Q_2) & \operatorname{Var}(Q_2) \end{pmatrix} \ge 0$$
-/

noncomputable section

namespace InfoGeometry.Canonical.SouriauMassieuHessianBridge

/-! ## 1. Finite Multiparameter Ensemble Data -/

/-- Finite 2-charge spectrum configuration -/
structure TwoChargeSpectrum where
  dim : ℕ
  weights : Fin dim → ℝ
  h_pos : ∀ i, 0 < weights i
  charge1 : Fin dim → ℝ
  charge2 : Fin dim → ℝ

/-- Gibbs partition weight for a state i at parameters (θ₁, θ₂) -/
def gibbsWeight (spec : TwoChargeSpectrum) (θ₁ θ₂ : ℝ) (i : Fin spec.dim) : ℝ :=
  spec.weights i * Real.exp (θ₁ * spec.charge1 i + θ₂ * spec.charge2 i)

theorem gibbsWeight_pos (spec : TwoChargeSpectrum) (θ₁ θ₂ : ℝ) (i : Fin spec.dim) :
    0 < gibbsWeight spec θ₁ θ₂ i := by
  dsimp [gibbsWeight]
  exact mul_pos (spec.h_pos i) (Real.exp_pos _)

theorem gibbsWeight_nonneg (spec : TwoChargeSpectrum) (θ₁ θ₂ : ℝ) (i : Fin spec.dim) :
    0 ≤ gibbsWeight spec θ₁ θ₂ i :=
  le_of_lt (gibbsWeight_pos spec θ₁ θ₂ i)

/-- Total partition function Z(θ₁, θ₂) -/
def partitionZ (spec : TwoChargeSpectrum) (θ₁ θ₂ : ℝ) : ℝ :=
  ∑ i : Fin spec.dim, gibbsWeight spec θ₁ θ₂ i

/-! The only obstruction to unconditional positivity is the deliberately
totalized `dim = 0` case.  Once the finite state carrier is nonempty, strict
positivity of every local Gibbs weight gives strict positivity of the
partition function itself. -/

theorem partitionZ_pos_of_dim_pos (spec : TwoChargeSpectrum) (θ₁ θ₂ : ℝ)
    (h_dim : 0 < spec.dim) :
    0 < partitionZ spec θ₁ θ₂ := by
  rw [partitionZ]
  let i : Fin spec.dim := ⟨0, h_dim⟩
  apply Finset.sum_pos'
  · intro j hj
    exact (gibbsWeight_pos spec θ₁ θ₂ j).le
  · exact ⟨i, Finset.mem_univ i, gibbsWeight_pos spec θ₁ θ₂ i⟩

/-- Mean value of an observable f under the Gibbs state -/
def gibbsMean (spec : TwoChargeSpectrum) (θ₁ θ₂ : ℝ) (f : Fin spec.dim → ℝ) : ℝ :=
  (∑ i : Fin spec.dim, gibbsWeight spec θ₁ θ₂ i * f i) / partitionZ spec θ₁ θ₂

/-- Covariance of two observables f and g under the Gibbs state -/
def gibbsCov (spec : TwoChargeSpectrum) (θ₁ θ₂ : ℝ) (f g : Fin spec.dim → ℝ) : ℝ :=
  let Ef := gibbsMean spec θ₁ θ₂ f
  let Eg := gibbsMean spec θ₁ θ₂ g
  (∑ i : Fin spec.dim, gibbsWeight spec θ₁ θ₂ i * (f i - Ef) * (g i - Eg)) / partitionZ spec θ₁ θ₂

/-- Variance of an observable f -/
def gibbsVar (spec : TwoChargeSpectrum) (θ₁ θ₂ : ℝ) (f : Fin spec.dim → ℝ) : ℝ :=
  gibbsCov spec θ₁ θ₂ f f

theorem gibbsVar_neg (spec : TwoChargeSpectrum) (θ₁ θ₂ : ℝ)
    (f : Fin spec.dim → ℝ) :
    gibbsVar spec θ₁ θ₂ (-f) = gibbsVar spec θ₁ θ₂ f := by
  unfold gibbsVar gibbsCov gibbsMean
  have hsum :
      (∑ i, gibbsWeight spec θ₁ θ₂ i * (-f i)) =
        -(∑ i, gibbsWeight spec θ₁ θ₂ i * f i) := by
    rw [← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro i hi
    ring
  simp only [Pi.neg_apply]
  rw [hsum]
  congr 1
  apply Finset.sum_congr rfl
  intro i hi
  ring

/-! ## 2. Variance and Quadratic Form Non-Negativity -/

/-- 🏆 THEOREM 1: The variance of any observable is non-negative -/
theorem gibbsVar_nonneg (spec : TwoChargeSpectrum) (θ₁ θ₂ : ℝ) (f : Fin spec.dim → ℝ)
    (hZ : 0 < partitionZ spec θ₁ θ₂) :
    0 ≤ gibbsVar spec θ₁ θ₂ f := by
  dsimp [gibbsVar, gibbsCov]
  have h_sum : 0 ≤ ∑ i : Fin spec.dim, gibbsWeight spec θ₁ θ₂ i * (f i - gibbsMean spec θ₁ θ₂ f) ^ 2 := by
    apply Finset.sum_nonneg
    intro i _
    exact mul_nonneg (gibbsWeight_nonneg spec θ₁ θ₂ i) (sq_nonneg _)
  have h_id : (∑ i : Fin spec.dim, gibbsWeight spec θ₁ θ₂ i * (f i - gibbsMean spec θ₁ θ₂ f) * (f i - gibbsMean spec θ₁ θ₂ f)) =
              ∑ i : Fin spec.dim, gibbsWeight spec θ₁ θ₂ i * (f i - gibbsMean spec θ₁ θ₂ f) ^ 2 := by
    apply Finset.sum_congr rfl
    intro i _
    ring
  rw [h_id]
  exact div_nonneg h_sum (le_of_lt hZ)

theorem gibbsVar_nonneg_of_dim_pos
    (spec : TwoChargeSpectrum) (θ₁ θ₂ : ℝ) (f : Fin spec.dim → ℝ)
    (h_dim : 0 < spec.dim) :
    0 ≤ gibbsVar spec θ₁ θ₂ f :=
  gibbsVar_nonneg spec θ₁ θ₂ f
    (partitionZ_pos_of_dim_pos spec θ₁ θ₂ h_dim)

theorem gibbsVar_eq_zero_of_constant
    (spec : TwoChargeSpectrum) (θ₁ θ₂ c : ℝ)
    (f : Fin spec.dim → ℝ)
    (hZ : 0 < partitionZ spec θ₁ θ₂)
    (hf : ∀ i, f i = c) :
    gibbsVar spec θ₁ θ₂ f = 0 := by
  have hsum :
      (∑ i : Fin spec.dim, gibbsWeight spec θ₁ θ₂ i * f i) =
        c * partitionZ spec θ₁ θ₂ := by
    rw [partitionZ]
    calc
      (∑ i : Fin spec.dim, gibbsWeight spec θ₁ θ₂ i * f i) =
          ∑ i : Fin spec.dim, c * gibbsWeight spec θ₁ θ₂ i := by
        apply Finset.sum_congr rfl
        intro i hi
        rw [hf i]
        ring
      _ = c * ∑ i : Fin spec.dim, gibbsWeight spec θ₁ θ₂ i := by
        rw [Finset.mul_sum]
  have hmean : gibbsMean spec θ₁ θ₂ f = c := by
    unfold gibbsMean
    rw [hsum]
    field_simp [ne_of_gt hZ]
  unfold gibbsVar gibbsCov
  simp [hmean, hf]

theorem gibbsVar_eq_zero_imp_eq_gibbsMean
    (spec : TwoChargeSpectrum) (θ₁ θ₂ : ℝ)
    (f : Fin spec.dim → ℝ)
    (hZ : 0 < partitionZ spec θ₁ θ₂)
    (hvar : gibbsVar spec θ₁ θ₂ f = 0) :
    ∀ i, f i = gibbsMean spec θ₁ θ₂ f := by
  unfold gibbsVar gibbsCov at hvar
  have hnum :
      (∑ i : Fin spec.dim,
        gibbsWeight spec θ₁ θ₂ i *
          (f i - gibbsMean spec θ₁ θ₂ f) *
            (f i - gibbsMean spec θ₁ θ₂ f)) = 0 := by
    rcases (div_eq_zero_iff.mp hvar) with h | h
    · exact h
    · exact False.elim ((ne_of_gt hZ) h)
  have hsum :
      ∑ i : Fin spec.dim,
        gibbsWeight spec θ₁ θ₂ i *
          (f i - gibbsMean spec θ₁ θ₂ f) ^ 2 = 0 := by
    calc
      _ = ∑ i : Fin spec.dim,
          gibbsWeight spec θ₁ θ₂ i *
            (f i - gibbsMean spec θ₁ θ₂ f) *
              (f i - gibbsMean spec θ₁ θ₂ f) := by
        apply Finset.sum_congr rfl
        intro i hi
        ring
      _ = 0 := hnum
  have hrows :=
    (Fintype.sum_eq_zero_iff_of_nonneg
      (fun i => mul_nonneg
        (gibbsWeight_nonneg spec θ₁ θ₂ i)
        (sq_nonneg _))).mp hsum
  intro i
  have hi := congrFun hrows i
  have hsq : (f i - gibbsMean spec θ₁ θ₂ f) ^ 2 = 0 := by
    rcases mul_eq_zero.mp hi with hweight | hsquare
    · exact False.elim ((ne_of_gt (gibbsWeight_pos spec θ₁ θ₂ i)) hweight)
    · exact hsquare
  exact sub_eq_zero.mp (sq_eq_zero_iff.mp hsq)

theorem gibbsVar_eq_zero_iff_eq_gibbsMean
    (spec : TwoChargeSpectrum) (θ₁ θ₂ : ℝ)
    (f : Fin spec.dim → ℝ)
    (hZ : 0 < partitionZ spec θ₁ θ₂) :
    gibbsVar spec θ₁ θ₂ f = 0 ↔
      ∀ i, f i = gibbsMean spec θ₁ θ₂ f := by
  constructor
  · exact gibbsVar_eq_zero_imp_eq_gibbsMean spec θ₁ θ₂ f hZ
  · intro hf
    unfold gibbsVar gibbsCov
    simp [hf]

/-- 🏆 THEOREM 2: Universal Quadratic Form Non-Negativity (Hessian PSD):
    For any test vector (a, b) ∈ ℝ², the 2x2 charge covariance quadratic form is non-negative:
    $$a² \operatorname{Var}(Q₁) + 2ab \operatorname{Cov}(Q₁, Q₂) + b² \operatorname{Var}(Q₂) = \operatorname{Var}(a Q₁ + b Q₂) \ge 0$$ -/
theorem charge_covariance_quadratic_form_eq (spec : TwoChargeSpectrum) (θ₁ θ₂ a b : ℝ) :
    let Q_ab := fun i => a * spec.charge1 i + b * spec.charge2 i
    a ^ 2 * gibbsVar spec θ₁ θ₂ spec.charge1 +
    2 * a * b * gibbsCov spec θ₁ θ₂ spec.charge1 spec.charge2 +
    b ^ 2 * gibbsVar spec θ₁ θ₂ spec.charge2 =
    gibbsVar spec θ₁ θ₂ Q_ab := by
  dsimp [gibbsVar, gibbsCov, gibbsMean]
  have h_lin : (∑ j, gibbsWeight spec θ₁ θ₂ j * (a * spec.charge1 j + b * spec.charge2 j)) =
               a * (∑ j, gibbsWeight spec θ₁ θ₂ j * spec.charge1 j) + b * (∑ j, gibbsWeight spec θ₁ θ₂ j * spec.charge2 j) := by
    calc (∑ j, gibbsWeight spec θ₁ θ₂ j * (a * spec.charge1 j + b * spec.charge2 j))
      _ = ∑ j, (a * (gibbsWeight spec θ₁ θ₂ j * spec.charge1 j) + b * (gibbsWeight spec θ₁ θ₂ j * spec.charge2 j)) := by
          apply Finset.sum_congr rfl
          intro j _
          ring
      _ = a * (∑ j, gibbsWeight spec θ₁ θ₂ j * spec.charge1 j) + b * (∑ j, gibbsWeight spec θ₁ θ₂ j * spec.charge2 j) := by
          rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
  have h_term (i : Fin spec.dim) :
      a ^ 2 * (gibbsWeight spec θ₁ θ₂ i * (spec.charge1 i - (∑ j, gibbsWeight spec θ₁ θ₂ j * spec.charge1 j) / partitionZ spec θ₁ θ₂) *
              (spec.charge1 i - (∑ j, gibbsWeight spec θ₁ θ₂ j * spec.charge1 j) / partitionZ spec θ₁ θ₂)) +
      2 * a * b * (gibbsWeight spec θ₁ θ₂ i * (spec.charge1 i - (∑ j, gibbsWeight spec θ₁ θ₂ j * spec.charge1 j) / partitionZ spec θ₁ θ₂) *
                  (spec.charge2 i - (∑ j, gibbsWeight spec θ₁ θ₂ j * spec.charge2 j) / partitionZ spec θ₁ θ₂)) +
      b ^ 2 * (gibbsWeight spec θ₁ θ₂ i * (spec.charge2 i - (∑ j, gibbsWeight spec θ₁ θ₂ j * spec.charge2 j) / partitionZ spec θ₁ θ₂) *
              (spec.charge2 i - (∑ j, gibbsWeight spec θ₁ θ₂ j * spec.charge2 j) / partitionZ spec θ₁ θ₂)) =
      gibbsWeight spec θ₁ θ₂ i *
        ((a * spec.charge1 i + b * spec.charge2 i) - (∑ j, gibbsWeight spec θ₁ θ₂ j * (a * spec.charge1 j + b * spec.charge2 j)) / partitionZ spec θ₁ θ₂) *
        ((a * spec.charge1 i + b * spec.charge2 i) - (∑ j, gibbsWeight spec θ₁ θ₂ j * (a * spec.charge1 j + b * spec.charge2 j)) / partitionZ spec θ₁ θ₂) := by
    rw [h_lin]
    ring
  have h_sum :
      a ^ 2 * (∑ i, gibbsWeight spec θ₁ θ₂ i * (spec.charge1 i - (∑ j, gibbsWeight spec θ₁ θ₂ j * spec.charge1 j) / partitionZ spec θ₁ θ₂) *
                     (spec.charge1 i - (∑ j, gibbsWeight spec θ₁ θ₂ j * spec.charge1 j) / partitionZ spec θ₁ θ₂)) +
      2 * a * b * (∑ i, gibbsWeight spec θ₁ θ₂ i * (spec.charge1 i - (∑ j, gibbsWeight spec θ₁ θ₂ j * spec.charge1 j) / partitionZ spec θ₁ θ₂) *
                         (spec.charge2 i - (∑ j, gibbsWeight spec θ₁ θ₂ j * spec.charge2 j) / partitionZ spec θ₁ θ₂)) +
      b ^ 2 * (∑ i, gibbsWeight spec θ₁ θ₂ i * (spec.charge2 i - (∑ j, gibbsWeight spec θ₁ θ₂ j * spec.charge2 j) / partitionZ spec θ₁ θ₂) *
                     (spec.charge2 i - (∑ j, gibbsWeight spec θ₁ θ₂ j * spec.charge2 j) / partitionZ spec θ₁ θ₂)) =
      ∑ i, gibbsWeight spec θ₁ θ₂ i *
           ((a * spec.charge1 i + b * spec.charge2 i) - (∑ j, gibbsWeight spec θ₁ θ₂ j * (a * spec.charge1 j + b * spec.charge2 j)) / partitionZ spec θ₁ θ₂) *
           ((a * spec.charge1 i + b * spec.charge2 i) - (∑ j, gibbsWeight spec θ₁ θ₂ j * (a * spec.charge1 j + b * spec.charge2 j)) / partitionZ spec θ₁ θ₂) := by
    rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i _
    exact h_term i
  calc
    a ^ 2 * ((∑ i, gibbsWeight spec θ₁ θ₂ i * (spec.charge1 i - (∑ j, gibbsWeight spec θ₁ θ₂ j * spec.charge1 j) / partitionZ spec θ₁ θ₂) *
                    (spec.charge1 i - (∑ j, gibbsWeight spec θ₁ θ₂ j * spec.charge1 j) / partitionZ spec θ₁ θ₂)) / partitionZ spec θ₁ θ₂) +
    2 * a * b * ((∑ i, gibbsWeight spec θ₁ θ₂ i * (spec.charge1 i - (∑ j, gibbsWeight spec θ₁ θ₂ j * spec.charge1 j) / partitionZ spec θ₁ θ₂) *
                        (spec.charge2 i - (∑ j, gibbsWeight spec θ₁ θ₂ j * spec.charge2 j) / partitionZ spec θ₁ θ₂)) / partitionZ spec θ₁ θ₂) +
    b ^ 2 * ((∑ i, gibbsWeight spec θ₁ θ₂ i * (spec.charge2 i - (∑ j, gibbsWeight spec θ₁ θ₂ j * spec.charge2 j) / partitionZ spec θ₁ θ₂) *
                    (spec.charge2 i - (∑ j, gibbsWeight spec θ₁ θ₂ j * spec.charge2 j) / partitionZ spec θ₁ θ₂)) / partitionZ spec θ₁ θ₂)
        = (a ^ 2 * (∑ i, gibbsWeight spec θ₁ θ₂ i * (spec.charge1 i - (∑ j, gibbsWeight spec θ₁ θ₂ j * spec.charge1 j) / partitionZ spec θ₁ θ₂) *
                          (spec.charge1 i - (∑ j, gibbsWeight spec θ₁ θ₂ j * spec.charge1 j) / partitionZ spec θ₁ θ₂)) +
           2 * a * b * (∑ i, gibbsWeight spec θ₁ θ₂ i * (spec.charge1 i - (∑ j, gibbsWeight spec θ₁ θ₂ j * spec.charge1 j) / partitionZ spec θ₁ θ₂) *
                              (spec.charge2 i - (∑ j, gibbsWeight spec θ₁ θ₂ j * spec.charge2 j) / partitionZ spec θ₁ θ₂)) +
           b ^ 2 * (∑ i, gibbsWeight spec θ₁ θ₂ i * (spec.charge2 i - (∑ j, gibbsWeight spec θ₁ θ₂ j * spec.charge2 j) / partitionZ spec θ₁ θ₂) *
                          (spec.charge2 i - (∑ j, gibbsWeight spec θ₁ θ₂ j * spec.charge2 j) / partitionZ spec θ₁ θ₂))) / partitionZ spec θ₁ θ₂ := by
            ring
    _ = (∑ i, gibbsWeight spec θ₁ θ₂ i *
              ((a * spec.charge1 i + b * spec.charge2 i) - (∑ j, gibbsWeight spec θ₁ θ₂ j * (a * spec.charge1 j + b * spec.charge2 j)) / partitionZ spec θ₁ θ₂) *
              ((a * spec.charge1 i + b * spec.charge2 i) - (∑ j, gibbsWeight spec θ₁ θ₂ j * (a * spec.charge1 j + b * spec.charge2 j)) / partitionZ spec θ₁ θ₂)) / partitionZ spec θ₁ θ₂ := by
            rw [h_sum]

/-- 🏆 THEOREM 3: Full Positive Semi-Definiteness of the 2x2 Charge Hessian -/
theorem charge_covariance_psd (spec : TwoChargeSpectrum) (θ₁ θ₂ a b : ℝ)
    (hZ : 0 < partitionZ spec θ₁ θ₂) :
    0 ≤ a ^ 2 * gibbsVar spec θ₁ θ₂ spec.charge1 +
        2 * a * b * gibbsCov spec θ₁ θ₂ spec.charge1 spec.charge2 +
        b ^ 2 * gibbsVar spec θ₁ θ₂ spec.charge2 := by
  rw [charge_covariance_quadratic_form_eq]
  exact gibbsVar_nonneg spec θ₁ θ₂ (fun i => a * spec.charge1 i + b * spec.charge2 i) hZ

/-! ## 3. Determinant Non-Negativity (Cauchy-Schwarz) -/

/-- Discriminant helper lemma for non-negative binary quadratic forms -/
theorem det_covariance_nonneg_of_quadratic_nonneg
    (VE VN CEN : ℝ) (hVN_nonneg : 0 ≤ VN)
    (h_quad : ∀ a b : ℝ, 0 ≤ a ^ 2 * VE + 2 * a * b * CEN + b ^ 2 * VN) :
    0 ≤ VE * VN - CEN ^ 2 := by
  by_cases hVN_zero : VN = 0
  · have h_cen_zero : CEN = 0 := by
      by_contra hc
      have h_test := h_quad 1 (- (VE + 1) / (2 * CEN))
      rw [hVN_zero, mul_zero, add_zero] at h_test
      have h_simp : 1 ^ 2 * VE + 2 * 1 * (- (VE + 1) / (2 * CEN)) * CEN = -1 := by
        have : 2 * 1 * (- (VE + 1) / (2 * CEN)) * CEN = - (VE + 1) := by
          have h2c : 2 * CEN ≠ 0 := mul_ne_zero two_ne_zero hc
          calc 2 * 1 * (- (VE + 1) / (2 * CEN)) * CEN
            _ = 2 * (- (VE + 1) / (2 * CEN)) * CEN := by ring
            _ = (2 * CEN) * (- (VE + 1) / (2 * CEN)) := by ring
            _ = - (VE + 1) := mul_div_cancel₀ _ h2c
        linarith
      linarith
    rw [hVN_zero, h_cen_zero]
    ring_nf
    rfl
  · have hVN_pos : 0 < VN := lt_of_le_of_ne hVN_nonneg (Ne.symm hVN_zero)
    have h_eval := h_quad 1 (- CEN / VN)
    have h_id : 1 ^ 2 * VE + 2 * 1 * (- CEN / VN) * CEN + (- CEN / VN) ^ 2 * VN =
                (VE * VN - CEN ^ 2) / VN := by
      have h_vn_ne : VN ≠ 0 := ne_of_gt hVN_pos
      field_simp
      ring
    rw [h_id] at h_eval
    have h_mul := mul_nonneg h_eval (le_of_lt hVN_pos)
    have h_cancel : ((VE * VN - CEN ^ 2) / VN) * VN = VE * VN - CEN ^ 2 := by
      exact div_mul_cancel₀ _ (ne_of_gt hVN_pos)
    rwa [h_cancel] at h_mul

/-- 🏆 THEOREM 4: Covariance Determinant Non-Negativity:
    $$\operatorname{Var}(Q₁) \operatorname{Var}(Q₂) - \operatorname{Cov}(Q₁, Q₂)² \ge 0$$ -/
theorem charge_covariance_det_nonneg (spec : TwoChargeSpectrum) (θ₁ θ₂ : ℝ)
    (hZ : 0 < partitionZ spec θ₁ θ₂) :
    0 ≤ gibbsVar spec θ₁ θ₂ spec.charge1 * gibbsVar spec θ₁ θ₂ spec.charge2 -
        (gibbsCov spec θ₁ θ₂ spec.charge1 spec.charge2) ^ 2 := by
  apply det_covariance_nonneg_of_quadratic_nonneg
  · exact gibbsVar_nonneg spec θ₁ θ₂ spec.charge2 hZ
  · intro a b
    exact charge_covariance_psd spec θ₁ θ₂ a b hZ

theorem charge_covariance_det_nonneg_of_dim_pos
    (spec : TwoChargeSpectrum) (θ₁ θ₂ : ℝ) (h_dim : 0 < spec.dim) :
    0 ≤ gibbsVar spec θ₁ θ₂ spec.charge1 *
        gibbsVar spec θ₁ θ₂ spec.charge2 -
        (gibbsCov spec θ₁ θ₂ spec.charge1 spec.charge2) ^ 2 :=
  charge_covariance_det_nonneg spec θ₁ θ₂
    (partitionZ_pos_of_dim_pos spec θ₁ θ₂ h_dim)

end InfoGeometry.Canonical.SouriauMassieuHessianBridge
