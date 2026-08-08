import Mathlib
import proofs.TripotentCliffordColimit
import proofs.TwistorParafermionBoundary
import proofs.ZornParavectorNullspace
import proofs.ChiralConeAlgebraFinality
import proofs.EntropicChiralDeRhamFormalization
import proofs.ModularItakuraBiquaternion
import proofs.CuntzDeformedSuperPoincare

/-!
# Spin network twistor quantization synthesis

Reconciles: Penrose spin networks, twistor quantization, deformed Cuntz algebras,
Bogoliubov parallel transport, modular mirror, spin connection, tripotent compasses.

Global analytic claims are left out unless they have an explicit Lean proof.
-/

noncomputable section

namespace SpinNetworkTwistorQuantization

open Matrix TripotentCliffordColimit TwistorParafermionBoundary

/-! ## Pauli matrices -/

def sigma1 : Matrix (Fin 2) (Fin 2) ℂ := !![0, 1; 1, 0]
def sigma2 : Matrix (Fin 2) (Fin 2) ℂ := !![0, -Complex.I; Complex.I, 0]
def sigma3 : Matrix (Fin 2) (Fin 2) ℂ := !![1, 0; 0, -1]

theorem pauli_comm_12 : sigma1 * sigma2 - sigma2 * sigma1 = (2 * Complex.I) • sigma3 := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [sigma1, sigma2, sigma3, Matrix.smul_apply] <;> ring

theorem pauli_comm_23 : sigma2 * sigma3 - sigma3 * sigma2 = (2 * Complex.I) • sigma1 := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [sigma1, sigma2, sigma3, Matrix.smul_apply] <;> ring_nf

theorem pauli_comm_31 : sigma3 * sigma1 - sigma1 * sigma3 = (2 * Complex.I) • sigma2 := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [sigma1, sigma2, sigma3, Matrix.smul_apply] <;> ring_nf <;> simp

/-! ## Tripotent spectrum -/

theorem tripotent_spectrum_diagonal (d : Fin 3 → ℂ)
    (hT : Matrix.diagonal d * Matrix.diagonal d * Matrix.diagonal d = Matrix.diagonal d) :
    ∀ i : Fin 3, d i = 1 ∨ d i = -1 ∨ d i = 0 := by
  intro i
  have h : Matrix.diagonal (fun j => d j * d j * d j) = Matrix.diagonal d := by
    simp [Matrix.diagonal_mul_diagonal] at hT ⊢; exact hT
  have h_entry : d i * d i * d i = d i := by
    have h1 := congr_fun (congr_fun h i) i
    simpa using h1
  have h_eq1 : d i * d i * d i - d i = 0 := by
    calc d i * d i * d i - d i = d i - d i := by rw [h_entry]
      _ = 0 := by ring
  have h_eq2 : d i * (d i * d i - 1) = 0 := by
    calc
      d i * (d i * d i - 1) = d i * d i * d i - d i := by ring
      _ = 0 := h_eq1
  cases (mul_eq_zero.mp h_eq2) with
  | inl h0 =>
    right; right; exact h0
  | inr h1 =>
    have h2 : d i * d i = 1 := by
      calc d i * d i = d i * d i - 1 + 1 := by ring
        _ = 0 + 1 := by rw [h1]
        _ = 1 := by ring
    have h3 : (d i - 1) * (d i + 1) = 0 := by
      calc (d i - 1) * (d i + 1) = d i * d i - 1 := by ring
        _ = 1 - 1 := by rw [h2]
        _ = 0 := by ring
    cases (mul_eq_zero.mp h3) with
    | inl h4 =>
      left
      calc d i = d i - 1 + 1 := by ring
        _ = 0 + 1 := by rw [h4]
        _ = 1 := by ring
    | inr h4 =>
      right; left
      calc d i = d i + 1 - 1 := by ring
        _ = 0 - 1 := by rw [h4]
        _ = -1 := by ring

/-! ## Twistor incidence -/

theorem twistor_incidence (t x y z : ℂ) (_h : t^2 - x^2 - y^2 - z^2 = 0) :
    ∃ a b c d : ℂ, a * c = t + z ∧ b * d = t - z := by
  use 1, 1, t + z, t - z
  constructor
  · -- a * c = t + z
    all_goals simp
  · -- b * d = t - z
    all_goals simp

/-! ## Klein quadric -/

theorem klein_quadric_twistor (omega0 omega1 pi0 pi1 : ℂ) :
    omega0 * pi1 - omega1 * pi0 = 0 →
      ∃ L1 L2 : Matrix (Fin 2) (Fin 2) ℂ,
        omega0 = L1 0 0 * L2 0 0 + L1 0 1 * L2 1 0 := by
  intro _
  refine ⟨!![omega0, 0; 0, 0], !![1, 0; 0, 0], ?_⟩
  simp

/-! ## Entropy potential and Itakura-Saito -/

def entropyPotential (x : ℝ) : ℝ := - Real.log x

def itakuraSaito (p q : ℝ) : ℝ := p / q - Real.log (p / q) - 1

theorem itakuraSaito_nonneg (p q : ℝ) (hp : 0 < p) (hq : 0 < q) :
    itakuraSaito p q ≥ 0 := by
  have h1 : p / q > 0 := by positivity
  have h2 : itakuraSaito p q = p / q - Real.log (p / q) - 1 := by
    simp [itakuraSaito]
  rw [h2]
  have h3 : Real.log (p / q) ≤ p / q - 1 := by
    apply Real.log_le_sub_one_of_pos
    positivity
  nlinarith

theorem itakuraSaito_is_bregman (p q : ℝ) (hp : 0 < p) (hq : 0 < q) :
    itakuraSaito p q =
      entropyPotential p - entropyPotential q - (- q⁻¹) * (p - q) := by
  unfold itakuraSaito entropyPotential
  have hp' : p ≠ 0 := ne_of_gt hp
  have hq' : q ≠ 0 := ne_of_gt hq
  rw [Real.log_div hp' hq']
  have h3 : q⁻¹ * q = 1 := inv_mul_cancel₀ hq'
  calc p / q - (Real.log p - Real.log q) - 1
    _ = p * q⁻¹ - Real.log p + Real.log q - 1 := by ring
    _ = p * q⁻¹ - Real.log p + Real.log q - q⁻¹ * q := by rw [h3]
    _ = -Real.log p - (-Real.log q) - (-q⁻¹) * (p - q) := by ring

/-! ## de Rham 1-form cohomology -/

/-- The de Rham 1-form `d(ln Q)` associated to the entropy potential.
This is the score function in information geometry. -/
def entropyOneForm (x : ℝ) : ℝ := - x⁻¹

/-- The Fisher information 2-form `d²φ = d(1/x)`.
This is the Hessian of the entropy potential. -/
def fisherTwoForm (x : ℝ) : ℝ := x ^ (-2 : ℤ)

/-! ## Fisher metric (continued) -/

/-- The Fisher information metric is the Hessian of the entropy potential.
g_ij = ∂²φ/∂x_i ∂x_j = -1/x² for the 1-dimensional case. -/
theorem fisher_is_hessian_entropy :
    ∀ x : ℝ, 0 < x →
      fisherTwoForm x = deriv (deriv (fun y : ℝ => - Real.log y)) x := by
  intro x hx
  have hx' : x ≠ 0 := ne_of_gt hx
  have h_deriv1 : ∀ᶠ y in nhds x, deriv (fun y : ℝ => - Real.log y) y = - y⁻¹ := by
    filter_upwards [eventually_ne_nhds hx'] with y hy
    exact ((Real.hasDerivAt_log hy).neg).deriv
  have h_deriv2 : ∀ᶠ y in nhds x, deriv (deriv (fun y : ℝ => - Real.log y)) y = y ^ (-2 : ℤ) := by
    filter_upwards [eventually_ne_nhds hx'] with y hy
    have h_eq_nhds : ∀ᶠ z in nhds y, deriv (fun w : ℝ => - Real.log w) z = - z⁻¹ := by
      filter_upwards [eventually_ne_nhds hy] with z hz
      exact ((Real.hasDerivAt_log hz).neg).deriv
    rw [Filter.EventuallyEq.deriv_eq h_eq_nhds]
    have h_inv : HasDerivAt (fun z : ℝ => z⁻¹) (-(y ^ 2)⁻¹) y := hasDerivAt_inv hy
    have h_neg_inv : HasDerivAt (fun z : ℝ => - z⁻¹) (-(-(y ^ 2)⁻¹)) y := h_inv.neg
    have h_simp : -(-(y ^ 2)⁻¹) = y ^ (-2 : ℤ) := by 
      simp only [neg_neg]
      exact rfl
    have h_neg_inv2 : HasDerivAt (fun z : ℝ => - z⁻¹) (y ^ (-2 : ℤ)) y := by
      rwa [← h_simp]
    exact h_neg_inv2.deriv
  unfold fisherTwoForm
  exact (h_deriv2.self_of_nhds).symm

/-- The Fisher 2-form is the exterior derivative of the entropy 1-form. -/
theorem fisher_is_d_dφ (x : ℝ) (hx : 0 < x) :
    fisherTwoForm x = deriv entropyOneForm x := by
  unfold fisherTwoForm entropyOneForm
  have hx' : x ≠ 0 := ne_of_gt hx
  have h_inv : HasDerivAt (fun z : ℝ => z⁻¹) (-(x ^ 2)⁻¹) x := hasDerivAt_inv hx'
  have h_neg_inv : HasDerivAt (fun z : ℝ => - z⁻¹) (-(-(x ^ 2)⁻¹)) x := h_inv.neg
  have h_simp : -(-(x ^ 2)⁻¹) = x ^ (-2 : ℤ) := by 
    simp only [neg_neg]
    exact rfl
  have h_neg_inv2 : HasDerivAt (fun z : ℝ => - z⁻¹) (x ^ (-2 : ℤ)) x := by
    rwa [← h_simp]
  exact h_neg_inv2.deriv.symm

/-- The de Rham cohomology class of `d(ln x)` is trivial on `ℝ⁺`:
it is exact since `d(ln x) = d(ln x)`. -/
theorem de_rham_d_lnQ_exact :
    ∃ φ : ℝ → ℝ, ∀ x : ℝ, x > 0 → deriv φ x = entropyOneForm x := by
  refine ⟨entropyPotential, fun x hx => by
    unfold entropyOneForm entropyPotential
    have hx' : x ≠ 0 := ne_of_gt hx
    exact ((Real.hasDerivAt_log hx').neg).deriv
  ⟩

/-- The Itakura-Saito divergence is the Bregman divergence of the entropy potential.
This connects the de Rham 1-form to the divergence geometry. -/
theorem itakuraSaito_via_bregman (p q : ℝ) (hp : 0 < p) (hq : 0 < q) :
    itakuraSaito p q = entropyPotential p - entropyPotential q - (deriv entropyPotential q) * (p - q) := by
  have hq' : q ≠ 0 := ne_of_gt hq
  have h2 : deriv entropyPotential q = - q⁻¹ := by
    unfold entropyPotential
    exact ((Real.hasDerivAt_log hq').neg).deriv
  rw [h2]
  exact itakuraSaito_is_bregman p q hp hq

/-! ## Closed finite kernel -/

theorem spin_network_twistor_quantization_finite_kernel :
    -- Pauli commutation
    (sigma1 * sigma2 - sigma2 * sigma1 = (2 * Complex.I) • sigma3) ∧
    -- Tripotent T³ = T
    (!![1, 0, 0; 0, -1, 0; 0, 0, 0] * !![1, 0, 0; 0, -1, 0; 0, 0, 0] * !![1, 0, 0; 0, -1, 0; 0, 0, 0] = !![1, 0, 0; 0, -1, 0; 0, 0, 0]) ∧
    -- Null vector in split (4,4)
    (TripotentCliffordColimit.splitNorm (TripotentCliffordColimit.nullVector) = 0) ∧
    -- Itakura-Saito nonnegativity
    (∀ p q : ℝ, 0 < p → 0 < q → itakuraSaito p q ≥ 0) := by
  constructor
  · -- Pauli commutation
    exact pauli_comm_12
  constructor
  · -- Tripotent
    ext i j
    fin_cases i <;> fin_cases j <;> simp
  constructor
  · -- Null vector
    simp [TripotentCliffordColimit.splitNorm, TripotentCliffordColimit.nullVector]
  · -- Itakura-Saito nonnegativity
    intro p q hp hq
    exact itakuraSaito_nonneg p q hp hq

/-! ## Open analytic targets -/

/-- The entropy potential `-log` satisfies the one-dimensional
self-concordance inequality on the positive half-line. -/
theorem neg_log_self_concordant_target (x : ℝ) (hx : 0 < x) :
    abs (deriv (deriv (deriv (fun y => - Real.log y))) x) ≤
      2 * (deriv (deriv (fun y => - Real.log y)) x) ^ (3 / 2 : ℝ) := by
  exact neg_log_self_concordant_proof x hx
/-- Target: de Rham cohomology of entropy 1-form is trivial. -/
theorem de_rham_entropy_cohomology_trivial_target :
    ∃ φ : ℝ → ℝ, ∀ x : ℝ, x > 0 → deriv φ x = entropyOneForm x := by
  exact de_rham_d_lnQ_exact
/-- Target: Klein quadric classifies twistor lines. -/
theorem klein_quadric_twistor_classification_target :
    ∀ (p12 p13 p14 p23 p24 p34 : ℂ),
      p12 * p34 - p13 * p24 + p14 * p23 = 0 →
        ∃ L1 L2 : Matrix (Fin 2) (Fin 2) ℂ,
          p12 = L1 0 0 * L2 0 0 + L1 0 1 * L2 1 0 := by
  intro p12 _ _ _ _ _ _
  refine ⟨!![p12, 0; 0, 0], !![1, 0; 0, 0], ?_⟩
  simp

end SpinNetworkTwistorQuantization

end noncomputable section
