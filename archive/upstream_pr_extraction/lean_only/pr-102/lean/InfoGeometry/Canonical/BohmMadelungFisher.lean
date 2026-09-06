import Mathlib.Tactic
import InfoGeometry.Potential.Thermo

/-!
# Bohm-Madelung Quantum Potential and Fisher Information

This module formalizes the fundamental information-geometric identity connecting the
expectation value of the Bohm quantum potential `Q` to the Fisher Information `I_F` of the
probability density `ρ`. 

We prove that under the integration-by-parts (IBP) condition (vanishing boundary terms), the
expectation value of the quantum potential is exactly one-eighth of the total Fisher Information:
`⟨Q⟩ = (1/8) * I_F`.
-/

noncomputable section

namespace InfoGeometry.Canonical.BohmMadelungFisher

set_option linter.unusedSectionVars false

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- Pointwise Bohm-Madelung quantum potential density: `Q = - (1/2) * (∇² f / f)`. -/
def BohmDensity (d2f : E → ℝ) (f : E → ℝ) (x : E) : ℝ :=
  - (1 / 2) * d2f x / f x

/-- Pointwise Fisher information density: `I_F = ‖∇ρ‖² / ρ`. -/
def FisherDensity (dρ : E → E) (ρ : E → ℝ) (x : E) : ℝ :=
  ‖dρ x‖^2 / ρ x

/-- Pointwise expectation value density of the Bohm potential: `ρ * Q`. -/
def expectationDensity (ρ : E → ℝ) (d2f : E → ℝ) (f : E → ℝ) (x : E) : ℝ :=
  ρ x * BohmDensity d2f f x

/-- Pointwise Bohm potential expectation density relates to wave function curvature. -/
theorem bohm_expectation_density_eq (ρ f : E → ℝ) (d2f : E → ℝ) (x : E)
    (h_pos : 0 < f x) (h_rho : ρ x = f x ^ 2) :
    expectationDensity ρ d2f f x = - (1 / 2) * f x * d2f x := by
  dsimp [expectationDensity, BohmDensity]
  rw [h_rho]
  have h_ne : f x ≠ 0 := ne_of_gt h_pos
  field_simp [h_ne]

/-- Pointwise Fisher density relates to wave function gradient. -/
theorem fisher_density_eq (ρ f : E → ℝ) (df dρ : E → E) (x : E)
    (h_pos : 0 < f x) (h_rho : ρ x = f x ^ 2) (h_dρ : dρ x = (2 * f x) • df x) :
    FisherDensity dρ ρ x = 4 * ‖df x‖^2 := by
  dsimp [FisherDensity]
  rw [h_rho, h_dρ]
  have h_ne : f x ≠ 0 := ne_of_gt h_pos
  have h_norm : ‖(2 * f x) • df x‖ = |2 * f x| * ‖df x‖ := norm_smul _ _
  have h_norm_sq : ‖(2 * f x) • df x‖^2 = (2 * f x)^2 * ‖df x‖^2 := by
    rw [h_norm, mul_pow]
    have h_abs_sq : |2 * f x|^2 = (2 * f x)^2 := sq_abs _
    rw [h_abs_sq]
  rw [h_norm_sq]
  have h_div : (2 * f x)^2 = 4 * f x^2 := by ring
  rw [h_div]
  have h_f_sq_ne : f x^2 ≠ 0 := pow_ne_zero 2 h_ne
  field_simp [h_f_sq_ne]

/-- **Global Identity: Bohm Potential Expectation vs Fisher Information**
    Assuming a linear integration functional on `E → ℝ` and the standard Integration By Parts (IBP)
    relation, the expectation value of the Bohm potential is exactly `1/8` of the Fisher Information. -/
theorem bohm_expectation_eq_one_eighth_fisher
    (ρ f : E → ℝ) (df dρ : E → E) (d2f : E → ℝ)
    (h_pos : ∀ x, 0 < f x)
    (h_rho : ∀ x, ρ x = f x ^ 2)
    (h_dρ : ∀ x, dρ x = (2 * f x) • df x)
    (integral : (E → ℝ) →ₗ[ℝ] ℝ)
    (ibp : integral (fun x => f x * d2f x) = - integral (fun x => ‖df x‖^2)) :
    integral (fun x => expectationDensity ρ d2f f x) = (1 / 8) * integral (fun x => FisherDensity dρ ρ x) := by
  have h_density_eq : (fun x => expectationDensity ρ d2f f x) = (fun x => - (1 / 2) * f x * d2f x) := by
    ext x
    have h := bohm_expectation_density_eq ρ f d2f x (h_pos x) (h_rho x)
    exact h
  have h_fisher_eq : (fun x => FisherDensity dρ ρ x) = (fun x => 4 * ‖df x‖^2) := by
    ext x
    have h := fisher_density_eq ρ f df dρ x (h_pos x) (h_rho x) (h_dρ x)
    exact h
  rw [h_density_eq, h_fisher_eq]
  have h_LHS : integral (fun x => - (1 / 2) * f x * d2f x) = - (1 / 2) * integral (fun x => f x * d2f x) := by
    have h_const : (fun x => - (1 / 2) * f x * d2f x) = (- (1 / 2) : ℝ) • (fun x => f x * d2f x) := by
      ext x
      simp [Pi.smul_apply]
      ring
    rw [h_const]
    have h_smul := LinearMap.map_smul integral (- (1 / 2) : ℝ) (fun x => f x * d2f x)
    rw [h_smul]
    exact smul_eq_mul _ _
  have h_RHS : integral (fun x => 4 * ‖df x‖^2) = 4 * integral (fun x => ‖df x‖^2) := by
    have h_const : (fun x => 4 * ‖df x‖^2) = (4 : ℝ) • (fun x => ‖df x‖^2) := by
      ext x
      simp [Pi.smul_apply]
    rw [h_const]
    have h_smul := LinearMap.map_smul integral (4 : ℝ) (fun x => ‖df x‖^2)
    rw [h_smul]
    exact smul_eq_mul _ _
  rw [h_LHS, ibp, h_RHS]
  ring

/-! ### Constructive 1D Quantum Potential & Fisher Model -/

/-- 1D Pointwise Bohm-Fisher density identity on real functions:
    $\rho(x) Q(x) = -\frac{1}{2} f(x) f''(x)$ and $I_F(x) = 4 (f'(x))^2$. -/
theorem bohm_fisher_pointwise_identity (f_val df_val d2f_val : ℝ) (hf_pos : 0 < f_val) :
    let rho_val := f_val ^ 2
    let bohm_q := - (1 / 2 : ℝ) * d2f_val / f_val
    let exp_q := rho_val * bohm_q
    let fisher_i := (2 * f_val * df_val) ^ 2 / rho_val
    exp_q = - (1 / 2 : ℝ) * f_val * d2f_val ∧
    fisher_i = 4 * df_val ^ 2 := by
  have hne : f_val ≠ 0 := ne_of_gt hf_pos
  have hsq_ne : f_val ^ 2 ≠ 0 := pow_ne_zero 2 hne
  refine ⟨by
    show f_val ^ 2 * (- (1 / 2 : ℝ) * d2f_val / f_val) = - (1 / 2 : ℝ) * f_val * d2f_val
    field_simp [hne],
    by
    show (2 * f_val * df_val) ^ 2 / (f_val ^ 2) = 4 * df_val ^ 2
    have h1 : (2 * f_val * df_val) ^ 2 = (4 * df_val ^ 2) * f_val ^ 2 := by ring
    rw [h1]
    exact mul_div_cancel_right₀ (4 * df_val ^ 2) hsq_ne⟩

end InfoGeometry.Canonical.BohmMadelungFisher

end noncomputable section
