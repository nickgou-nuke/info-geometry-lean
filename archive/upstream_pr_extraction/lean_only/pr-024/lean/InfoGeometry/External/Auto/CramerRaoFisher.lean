import Mathlib

/-!
# Cramér-Rao and Fisher Curvature

Finite scalar information-geometry layer for the Primon/Fenchel dictionary.

The file proves the checkable core:

* a positive Fisher scalar `I` gives the Cramér-Rao lower bound `I⁻¹`;
* the quadratic log-partition chart `I * θ² / 2` has Fenchel dual
  `E² / (2I)`;
* the dual Hessian is the reciprocal Fisher curvature;
* inversion of a positive partition function flips the log-potential.

This is a finite real model.  It does not prove the Riemann hypothesis or
analytic properties of the Riemann zeta function.
-/

noncomputable section

set_option linter.unnecessarySimpa false

def fisherQuadratic (I θ : ℝ) : ℝ :=
  I * θ ^ 2 / 2

def dualFisherQuadratic (I E : ℝ) : ℝ :=
  E ^ 2 / (2 * I)

def cramerRaoBound (I : ℝ) : ℝ :=
  I⁻¹

def bosonicLogPotential (Z : ℝ) : ℝ :=
  Real.log Z

def fermionicInverseLogPotential (Z : ℝ) : ℝ :=
  Real.log Z⁻¹

theorem cramerRao_from_information_product {I variance : ℝ}
    (hI : 0 < I) (hprod : 1 ≤ I * variance) :
    cramerRaoBound I ≤ variance := by
  unfold cramerRaoBound
  calc
    I⁻¹ = I⁻¹ * 1 := by ring
    _ ≤ I⁻¹ * (I * variance) := by
      exact mul_le_mul_of_nonneg_left hprod (inv_nonneg.mpr (le_of_lt hI))
    _ = variance := by
      field_simp [ne_of_gt hI]

theorem fisher_fenchel_young {I θ E : ℝ} (hI : 0 < I) :
    θ * E ≤ fisherQuadratic I θ + dualFisherQuadratic I E := by
  unfold fisherQuadratic dualFisherQuadratic
  have hgap :
      I * θ ^ 2 / 2 + E ^ 2 / (2 * I) - θ * E =
        (I * θ - E) ^ 2 / (2 * I) := by
    field_simp [ne_of_gt hI]
    ring
  have hnonneg : 0 ≤ (I * θ - E) ^ 2 / (2 * I) :=
    div_nonneg (sq_nonneg (I * θ - E)) (by positivity)
  nlinarith

theorem fisher_fenchel_eq_on_gradient {I θ : ℝ} (hI : I ≠ 0) :
    fisherQuadratic I θ + dualFisherQuadratic I (I * θ) = θ * (I * θ) := by
  unfold fisherQuadratic dualFisherQuadratic
  field_simp [hI]
  ring

theorem fisher_gradient {I θ : ℝ} :
    deriv (fisherQuadratic I) θ = I * θ := by
  unfold fisherQuadratic
  have hsq : HasDerivAt (fun θ : ℝ => θ ^ 2) (2 * θ) θ := by
    simpa using hasDerivAt_pow 2 θ
  have hscaled : HasDerivAt (fun θ : ℝ => (I / 2) * θ ^ 2)
      ((I / 2) * (2 * θ)) θ :=
    hsq.const_mul (I / 2)
  simpa [mul_comm, mul_left_comm, mul_assoc, div_eq_mul_inv] using hscaled.deriv

theorem dual_fisher_gradient {I E : ℝ} (hI : I ≠ 0) :
    deriv (dualFisherQuadratic I) E = E / I := by
  unfold dualFisherQuadratic
  have hsq : HasDerivAt (fun E : ℝ => E ^ 2) (2 * E) E := by
    simpa using hasDerivAt_pow 2 E
  have hscaled : HasDerivAt (fun E : ℝ => (1 / (2 * I)) * E ^ 2)
      ((1 / (2 * I)) * (2 * E)) E :=
    hsq.const_mul (1 / (2 * I))
  have hne : 2 * I ≠ 0 := mul_ne_zero two_ne_zero hI
  simpa [div_eq_mul_inv, hne, mul_comm, mul_left_comm, mul_assoc] using hscaled.deriv

theorem dual_fisher_hessian {I E : ℝ} (hI : I ≠ 0) :
    deriv (fun x : ℝ => deriv (dualFisherQuadratic I) x) E = I⁻¹ := by
  have hgrad : (fun x : ℝ => deriv (dualFisherQuadratic I) x) =
      fun x : ℝ => x / I := by
    funext x
    exact dual_fisher_gradient (I := I) (E := x) hI
  rw [hgrad]
  have hlin : HasDerivAt (fun x : ℝ => (1 / I) * x) (1 / I) E := by
    simpa [id] using (hasDerivAt_id E |>.const_mul (1 / I))
  simpa [div_eq_mul_inv, mul_comm] using hlin.deriv

theorem fisher_hessian {I θ : ℝ} :
    deriv (fun x : ℝ => deriv (fisherQuadratic I) x) θ = I := by
  have hgrad : (fun x : ℝ => deriv (fisherQuadratic I) x) =
      fun x : ℝ => I * x := by
    funext x
    exact fisher_gradient (I := I) (θ := x)
  rw [hgrad]
  have hlin : HasDerivAt (fun x : ℝ => I * x) I θ := by
    simpa [id] using (hasDerivAt_id θ |>.const_mul I)
  simpa using hlin.deriv

theorem hessian_inverse_duality {I θ E : ℝ} (hI : I ≠ 0) :
    deriv (fun x : ℝ => deriv (fisherQuadratic I) x) θ *
      deriv (fun x : ℝ => deriv (dualFisherQuadratic I) x) E = 1 := by
  rw [fisher_hessian, dual_fisher_hessian hI]
  field_simp [hI]

theorem inverse_partition_log_duality {Z : ℝ} :
    fermionicInverseLogPotential Z = -bosonicLogPotential Z := by
  unfold fermionicInverseLogPotential bosonicLogPotential
  rw [Real.log_inv]

/-- Consolidated finite CRB/Fenchel package. -/
theorem cramer_rao_fisher_synthesis {I variance Z : ℝ}
    (hI : 0 < I) (hprod : 1 ≤ I * variance) (hZ : 0 < Z) :
    cramerRaoBound I ≤ variance ∧
    (∀ θ E, θ * E ≤ fisherQuadratic I θ + dualFisherQuadratic I E) ∧
    (∀ θ E, deriv (fun x : ℝ => deriv (fisherQuadratic I) x) θ *
      deriv (fun x : ℝ => deriv (dualFisherQuadratic I) x) E = 1) ∧
    fermionicInverseLogPotential Z = -bosonicLogPotential Z := by
  have _ := hZ
  exact ⟨cramerRao_from_information_product hI hprod,
    fun θ E => fisher_fenchel_young hI,
    fun θ E => hessian_inverse_duality (I := I) (θ := θ) (E := E) (ne_of_gt hI),
    inverse_partition_log_duality⟩

end noncomputable section
