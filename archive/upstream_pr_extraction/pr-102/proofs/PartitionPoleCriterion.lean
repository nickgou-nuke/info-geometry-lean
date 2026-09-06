import Mathlib

/-!
# Partition Function Pole Criterion

Finite analytic model for the Hagedorn/zeta pole heuristic.

If the density of states grows like `exp (βc * E)`, then the Boltzmann
integrand behaves like

`exp (-(β - βc) * E)`.

For `a = β - βc > 0`, the antiderivative of `exp (-aE)` is

`- exp (-aE) / a`,

and the limiting pole scale is `1 / a`.

This file proves the local differential/algebraic facts.  It does not assert
an improper-integral convergence theorem for zeta.
-/

noncomputable section

def densityGrowthKernel (βc E : ℝ) : ℝ :=
  Real.exp (βc * E)

def boltzmannDamping (β E : ℝ) : ℝ :=
  Real.exp (-(β * E))

def poleIntegrand (β βc E : ℝ) : ℝ :=
  densityGrowthKernel βc E * boltzmannDamping β E

def poleRate (β βc : ℝ) : ℝ :=
  β - βc

def poleModel (β βc : ℝ) : ℝ :=
  (poleRate β βc)⁻¹

def poleAntiderivative (β βc E : ℝ) : ℝ :=
  -Real.exp (-(poleRate β βc * E)) / poleRate β βc

def poleCutoffIntegralModel (β βc L : ℝ) : ℝ :=
  (1 - Real.exp (-(poleRate β βc * L))) / poleRate β βc

theorem poleIntegrand_eq_rate (β βc E : ℝ) :
    poleIntegrand β βc E = Real.exp (-(poleRate β βc * E)) := by
  unfold poleIntegrand densityGrowthKernel boltzmannDamping poleRate
  rw [← Real.exp_add]
  congr 1
  ring

theorem poleAntiderivative_deriv {β βc E : ℝ} (h : poleRate β βc ≠ 0) :
    deriv (fun x => poleAntiderivative β βc x) E =
      poleIntegrand β βc E := by
  unfold poleAntiderivative
  have hrate : poleRate β βc ≠ 0 := h
  have hlinear :
      HasDerivAt (fun x : ℝ => -(poleRate β βc * x)) (-(poleRate β βc)) E := by
    simpa [mul_comm, mul_left_comm, mul_assoc] using
      ((hasDerivAt_id E).const_mul (-(poleRate β βc)))
  have hexp :
      HasDerivAt (fun x : ℝ => Real.exp (-(poleRate β βc * x)))
        (Real.exp (-(poleRate β βc * E)) * (-(poleRate β βc))) E := by
    exact (Real.hasDerivAt_exp (-(poleRate β βc * E))).comp E hlinear
  have hscaled :
      HasDerivAt
        (fun x : ℝ => -(Real.exp (-(poleRate β βc * x))) / poleRate β βc)
        ((-(Real.exp (-(poleRate β βc * E)) * (-(poleRate β βc)))) /
          poleRate β βc) E := by
    exact hexp.neg.div_const (poleRate β βc)
  rw [hscaled.deriv]
  rw [poleIntegrand_eq_rate]
  field_simp [hrate]

theorem poleCutoffIntegralModel_eq_antiderivative_diff (β βc L : ℝ) :
    poleCutoffIntegralModel β βc L =
      poleAntiderivative β βc L - poleAntiderivative β βc 0 := by
  unfold poleCutoffIntegralModel poleAntiderivative
  by_cases h : poleRate β βc = 0
  · simp [h]
  · field_simp [h]
    simp
    ring

theorem poleModel_is_inverse {β βc : ℝ} (h : β ≠ βc) :
    poleRate β βc * poleModel β βc = 1 := by
  unfold poleRate poleModel
  change (β - βc) * (β - βc)⁻¹ = 1
  field_simp [sub_ne_zero.mpr h]

theorem poleModel_positive {β βc : ℝ} (h : βc < β) :
    0 < poleModel β βc := by
  unfold poleModel poleRate
  exact inv_pos.mpr (sub_pos.mpr h)

theorem zeta_critical_rate (β : ℝ) :
    poleRate β 1 = β - 1 := by
  rfl

theorem zeta_pole_model_inverse {β : ℝ} (h : β ≠ 1) :
    (β - 1) * poleModel β 1 = 1 := by
  simpa [poleRate, poleModel] using poleModel_is_inverse (β := β) (βc := 1) h

/-- Consolidated pole-criterion package. -/
theorem partition_pole_criterion_synthesis :
    (∀ β βc E, poleIntegrand β βc E = Real.exp (-(poleRate β βc * E))) ∧
    (∀ β βc, β ≠ βc → poleRate β βc * poleModel β βc = 1) ∧
    (∀ β βc, βc < β → 0 < poleModel β βc) ∧
    (∀ β, poleRate β 1 = β - 1) ∧
    (∀ β, β ≠ 1 → (β - 1) * poleModel β 1 = 1) := by
  exact ⟨poleIntegrand_eq_rate, fun β βc h => poleModel_is_inverse h,
    fun β βc h => poleModel_positive h, zeta_critical_rate,
    fun β h => zeta_pole_model_inverse h⟩

end noncomputable section
