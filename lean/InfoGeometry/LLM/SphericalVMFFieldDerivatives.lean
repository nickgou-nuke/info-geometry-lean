import InfoGeometry.LLM.SphericalVMFExponentialFamily
import Mathlib.Tactic

set_option autoImplicit false

namespace InfoGeometry.LLM.SphericalVMF

open MeasureTheory ProbabilityTheory Metric Set
open scoped RealInnerProductSpace

noncomputable section

section NaturalParameterLine

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [CompleteSpace E] [MeasurableSpace E] [BorelSpace E]

variable (σ : Measure (UnitSphere E)) [IsProbabilityMeasure σ]

/-- Exponential tilting is additive in the natural parameter. -/
theorem law_tilted_spinObservable (θ v : E) (t : ℝ) :
    (law σ θ).tilted (fun s => t * spinObservable v s) =
      law σ (θ + t • v) := by
  have hθ : Integrable (fun s => Real.exp (spinObservable θ s)) σ := by
    simpa using integrable_exp_mul_spinObservable σ 1 θ
  unfold law
  rw [MeasureTheory.tilted_tilted hθ]
  congr 1
  funext s
  simp [spinObservable, real_inner_add_left, real_inner_smul_left]

/-- At every point of a natural-parameter line, the derivative of the log partition
is the corresponding projected mean spin. -/
theorem deriv_directionalPotential_eq_inner_response (θ v : E) (t : ℝ) :
    deriv (directionalPotential σ θ v) t =
      ⟪v, response σ (θ + t • v)⟫_ℝ := by
  have hfun : directionalPotential σ θ v =
      ProbabilityTheory.cgf (spinObservable v) (law σ θ) := by
    funext r
    exact directionalPotential_eq_cgf σ θ v r
  rw [hfun]
  have ht : t ∈ interior
      (ProbabilityTheory.integrableExpSet (spinObservable v) (law σ θ)) :=
    mem_interior_integrableExpSet_spinObservable (law σ θ) v t
  have hder := ProbabilityTheory.integral_tilted_mul_self
    (μ := law σ θ) (X := spinObservable v) (t := t) ht
  calc
    deriv (ProbabilityTheory.cgf (spinObservable v) (law σ θ)) t =
        ∫ s, spinObservable v s ∂
          ((law σ θ).tilted (fun s => t * spinObservable v s)) := by
      simpa using hder.symm
    _ = ∫ s, spinObservable v s ∂(law σ (θ + t • v)) := by
      rw [law_tilted_spinObservable σ θ v t]
    _ = ⟪v, response σ (θ + t • v)⟫_ℝ :=
      integral_spinObservable_eq_inner_response σ (θ + t • v) v

/-- Projected mean spin along a natural-parameter line. -/
noncomputable def projectedResponseLine (θ v : E) (t : ℝ) : ℝ :=
  ⟪v, response σ (θ + t • v)⟫_ℝ

/-- The directional Jacobian of the response is the directional covariance. -/
theorem deriv_projectedResponseLine_zero_eq_covarianceHessian (θ v : E) :
    deriv (projectedResponseLine σ θ v) 0 =
      covarianceHessian σ θ v v := by
  have hline : projectedResponseLine σ θ v =
      deriv (directionalPotential σ θ v) := by
    funext t
    exact (deriv_directionalPotential_eq_inner_response σ θ v t).symm
  rw [hline]
  have hsecond :=
    iteratedDeriv_two_directionalPotential_zero_eq_covarianceHessian σ θ v
  rw [show (2 : ℕ) = 1 + 1 by norm_num, iteratedDeriv_succ,
    iteratedDeriv_one] at hsecond
  exact hsecond

/-- Directional cumulants of the spherical sufficient statistic. -/
noncomputable def directionalCumulant (n : ℕ) (θ v : E) : ℝ :=
  iteratedDeriv n (directionalPotential σ θ v) 0

@[simp] theorem directionalCumulant_one (θ v : E) :
    directionalCumulant σ 1 θ v = ⟪v, response σ θ⟫_ℝ := by
  simpa [directionalCumulant] using
    deriv_directionalPotential_zero_eq_inner_response σ θ v

@[simp] theorem directionalCumulant_two (θ v : E) :
    directionalCumulant σ 2 θ v = covarianceHessian σ θ v v := by
  simpa [directionalCumulant] using
    iteratedDeriv_two_directionalPotential_zero_eq_covarianceHessian σ θ v

/-- The second directional derivative of the mean response is the third
log-partition cumulant, not the covariance. -/
theorem iteratedDeriv_two_projectedResponseLine_zero_eq_cumulant_three
    (θ v : E) :
    iteratedDeriv 2 (projectedResponseLine σ θ v) 0 =
      directionalCumulant σ 3 θ v := by
  have hline : projectedResponseLine σ θ v =
      deriv (directionalPotential σ θ v) := by
    funext t
    exact (deriv_directionalPotential_eq_inner_response σ θ v t).symm
  rw [hline]
  unfold directionalCumulant
  have hsucc := iteratedDeriv_succ'
    (n := 2) (f := directionalPotential σ θ v) (x := 0)
  simpa using hsucc.symm

end NaturalParameterLine

section FieldParameterLine

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [CompleteSpace E] [MeasurableSpace E] [BorelSpace E]
  [FiniteDimensional ℝ E] [Nontrivial E]

variable (μ : Measure E) [μ.IsAddHaarMeasure]

/-- Log-partition increment when the parameter is written as `θ = β • h`. -/
noncomputable def vmfFieldDirectionalPotential
    (β : ℝ) (h v : E) (t : ℝ) : ℝ :=
  vmfLogPartition μ β (h + t • v) - vmfLogPartition μ β h

/-- Reparameterizing by the field multiplies the natural direction by `β`. -/
theorem vmfFieldDirectionalPotential_eq_directionalPotential
    (β : ℝ) (h v : E) :
    vmfFieldDirectionalPotential μ β h v =
      directionalPotential (vmfBaseMeasure μ) (β • h) (β • v) := by
  funext t
  simp [vmfFieldDirectionalPotential, vmfLogPartition, directionalPotential,
    smul_add, smul_smul, mul_comm]

/-- Field derivative of the vMF log partition. The factor `β` is mandatory:
`D_h log Z(β h)[v] = β * ⟪v, φ_β(h)⟫`. -/
theorem deriv_vmfFieldDirectionalPotential_eq_beta_mul_response
    (β : ℝ) (h v : E) (t : ℝ) :
    deriv (vmfFieldDirectionalPotential μ β h v) t =
      β * ⟪v, vmfResponse μ β (h + t • v)⟫_ℝ := by
  rw [vmfFieldDirectionalPotential_eq_directionalPotential μ β h v]
  simpa [vmfResponse, smul_add, smul_smul, mul_comm,
    real_inner_smul_left] using
    (deriv_directionalPotential_eq_inner_response
      (vmfBaseMeasure μ) (β • h) (β • v) t)

/-- At nonzero inverse temperature the vMF mean response is `β⁻¹` times the
field-gradient of the log partition. -/
theorem inner_vmfResponse_eq_inv_mul_deriv_fieldPotential
    (β : ℝ) (hβ : β ≠ 0) (h v : E) (t : ℝ) :
    ⟪v, vmfResponse μ β (h + t • v)⟫_ℝ =
      β⁻¹ * deriv (vmfFieldDirectionalPotential μ β h v) t := by
  rw [deriv_vmfFieldDirectionalPotential_eq_beta_mul_response]
  field_simp [hβ]

/-- The field Hessian of the vMF log partition has the required `β²` scaling. -/
theorem iteratedDeriv_two_vmfFieldDirectionalPotential_zero_eq_beta_sq_covariance
    (β : ℝ) (h v : E) :
    iteratedDeriv 2 (vmfFieldDirectionalPotential μ β h v) 0 =
      β ^ 2 * vmfCovarianceHessian μ β h v v := by
  rw [vmfFieldDirectionalPotential_eq_directionalPotential μ β h v]
  rw [iteratedDeriv_two_directionalPotential_zero_eq_covarianceHessian]
  simp only [vmfCovarianceHessian, covarianceHessianBilin_apply]
  rw [covarianceHessian_smul_left, covarianceHessian_smul_right]
  ring

/-- Directional field cumulants of the vMF log partition. -/
noncomputable def vmfFieldDirectionalCumulant
    (n : ℕ) (β : ℝ) (h v : E) : ℝ :=
  iteratedDeriv n (vmfFieldDirectionalPotential μ β h v) 0

@[simp] theorem vmfFieldDirectionalCumulant_one
    (β : ℝ) (h v : E) :
    vmfFieldDirectionalCumulant μ 1 β h v =
      β * ⟪v, vmfResponse μ β h⟫_ℝ := by
  unfold vmfFieldDirectionalCumulant
  rw [iteratedDeriv_one]
  simpa using deriv_vmfFieldDirectionalPotential_eq_beta_mul_response μ β h v 0

theorem vmfFieldDirectionalCumulant_eq_directionalCumulant
    (n : ℕ) (β : ℝ) (h v : E) :
    vmfFieldDirectionalCumulant μ n β h v =
      directionalCumulant (vmfBaseMeasure μ) n (β • h) (β • v) := by
  unfold vmfFieldDirectionalCumulant directionalCumulant
  rw [vmfFieldDirectionalPotential_eq_directionalPotential μ β h v]

@[simp] theorem vmfFieldDirectionalCumulant_two
    (β : ℝ) (h v : E) :
    vmfFieldDirectionalCumulant μ 2 β h v =
      β ^ 2 * vmfCovarianceHessian μ β h v v := by
  simpa [vmfFieldDirectionalCumulant] using
    iteratedDeriv_two_vmfFieldDirectionalPotential_zero_eq_beta_sq_covariance
      μ β h v

@[simp] theorem vmfPartition_zero_field (β : ℝ) :
    vmfPartition μ β (0 : E) = 1 := by
  simp [vmfPartition]

@[simp] theorem vmfPartition_zero_beta (h : E) :
    vmfPartition μ 0 h = 1 := by
  simp [vmfPartition]

end FieldParameterLine

end
end InfoGeometry.LLM.SphericalVMF
