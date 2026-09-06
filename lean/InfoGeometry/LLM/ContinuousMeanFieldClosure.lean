import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.Probability.Moments.Variance

set_option autoImplicit false

namespace InfoGeometry.LLM.ContinuousMeanFieldClosure

open MeasureTheory ProbabilityTheory

noncomputable section

variable {Ω E F : Type*} [MeasurableSpace Ω]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]

/-- Bochner mean of a vector-valued random field. -/
noncomputable def mean (μ : Measure Ω) (H : Ω → E) : E :=
  ∫ ω, H ω ∂μ

/-- Exact nonlinear mean-field closure defect `E[φ(H)] - φ(E[H])`. -/
noncomputable def closureDefect
    (μ : Measure Ω) (φ : E → F) (H : Ω → E) : F :=
  (∫ ω, φ (H ω) ∂μ) - φ (mean μ H)

/-- Centered fluctuation field. -/
noncomputable def centeredField
    (μ : Measure Ω) (H : Ω → E) (ω : Ω) : E :=
  H ω - mean μ H

/-- Quadratic term associated with a continuous bilinear second-variation candidate. -/
noncomputable def quadraticClosureTerm
    (μ : Measure Ω) (H : Ω → E)
    (B : E →L[ℝ] E →L[ℝ] F) : F :=
  ∫ ω, (1 / 2 : ℝ) • B (centeredField μ H ω) (centeredField μ H ω) ∂μ

/-- Exact second-order remainder around the mean `m`. -/
noncomputable def secondOrderRemainder
    (φ : E → F) (D : E →L[ℝ] F) (B : E →L[ℝ] E →L[ℝ] F)
    (m x : E) : F :=
  φ x - φ m - D (x - m) - (1 / 2 : ℝ) • B (x - m) (x - m)

section Probability

variable (μ : Measure Ω) [IsProbabilityMeasure μ]

/-- Centering removes the first moment exactly. -/
theorem integral_centeredField_eq_zero
    (H : Ω → E) (hH : Integrable H μ) :
    ∫ ω, centeredField μ H ω ∂μ = 0 := by
  unfold centeredField mean
  rw [integral_sub hH (integrable_const _)]
  simp

/-- Every continuous linear response annihilates the centered first-order term. -/
theorem integral_linear_centeredField_eq_zero
    (H : Ω → E) (D : E →L[ℝ] F) (hH : Integrable H μ) :
    ∫ ω, D (centeredField μ H ω) ∂μ = 0 := by
  have hcenter : Integrable (centeredField μ H) μ := by
    unfold centeredField
    exact hH.sub (integrable_const _)
  rw [D.integral_comp_comm hcenter, integral_centeredField_eq_zero μ H hH, map_zero]

/-- Pointwise second-order Taylor decomposition, with no approximation hidden in the notation. -/
theorem secondOrder_decomposition
    (φ : E → F) (D : E →L[ℝ] F) (B : E →L[ℝ] E →L[ℝ] F)
    (m x : E) :
    φ x = φ m + D (x - m) + (1 / 2 : ℝ) • B (x - m) (x - m) +
      secondOrderRemainder φ D B m x := by
  unfold secondOrderRemainder
  abel

/-- Exact continuous Plefka/delta-method identity.

The linear fluctuation term cancels because `E[H - E[H]] = 0`.  What remains is the
quadratic covariance contraction plus the integrated second-order remainder.
-/
theorem closureDefect_eq_quadraticClosureTerm_add_remainder
    (φ : E → F) (H : Ω → E)
    (D : E →L[ℝ] F) (B : E →L[ℝ] E →L[ℝ] F)
    (hH : Integrable H μ)
    (hQ : Integrable
      (fun ω => (1 / 2 : ℝ) •
        B (centeredField μ H ω) (centeredField μ H ω)) μ)
    (hR : Integrable
      (fun ω => secondOrderRemainder φ D B (mean μ H) (H ω)) μ) :
    closureDefect μ φ H =
      quadraticClosureTerm μ H B +
        ∫ ω, secondOrderRemainder φ D B (mean μ H) (H ω) ∂μ := by
  have hcenter : Integrable (centeredField μ H) μ := by
    unfold centeredField
    exact hH.sub (integrable_const _)
  have hlinear : Integrable (fun ω => D (centeredField μ H ω)) μ :=
    D.integrable_comp hcenter
  have hconst : Integrable (fun _ : Ω => φ (mean μ H)) μ := integrable_const _
  have hdecomp :
      (fun ω => φ (H ω)) =
        (fun ω =>
          (φ (mean μ H) + D (centeredField μ H ω)) +
            (1 / 2 : ℝ) • B (centeredField μ H ω) (centeredField μ H ω) +
              secondOrderRemainder φ D B (mean μ H) (H ω)) := by
    funext ω
    simpa [centeredField] using
      secondOrder_decomposition φ D B (mean μ H) (H ω)
  have hlinzero :
      (∫ ω, D (centeredField μ H ω) ∂μ) = 0 :=
    integral_linear_centeredField_eq_zero μ H D hH
  have hconstint : (∫ _ : Ω, φ (mean μ H) ∂μ) = φ (mean μ H) := by simp
  unfold closureDefect quadraticClosureTerm
  rw [hdecomp]
  rw [integral_add ((hconst.add hlinear).add hQ) hR]
  rw [integral_add (hconst.add hlinear) hQ]
  rw [integral_add hconst hlinear]
  rw [hconstint, hlinzero]
  abel

/-- Quantified second-order closure bound.

If the pointwise Taylor remainder is bounded by `(C / 6) * ‖H - E[H]‖³`, then the
error after retaining the quadratic covariance term is bounded by the corresponding
third centered moment.  This is the rigorous content hidden by an informal `O(‖ξ‖³)`.
-/
theorem norm_closureDefect_sub_quadraticClosureTerm_le_thirdMoment
    (φ : E → F) (H : Ω → E)
    (D : E →L[ℝ] F) (B : E →L[ℝ] E →L[ℝ] F)
    (C : ℝ)
    (hH : Integrable H μ)
    (hQ : Integrable
      (fun ω => (1 / 2 : ℝ) •
        B (centeredField μ H ω) (centeredField μ H ω)) μ)
    (hR : Integrable
      (fun ω => secondOrderRemainder φ D B (mean μ H) (H ω)) μ)
    (hThird : Integrable
      (fun ω => (C / 6) * ‖centeredField μ H ω‖ ^ (3 : ℕ)) μ)
    (hbound : ∀ᵐ ω ∂μ,
      ‖secondOrderRemainder φ D B (mean μ H) (H ω)‖ ≤
        (C / 6) * ‖centeredField μ H ω‖ ^ (3 : ℕ)) :
    ‖closureDefect μ φ H - quadraticClosureTerm μ H B‖ ≤
      ∫ ω, (C / 6) * ‖centeredField μ H ω‖ ^ (3 : ℕ) ∂μ := by
  rw [closureDefect_eq_quadraticClosureTerm_add_remainder
    μ φ H D B hH hQ hR]
  simp only [add_sub_cancel_left]
  exact norm_integral_le_of_norm_le hThird hbound

end Probability

end
end InfoGeometry.LLM.ContinuousMeanFieldClosure
