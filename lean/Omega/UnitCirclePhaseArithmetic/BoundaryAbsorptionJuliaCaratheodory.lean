import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Complex.Norm
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Tactic
import Omega.UnitCirclePhaseArithmetic.AppEndpointBlaschkeRadialAbsorption
import Omega.Zeta.XiEndpointAbsorptionCoefficient
import Omega.Zeta.XiEndpointJuliaIndicatorEqualsAbsorption

namespace Complex

/-- Compatibility alias used by the unit-circle appendix files. -/
abbrev conj : ℂ → ℂ := star

end Complex

namespace Omega.UnitCirclePhaseArithmetic

open scoped BigOperators

noncomputable section

/-- Rotate a boundary point `ξ` to the endpoint `-1`. -/
def boundaryRotate (ξ a : ℂ) : ℂ :=
  -Complex.conj ξ * a

/-- The rotated root family indexed by `Fin roots.length`. -/
def boundaryRotatedRoots (roots : List ℂ) (ξ : ℂ) : Fin roots.length → ℂ :=
  fun i => boundaryRotate ξ (roots.get i)

/-- The Poisson kernel of a single root at a boundary point `ξ`. -/
def boundaryPoissonKernel (a ξ : ℂ) : ℝ :=
  (1 - ‖a‖ ^ 2) / ‖ξ - a‖ ^ 2

/-- Boundary absorption written through the rotated endpoint package. -/
def boundaryAbsorption (roots : List ℂ) (ξ : ℂ) : ℝ :=
  Omega.Zeta.xiEndpointAbsorptionCoefficient (boundaryRotatedRoots roots ξ)

/-- The Julia indicator transported from the endpoint `-1`. -/
def boundaryJuliaIndicator (roots : List ℂ) (ξ : ℂ) : ℝ :=
  Omega.Zeta.xiEndpointJuliaIndicator (fun _ => (1 : ℝ)) (boundaryRotatedRoots roots ξ)

/-- The transported boundary logarithmic derivative. -/
def boundaryAngularDerivative (roots : List ℂ) (ξ : ℂ) : ℂ :=
  -Omega.Zeta.xiEndpointBoundaryLogDerivative (fun _ => (1 : ℝ)) (boundaryRotatedRoots roots ξ)

/-- Concrete package for the boundary absorption / Julia--Caratheodory transport theorem. -/
def BoundaryAbsorptionJuliaCaratheodoryStatement (roots : List ℂ) (ξ : ℂ) : Prop :=
  ∀ (hξ : ‖ξ‖ = 1) (hroots : ∀ a ∈ roots, ‖a‖ < 1),
    boundaryAbsorption roots ξ = ∑ i : Fin roots.length, boundaryPoissonKernel (roots.get i) ξ ∧
      boundaryJuliaIndicator roots ξ = boundaryAbsorption roots ξ ∧
      Complex.re (boundaryAngularDerivative roots ξ) = boundaryAbsorption roots ξ ∧
      0 ≤ boundaryAbsorption roots ξ

lemma boundaryRotate_norm (hξ : ‖ξ‖ = 1) (a : ℂ) :
    ‖boundaryRotate ξ a‖ = ‖a‖ := by
  unfold boundaryRotate
  rw [norm_mul, norm_neg]
  have hconj : ‖Complex.conj ξ‖ = ‖ξ‖ := by simpa using Complex.norm_conj ξ
  rw [hconj, hξ, one_mul]

lemma boundaryPoissonKernel_eq_endpointPoissonMinusOne (hξ : ‖ξ‖ = 1) (a : ℂ) :
    boundaryPoissonKernel a ξ = endpointPoissonMinusOne (boundaryRotate ξ a) := by
  have hξmul : ξ * Complex.conj ξ = (1 : ℂ) := by
    simpa [hξ] using (Complex.mul_conj' ξ)
  have hden : ‖1 + boundaryRotate ξ a‖ = ‖ξ - a‖ := by
    calc
      ‖1 + boundaryRotate ξ a‖ = ‖ξ * (1 + boundaryRotate ξ a)‖ := by
        rw [norm_mul, hξ, one_mul]
      _ = ‖ξ - a‖ := by
        congr 1
        calc
          ξ * (1 + boundaryRotate ξ a) = ξ - (ξ * Complex.conj ξ) * a := by
            simp [boundaryRotate]
            ring
          _ = ξ - a := by rw [hξmul]; ring
  unfold boundaryPoissonKernel endpointPoissonMinusOne
  rw [boundaryRotate_norm hξ a, hden]

lemma boundaryPoissonKernel_nonneg {a ξ : ℂ} (ha : ‖a‖ < 1) :
    0 ≤ boundaryPoissonKernel a ξ := by
  unfold boundaryPoissonKernel
  have hnum : 0 ≤ 1 - ‖a‖ ^ 2 := by
    have hnorm_nonneg : 0 ≤ ‖a‖ := norm_nonneg _
    nlinarith
  have hden : 0 ≤ ‖ξ - a‖ ^ 2 := by positivity
  exact div_nonneg hnum hden

lemma boundaryAbsorption_eq_sum (roots : List ℂ) (ξ : ℂ) (hξ : ‖ξ‖ = 1)
    (hroots : ∀ a ∈ roots, ‖a‖ < 1) :
    boundaryAbsorption roots ξ = ∑ i : Fin roots.length, boundaryPoissonKernel (roots.get i) ξ := by
  have hrot : ∀ i : Fin roots.length, ‖boundaryRotatedRoots roots ξ i‖ < 1 := by
    intro i
    rw [boundaryRotatedRoots, boundaryRotate_norm hξ (roots.get i)]
    exact hroots (roots.get i) (List.get_mem roots i)
  have hcoeff :=
    (Omega.Zeta.paper_xi_endpoint_absorption_coefficient (boundaryRotatedRoots roots ξ) hrot).1
  calc
    boundaryAbsorption roots ξ =
        ∑ i : Fin roots.length, (1 - ‖boundaryRotatedRoots roots ξ i‖ ^ 2) / ‖1 + boundaryRotatedRoots roots ξ i‖ ^ 2 := by
          simpa [boundaryAbsorption] using hcoeff
    _ = ∑ i : Fin roots.length, boundaryPoissonKernel (roots.get i) ξ := by
          apply Finset.sum_congr rfl
          intro i _
          have h₁ : boundaryPoissonKernel (roots.get i) ξ = endpointPoissonMinusOne (boundaryRotate ξ (roots.get i)) := by
            rw [boundaryPoissonKernel_eq_endpointPoissonMinusOne hξ (roots.get i)]
          have h₂ : endpointPoissonMinusOne (boundaryRotate ξ (roots.get i)) = (1 - ‖boundaryRotate ξ (roots.get i)‖ ^ 2) / ‖1 + boundaryRotate ξ (roots.get i)‖ ^ 2 := by
            simp [endpointPoissonMinusOne]
          rw [h₁, h₂]
          <;> simp [boundaryRotatedRoots]

/-- Paper label: `thm:app-boundary-absorption-julia-caratheodory`. Rotating `ξ` to `-1`
transports the endpoint absorption coefficient and Julia indicator to an arbitrary boundary point;
the Poisson kernel simplifies back to the usual `|(ξ - a)|⁻²` form, and the transported indicator
is nonnegative for roots in the open unit disk. -/
theorem paper_app_boundary_absorption_julia_caratheodory (roots : List ℂ) (ξ : ℂ) :
    BoundaryAbsorptionJuliaCaratheodoryStatement roots ξ := by
  intro hξ hroots
  have h₁ : boundaryAbsorption roots ξ = ∑ i : Fin roots.length, boundaryPoissonKernel (roots.get i) ξ :=
    boundaryAbsorption_eq_sum roots ξ hξ hroots
  have h₂ : boundaryJuliaIndicator roots ξ = boundaryAbsorption roots ξ := by
    dsimp [boundaryJuliaIndicator, boundaryAbsorption]
    -- xiEndpointAbsorptionCoefficient a = xiEndpointAbsorption (fun _ => 1) a by definition
    <;> simp [Omega.Zeta.xiEndpointAbsorptionCoefficient]
    <;> rfl
  have h₃ : Complex.re (boundaryAngularDerivative roots ξ) = boundaryAbsorption roots ξ := by
    dsimp [boundaryAngularDerivative, boundaryAbsorption] at *
    -- Use the theorem from XiEndpointJuliaIndicatorEqualsAbsorption
    have h₄ := Omega.Zeta.paper_xi_endpoint_julia_indicator_equals_absorption (κ := roots.length) (w := fun _ => (1 : ℝ)) (z := boundaryRotatedRoots roots ξ)
    have h₅ : Omega.Zeta.xiEndpointJuliaIndicator (fun _ => (1 : ℝ)) (boundaryRotatedRoots roots ξ) = Omega.Zeta.xiEndpointAbsorption (fun _ => (1 : ℝ)) (boundaryRotatedRoots roots ξ) := h₄.1
    have h₆ : Omega.Zeta.xiEndpointAbsorption (fun _ => (1 : ℝ)) (boundaryRotatedRoots roots ξ) = Complex.re (-Omega.Zeta.xiEndpointBoundaryLogDerivative (fun _ => (1 : ℝ)) (boundaryRotatedRoots roots ξ)) := h₄.2
    have h₇ : Omega.Zeta.xiEndpointAbsorptionCoefficient (boundaryRotatedRoots roots ξ) = Omega.Zeta.xiEndpointAbsorption (fun _ => (1 : ℝ)) (boundaryRotatedRoots roots ξ) := by
      simp [Omega.Zeta.xiEndpointAbsorptionCoefficient]
      <;> rfl
    simp_all [Omega.Zeta.xiEndpointAbsorptionCoefficient]
    <;>
    (try ring_nf at *) <;>
    (try simp_all [Complex.ext_iff]) <;>
    (try norm_num at *) <;>
    (try linarith)
    <;>
    (try
      {
        simp_all [Omega.Zeta.xiEndpointAbsorptionCoefficient, Omega.Zeta.xiEndpointAbsorption, Omega.Zeta.xiEndpointAbsorptionTerm]
        <;>
        norm_num at *
        <;>
        linarith
      })
  have h₄ : 0 ≤ boundaryAbsorption roots ξ := by
    dsimp [boundaryAbsorption]
    have hrot : ∀ i : Fin roots.length, ‖boundaryRotatedRoots roots ξ i‖ < 1 := by
      intro i
      rw [boundaryRotatedRoots, boundaryRotate_norm hξ (roots.get i)]
      exact hroots (roots.get i) (List.get_mem roots i)
    -- Use the fact that each term in the sum is non-negative
    have h₅ : 0 ≤ Omega.Zeta.xiEndpointAbsorptionCoefficient (boundaryRotatedRoots roots ξ) := by
      have h₆ : Omega.Zeta.xiEndpointAbsorptionCoefficient (boundaryRotatedRoots roots ξ) = ∑ i : Fin roots.length, (1 - ‖boundaryRotatedRoots roots ξ i‖ ^ 2) / ‖1 + boundaryRotatedRoots roots ξ i‖ ^ 2 := by
        have h₇ := (Omega.Zeta.paper_xi_endpoint_absorption_coefficient (boundaryRotatedRoots roots ξ) hrot).1
        exact h₇
      rw [h₆]
      apply Finset.sum_nonneg
      intro i _
      have h₈ : 0 ≤ (1 - ‖boundaryRotatedRoots roots ξ i‖ ^ 2 : ℝ) := by
        have h₉ : ‖boundaryRotatedRoots roots ξ i‖ < 1 := hrot i
        have h₁₀ : ‖boundaryRotatedRoots roots ξ i‖ ^ 2 < 1 := by
          have h₁₁ : 0 ≤ ‖boundaryRotatedRoots roots ξ i‖ := norm_nonneg _
          nlinarith
        linarith
      have h₉ : 0 ≤ (‖1 + boundaryRotatedRoots roots ξ i‖ ^ 2 : ℝ) := by positivity
      exact div_nonneg h₈ h₉
    linarith
  exact ⟨h₁, h₂, h₃, h₄⟩

end

end Omega.UnitCirclePhaseArithmetic