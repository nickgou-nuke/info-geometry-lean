/-
Finite algebraic bridges for Legendre contact, skew-adjoint operators,
linear velocity readouts, and finite Gibbs weights.

These declarations do not prove that transformer attention is a physical fluid
or that a finite probability vector alone satisfies the KMS condition for a
specified algebra and time evolution.
-/

import InfoGeometry.Capstone.NavierStokesLegendre
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Krein.DoubledSpace
import InfoGeometry.Convex.Legendre
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.InnerProductSpace.Adjoint
import InfoGeometry.Potential.Thermo
import InfoGeometry.Canonical.NavierStokesBridge

open scoped InnerProductSpace
open InfoGeometry.LogPotential
open InfoGeometry.Canonical
open InfoGeometry.Krein

noncomputable section

namespace InfoGeometry.Capstone.FiniteLegendreFluidReadout

variable {E : Type _}
variable [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
variable [FiniteDimensional ℝ E]

local notation "H₂" => InfoGeometry.Krein.DoubledSpace E
local notation "EndH" => AlgebraEnd E

-- Axiomatic Legendre conjugate mapping for 1D duality
open InfoGeometry.Capstone.NavierStokesLegendre

/--
### STAGE 1: Information Theory (L = 0)

The Fenchel-Legendre gap represents information-theoretic loss.
At equilibrium, this loss vanishes.
-/
theorem information_loss_vanishes (L : LegendreModel) (θ η : ℝ)
  (hd : HasDerivAt L.L.ψ (L.grad θ) θ)
  (h_eq : η = L.grad θ) :
  L.fenchelGap θ η = 0 := by
  rw [fenchelGap_eq_zero_iff_contact L θ η hd]
  exact h_eq

/- At the Legendre contact point, the Fenchel gap vanishes. This is a scalar
convex-duality statement, with no attention interpretation assumed. -/
theorem legendre_contact_exists (L : LegendreModel) (θ : ℝ) :
  ∃ η : ℝ, η = L.grad θ ∧
    L.L.ψ θ + L.φ η - θ * η = 0 := by
  use L.grad θ
  refine ⟨rfl, ?_⟩
  exact L.fenchelGap_eq_zero_at_contact θ

omit [FiniteDimensional ℝ E] in
lemma skew_adjoint_quad_form_zero (A : DoubledSpace E →L[ℝ] DoubledSpace E)
    (hA : star A = -A) (v : DoubledSpace E) :
    ⟪v, A v⟫_ℝ = 0 := by
  have h1 : ⟪v, A v⟫_ℝ = ⟪star A v, v⟫_ℝ := by
    rw [ContinuousLinearMap.star_eq_adjoint]
    rw [real_inner_comm v (ContinuousLinearMap.adjoint A v)]
    rw [ContinuousLinearMap.adjoint_inner_right]
    rw [real_inner_comm v (A v)]
  have h2 : ⟪star A v, v⟫_ℝ = -⟪v, A v⟫_ℝ := by
    rw [hA]
    rw [ContinuousLinearMap.neg_apply]
    rw [inner_neg_left]
    rw [real_inner_comm (A v) v]
  linarith

omit [CompleteSpace E] [FiniteDimensional ℝ E] in
lemma inner_projBase_left (v : ArnoldMajoranaCarrier E) (x : E) :
    ⟪projBase v, x⟫_ℝ = ⟪v, embedBase x⟫_ℝ := by
  dsimp [projBase, embedBase, InfoGeometry.Krein.to_doubled]
  rw [inner_zero_right, add_zero]

omit [CompleteSpace E] [FiniteDimensional ℝ E] in
lemma inner_projBase_right (v : ArnoldMajoranaCarrier E) (x : E) :
    ⟪x, projBase v⟫_ℝ = ⟪embedBase x, v⟫_ℝ := by
  rw [real_inner_comm]
  rw [inner_projBase_left]
  rw [real_inner_comm]

/-- A skew-adjoint operator has zero trace after the specified base projection. -/
theorem collapse_trace_zero_for_bivector
  (K : EndH) (h_bivector : star K = -K) :
  LinearMap.trace ℝ E (collapseToBaseVelocity K).toLinearMap = 0 := by
  obtain ⟨ι, b, _⟩ := exists_orthonormalBasis ℝ E
  rw [LinearMap.trace_eq_sum_inner (collapseToBaseVelocity K).toLinearMap b]
  have h_zero : ∀ i, ⟪b i, (collapseToBaseVelocity K).toLinearMap (b i)⟫_ℝ = 0 := by
    intro i
    dsimp [collapseToBaseVelocity]
    rw [inner_projBase_right]
    apply skew_adjoint_quad_form_zero K h_bivector
  have h_sum : ∑ i, ⟪b i, (collapseToBaseVelocity K).toLinearMap (b i)⟫_ℝ = 0 := by
    apply Finset.sum_eq_zero
    intro i _
    exact h_zero i
  exact h_sum

/-- In this finite model, divergence-free means that the linear velocity
Jacobian has trace zero. The stated equivalence follows from the explicit
velocity formula of `madelungFluidState`. -/
theorem trace_free_implies_divergence_free
  (β : ℝ) (K : EndH)
  (vac : ThermalVacuum (E := E) K) (ω : EndH →L[ℝ] ℝ)
  (hSmooth : IsThermodynamicallySmoothed β K)
  (h_trace : LinearMap.trace ℝ E (collapseToBaseVelocity K).toLinearMap = 0) :
  IsDivergenceFree (madelungFluidState β K vac ω hSmooth).u := by
  rw [madelung_divergence_free_iff]
  exact Or.inr h_trace

/- Finite softmax weights are Gibbs weights for the explicitly chosen energy
`H i = -theta i`. The theorem below proves the weight identity, normalization,
and positivity. It does not state a KMS condition. -/
theorem finite_softmax_eq_gibbs_weights {n : ℕ} [Nonempty (Fin n)]
    (theta : Fin n → ℝ) (beta : ℝ) :
  let Z := ∑ i, Real.exp (beta * theta i)
  let rho : Fin n → ℝ := fun i => Real.exp (beta * theta i) / Z
  let H : Fin n → ℝ := fun i => -theta i
  (∀ i, rho i = Real.exp (-beta * H i) / Z) ∧
  (∑ i, rho i = 1) ∧
  (∀ i, rho i > 0) := by
  constructor
  · intro i
    dsimp
    have h : -beta * -theta i = beta * theta i := by ring
    rw [h]
  · constructor
    · have h1 : ∑ i, (Real.exp (beta * theta i) / ∑ j, Real.exp (beta * theta j)) =
        (∑ i, Real.exp (beta * theta i)) / ∑ j, Real.exp (beta * theta j) := by
          simp [Finset.sum_div]
      rw [h1]
      have h2 : ∑ j, Real.exp (beta * theta j) ≠ 0 := by
        have : 0 < ∑ j, Real.exp (beta * theta j) := by
          apply Finset.sum_pos
          · intro i _
            exact Real.exp_pos _
          · exact Finset.univ_nonempty
        exact this.ne'
      exact div_self h2
    · intro i
      apply div_pos (Real.exp_pos _)
      apply Finset.sum_pos
      · intro j _
        exact Real.exp_pos _
      · exact Finset.univ_nonempty

/- A skew-adjoint generator has trace-zero collapsed velocity, hence the
declared linear velocity readout is divergence-free in this finite model. -/
theorem skew_adjoint_madelung_velocity_divergence_free
    (β : ℝ) (K : EndH)
    (vac : ThermalVacuum (E := E) K) (ω : EndH →L[ℝ] ℝ)
    (hSmooth : IsThermodynamicallySmoothed β K)
    (h_bivector : star K = -K) :
  IsDivergenceFree (madelungFluidState β K vac ω hSmooth).u := by
  have h_trace_zero : LinearMap.trace ℝ E (collapseToBaseVelocity K).toLinearMap = 0 :=
    collapse_trace_zero_for_bivector K h_bivector
  exact trace_free_implies_divergence_free β K vac ω hSmooth h_trace_zero

end InfoGeometry.Capstone.FiniteLegendreFluidReadout
