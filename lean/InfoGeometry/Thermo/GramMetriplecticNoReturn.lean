/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Physics.FiniteMetriplecticDynamics
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.Calculus.Deriv.MeanValue

/-! # Entropy and return obstruction for a constructed Gram Onsager operator

On real Hilbert spaces, the dissipative operator is constructed as `A† A`.
The existing GENERIC velocity is used with this operator. The chain rule
connects its algebraic rate to the derivative of an actual entropy function
along a differentiable solution. Skewness and the entropy Casimir law give
`(S ∘ ρ)' = ‖A (grad S)‖²`.

An entropy return therefore forces the dissipative force to vanish throughout
the open return interval. A periodic solution has no dissipative part anywhere;
its remaining reversible motion need not be stationary. This is an obstruction
for an isolated entropy-producing evolution, not an existence theorem for the
ODE or a prohibition on externally driven heat-engine cycles.
-/

noncomputable section

namespace InfoGeometry.Thermo.GramMetriplecticNoReturn

open InfoGeometry.Physics
open scoped InnerProductSpace

variable {E F : Type*}
variable [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
variable [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]

/-- The existing GENERIC velocity with a constructed positive Gram operator. -/
def gramVelocity (J : E → E →L[ℝ] E) (A : E → E →L[ℝ] F)
    (gradH gradS : E → E) (x : E) : E :=
  metriplecticVelocity (fun x => (J x).toLinearMap)
    (fun x => ((A x).adjoint.comp (A x)).toLinearMap) gradH gradS x

theorem gramVelocity_apply (J : E → E →L[ℝ] E) (A : E → E →L[ℝ] F)
    (gradH gradS : E → E) (x : E) :
    gramVelocity J A gradH gradS x =
      J x (gradH x) + (A x).adjoint (A x (gradS x)) := rfl

variable (J : E → E →L[ℝ] E) (A : E → E →L[ℝ] F)
variable (gradH gradS : E → E)

/-- The rate identity uses the actual adjoint, not a supplied positivity field. -/
theorem entropy_rate_eq_norm_sq
    (hJ : ∀ x u v, inner ℝ (J x u) v = -inner ℝ u (J x v))
    (hcas : ∀ x, J x (gradS x) = 0) (x : E) :
    inner ℝ (gradS x) (gramVelocity J A gradH gradS x) =
      ‖A x (gradS x)‖ ^ 2 := by
  have hrate := entropyRate_eq_onsager_quadratic
    (fun _ : E => innerₗ E) (fun _ u v => real_inner_comm v u)
    (fun x => (J x).toLinearMap)
    (fun x => ((A x).adjoint.comp (A x)).toLinearMap)
    hJ gradH gradS hcas x
  change inner ℝ (gradS x) (gramVelocity J A gradH gradS x) =
    inner ℝ (gradS x) ((A x).adjoint (A x (gradS x))) at hrate
  rw [hrate, ContinuousLinearMap.adjoint_inner_right, real_inner_self_eq_norm_sq]

/-- Chain-rule realization of the algebraic entropy rate along a solution. -/
theorem hasDerivAt_entropy
    (S : E → ℝ) (ρ : ℝ → E) (t : ℝ)
    (hJ : ∀ x u v, inner ℝ (J x u) v = -inner ℝ u (J x v))
    (hcas : ∀ x, J x (gradS x) = 0)
    (hS : HasFDerivAt S (innerSL ℝ (gradS (ρ t))) (ρ t))
    (hρ : HasDerivAt ρ (gramVelocity J A gradH gradS (ρ t)) t) :
    HasDerivAt (S ∘ ρ) (‖A (ρ t) (gradS (ρ t))‖ ^ 2) t := by
  have h := hS.comp_hasDerivAt t hρ
  change HasDerivAt (S ∘ ρ)
    (inner ℝ (gradS (ρ t)) (gramVelocity J A gradH gradS (ρ t))) t at h
  rwa [entropy_rate_eq_norm_sq J A gradH gradS hJ hcas] at h

/-- Energy conservation follows from the actual gradient and `A (grad H)=0`. -/
theorem hasDerivAt_energy_zero
    (H : E → ℝ) (ρ : ℝ → E) (t : ℝ)
    (hJ : ∀ x u v, inner ℝ (J x u) v = -inner ℝ u (J x v))
    (hdeg : ∀ x, A x (gradH x) = 0)
    (hH : HasFDerivAt H (innerSL ℝ (gradH (ρ t))) (ρ t))
    (hρ : HasDerivAt ρ (gramVelocity J A gradH gradS (ρ t)) t) :
    HasDerivAt (H ∘ ρ) 0 t := by
  have hsym : ∀ x u v,
      inner ℝ ((A x).adjoint (A x u)) v =
        inner ℝ u ((A x).adjoint (A x v)) := by
    intro x u v
    rw [ContinuousLinearMap.adjoint_inner_left,
      ContinuousLinearMap.adjoint_inner_right]
  have hzero := energy_conserved
    (fun _ : E => innerₗ E) (fun _ u v => real_inner_comm v u)
    (fun x => (J x).toLinearMap)
    (fun x => ((A x).adjoint.comp (A x)).toLinearMap)
    hJ hsym gradH gradS (fun x => by simp [hdeg x]) (ρ t)
  have h := hH.comp_hasDerivAt t hρ
  change inner ℝ (gradH (ρ t)) (gramVelocity J A gradH gradS (ρ t)) = 0 at hzero
  change HasDerivAt (H ∘ ρ)
    (inner ℝ (gradH (ρ t)) (gramVelocity J A gradH gradS (ρ t))) t at h
  rwa [hzero] at h

variable (S : E → ℝ) (ρ : ℝ → E)
variable (hJ : ∀ x u v, inner ℝ (J x u) v = -inner ℝ u (J x v))
variable (hcas : ∀ x, J x (gradS x) = 0)
variable (hS : ∀ t, HasFDerivAt S (innerSL ℝ (gradS (ρ t))) (ρ t))
variable (hρ : ∀ t, HasDerivAt ρ (gramVelocity J A gradH gradS (ρ t)) t)

include hJ hcas hS hρ

/-- Entropy monotonicity is an analytic consequence of the solution equation. -/
theorem entropy_monotone : Monotone (S ∘ ρ) :=
  monotone_of_hasDerivAt_nonneg
    (fun t => hasDerivAt_entropy J A gradH gradS S ρ t hJ hcas (hS t) (hρ t))
    (fun _ => sq_nonneg _)

/-- Equal endpoint entropy forces constant entropy between the endpoints. -/
theorem entropy_eq_of_return {a b t : ℝ}
    (hreturn : S (ρ b) = S (ρ a)) (hat : a ≤ t) (htb : t ≤ b) :
    S (ρ t) = S (ρ a) := by
  have hm := entropy_monotone J A gradH gradS S ρ hJ hcas hS hρ
  exact le_antisymm ((hm htb).trans_eq hreturn) (hm hat)

/-- Every interior dissipative force vanishes on an entropy-return segment. -/
theorem dissipative_force_eq_zero_of_return {a b t : ℝ}
    (hreturn : S (ρ b) = S (ρ a)) (hat : a < t) (htb : t < b) :
    A (ρ t) (gradS (ρ t)) = 0 := by
  have heq : (S ∘ ρ) =ᶠ[nhds t] (fun _ => S (ρ a)) := by
    filter_upwards [Ioo_mem_nhds hat htb] with s hs
    exact entropy_eq_of_return J A gradH gradS S ρ hJ hcas hS hρ
      hreturn hs.1.le hs.2.le
  have hz : HasDerivAt (S ∘ ρ) 0 t :=
    (hasDerivAt_const t (S (ρ a))).congr_of_eventuallyEq heq
  have hnorm := (hasDerivAt_entropy J A gradH gradS S ρ t
    hJ hcas (hS t) (hρ t)).unique hz
  simpa only [sq_eq_zero_iff, norm_eq_zero] using hnorm

/-- A nonzero dissipative force rules out return to the same state. -/
theorem no_state_return_of_dissipative_force_ne_zero {a b t : ℝ}
    (hat : a < t) (htb : t < b)
    (hne : A (ρ t) (gradS (ρ t)) ≠ 0) : ρ b ≠ ρ a := by
  intro hreturn
  exact hne (dissipative_force_eq_zero_of_return J A gradH gradS S ρ
    hJ hcas hS hρ (congrArg S hreturn) hat htb)

/-- A positive-period solution has zero dissipative force at every time. -/
theorem dissipative_force_eq_zero_of_periodic {P : ℝ} (hP : 0 < P)
    (hperiod : Function.Periodic ρ P) (t : ℝ) :
    A (ρ t) (gradS (ρ t)) = 0 := by
  have hreturn : S (ρ (t + P / 2)) = S (ρ (t - P / 2)) := by
    have harg : t - P / 2 + P = t + P / 2 := by ring
    simpa only [harg] using congrArg S (hperiod (t - P / 2))
  exact dissipative_force_eq_zero_of_return J A gradH gradS S ρ hJ hcas hS hρ
    hreturn (by linarith) (by linarith)

/-- Periodicity leaves only the reversible component; it need not make it zero. -/
theorem periodic_velocity_eq_reversible {P : ℝ} (hP : 0 < P)
    (hperiod : Function.Periodic ρ P) (t : ℝ) :
    gramVelocity J A gradH gradS (ρ t) = J (ρ t) (gradH (ρ t)) := by
  rw [gramVelocity_apply,
    dissipative_force_eq_zero_of_periodic J A gradH gradS S ρ hJ hcas hS hρ
      hP hperiod t, map_zero, add_zero]

end InfoGeometry.Thermo.GramMetriplecticNoReturn
