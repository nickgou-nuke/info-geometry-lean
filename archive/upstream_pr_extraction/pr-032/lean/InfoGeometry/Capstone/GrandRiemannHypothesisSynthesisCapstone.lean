import Mathlib.Analysis.Complex.Basic
import Mathlib.Data.Complex.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Tactic

import InfoGeometry.Analysis.AsanoLeeYangCircleBridge
import InfoGeometry.Analysis.HurwitzAsanoColimitLimitBridge
import InfoGeometry.Canonical.HadamardEntireFactorizationBridge
import InfoGeometry.Canonical.PrimonInductiveColimitLimitBridge
import InfoGeometry.Canonical.MasterRHDeductionBridge

/-!
# Conditional colimit-to-critical-line transfer

This owner contains only the zero-transfer dependencies. It does not package
Hardy, Fisher, KMS, or spectral declarations as if they participated in this
proof. The analytic realization hypotheses remain explicit:
$$\forall s_0 \in \mathbb{C} \setminus \{1\}, \quad \zeta(s_0) = 0 \implies \operatorname{Re}(s_0) = \frac{1}{2}$$
-/

noncomputable section

namespace InfoGeometry.Capstone.GrandRH

open Complex
open InfoGeometry.Canonical.MasterRH
open InfoGeometry.Analysis.AsanoLeeYangCircle
open InfoGeometry.Analysis.HurwitzAsano
open InfoGeometry.Canonical.HadamardDivisor
open InfoGeometry.Canonical.PrimonColimit

/-- Minimal datum for the conditional colimit-to-critical-line transfer. -/
structure GrandRiemannHypothesisSystemDatum extends PrimonColimitDatum where
  /-- Hadamard cofactor entire function g : ℂ → ℂ -/
  hadamard_g : ℂ → ℂ
  /-- Completed xi function -/
  xi : ℂ → ℂ
  /-- Standard Riemann zeta function -/
  zeta : ℂ → ℂ
  /-- Exact Hadamard factorization identity -/
  h_hadamard : ∀ s : ℂ, s ≠ 1 → Z_lim (riemannCayleyForward s) = Complex.exp (hadamard_g s) * xi s

/-- A supplied colimit zero at a non-exceptional Cayley point lies on the
critical line. -/
theorem colimit_zero_to_critical_line
    (D : GrandRiemannHypothesisSystemDatum)
    (s0 : ℂ) (hs0_one : s0 ≠ 1)
    (hz_zero : D.Z_lim (riemannCayleyForward s0) = 0) :
    s0.re = 1 / 2 := by
  have h_circle := primon_colimit_roots_on_unit_circle D.toPrimonColimitDatum hz_zero
  exact (norm_riemannCayley_eq_one_iff s0 hs0_one).mp h_circle

/-- A supplied factorization transfers an `xi` zero to the critical line. -/
theorem xi_zero_to_critical_line_of_colimit_factorization
    (D : GrandRiemannHypothesisSystemDatum)
    (s0 : ℂ) (hs0 : s0 ∈ criticalStrip)
    (h_xi_zero : D.xi s0 = 0) :
    s0.re = 1 / 2 := by
  have hs0_one : s0 ≠ 1 := by
    rintro rfl
    have : (1 : ℂ).re = 1 := by simp
    have h_strip := hs0.2
    rw [this] at h_strip
    linarith
  have h_z_zero := (hadamard_divisor_zero_equiv D.hadamard_g D.h_hadamard hs0).mpr h_xi_zero
  exact colimit_zero_to_critical_line D s0 hs0_one h_z_zero

/-- Conditional critical-line transfer for the supplied zero correspondence.

The correspondence `h_match` and the unit-circle hypotheses carried by `D`
are inputs. This theorem is not an unconditional proof of the Riemann
Hypothesis. -/
theorem zeta_zero_to_critical_line_of_zero_correspondence
    (D : GrandRiemannHypothesisSystemDatum)
    (s0 : ℂ) (hs0_one : s0 ≠ 1)
    (h_match : ∀ s : ℂ, D.Z_lim (riemannCayleyForward s) = 0 ↔ D.zeta s = 0)
    (h_zeta_zero : D.zeta s0 = 0) :
    s0.re = 1 / 2 := by
  have h_z_zero := (h_match s0).mpr h_zeta_zero
  exact colimit_zero_to_critical_line D s0 hs0_one h_z_zero

end InfoGeometry.Capstone.GrandRH
