/- SPDX-License-Identifier: Apache-2.0 -/

import Mathlib.Tactic
import InfoGeometry.Algebra.FiniteSpinAlgebra
import Mathlib.Data.Real.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real

namespace InfoGeometry.Quantum.BostConnes

open Real

/-!
# Asymptotic Legendre Duality of the Bost-Connes Critical Boundary (β → 1⁺)

Near the critical point, the primary cumulant potential ψ(β) = ln ζ(β) 
induces the expectation energy:
  η(β) ≈ 1 / (β - 1)  ⟹  β(η) = 1 + 1 / η

The Legendre-Fenchel conjugate dual potential (negative entropy) is:
  φ(η) = -β(η) * η - ln ζ(β(η)) ≈ -η - 1 - ln η
-/

/-- The leading-order asymptotic inverse temperature as a function of energy η > 0. -/
noncomputable def betaAsymptotic (eta : ℝ) : ℝ :=
  1 + 1 / eta

/-- The leading-order asymptotic dual potential φ(η). -/
noncomputable def phiAsymptotic (eta : ℝ) : ℝ :=
  -eta - 1 - Real.log eta

/-- The first derivative (gradient) of the asymptotic dual potential dφ/dη. -/
noncomputable def dPhiAsymptotic (eta : ℝ) : ℝ :=
  -1 - 1 / eta

/-- The dual Hessian metric (inverse Fisher information) g*(η) = d²φ/dη². -/
noncomputable def dualHessianAsymptotic (eta : ℝ) : ℝ :=
  1 / (eta ^ 2)

/-! ## Verified Asymptotic Theorems -/

/-- 🏆 THEOREM 1: The gradient of the dual potential matches -β(η) identically:
    dφ/dη = -1 - 1/η = -β(η). -/
theorem dphi_eq_neg_beta (eta : ℝ) :
    dPhiAsymptotic eta = - betaAsymptotic eta := by
  unfold dPhiAsymptotic betaAsymptotic
  ring

/-- 🏆 THEOREM 2: Exact algebraic duality relation:
    φ(η) - η · (dφ/dη) = - ln η - 1. -/
theorem legendre_fenchel_identity (eta : ℝ) (h_eta : 0 < eta) :
    phiAsymptotic eta - eta * dPhiAsymptotic eta = - Real.log eta := by
  unfold phiAsymptotic dPhiAsymptotic
  have h_ne : eta ≠ 0 := ne_of_gt h_eta
  calc
    (-eta - 1 - Real.log eta) - eta * (-1 - 1 / eta)
      = -eta - 1 - Real.log eta - (-eta - eta * (1 / eta)) := by ring
    _ = -eta - 1 - Real.log eta - (-eta - 1) := by rw [mul_one_div_cancel h_ne]
    _ = - Real.log eta := by ring

/-- 🏆 THEOREM 3: Strict positivity of the dual metric for all finite energies η > 0. -/
theorem dual_hessian_pos (eta : ℝ) (h_eta : 0 < eta) :
    0 < dualHessianAsymptotic eta := by
  unfold dualHessianAsymptotic
  have h_sq : 0 < eta ^ 2 := sq_pos_of_ne_zero (ne_of_gt h_eta)
  exact one_div_pos.mpr h_sq

/-- 🏆 THEOREM 4: Curvature flattening / Cusp singularity at high energies:
    As η → ∞ (β → 1⁺), the dual metric g*(η) = 1/η² vanishes. -/
theorem dual_metric_vanishes_at_critical_boundary (ε : ℝ) (hε : 0 < ε) :
    ∃ M : ℝ, 0 < M ∧ ∀ eta : ℝ, M < eta → dualHessianAsymptotic eta < ε := by
  use (1 / Real.sqrt ε)
  constructor
  · exact one_div_pos.mpr (Real.sqrt_pos.mpr hε)
  · intro eta h_eta
    unfold dualHessianAsymptotic
    have h_sqrt_pos : 0 < Real.sqrt ε := Real.sqrt_pos.mpr hε
    have h_M_pos : 0 < 1 / Real.sqrt ε := one_div_pos.mpr h_sqrt_pos
    have h_eta_pos : 0 < eta := lt_trans h_M_pos h_eta
    have h_sq_lt : (1 / Real.sqrt ε) ^ 2 < eta ^ 2 := sq_lt_sq.mpr (by
      rw [abs_of_pos h_M_pos, abs_of_pos h_eta_pos]
      exact h_eta)
    have h_sq_eval : (1 / Real.sqrt ε) ^ 2 = 1 / ε := by
      rw [div_pow, one_pow, Real.sq_sqrt (le_of_lt hε)]
    rw [h_sq_eval] at h_sq_lt
    have h_sq_pos : 0 < eta ^ 2 := sq_pos_of_pos h_eta_pos
    exact (one_div_lt hε h_sq_pos).mp h_sq_lt

end InfoGeometry.Quantum.BostConnes
