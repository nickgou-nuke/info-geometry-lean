import Mathlib.Analysis.Calculus.Deriv.Basic
import InfoGeometry.Algebra.FiniteSpinAlgebra
import Mathlib.Data.Complex.Basic
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Topology.Instances.Complex
import Mathlib.Tactic

namespace InfoGeometry.Holography.ChernSimonsToLiouville

open Complex Real

noncomputable section

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

def liouvilleBackgroundCharge (b : ℝ) : ℝ :=
  b + 1 / b

def liouvilleCentralCharge (b : ℝ) : ℝ :=
  1 + 6 * (liouvilleBackgroundCharge b) ^ 2

def brownHenneauxCentralCharge (k : ℝ) : ℝ :=
  6 * k

def liouvillePotential (b μ ϕ : ℝ) : ℝ :=
  μ * Real.exp (2 * b * ϕ)

theorem liouville_background_charge_self_dual (b : ℝ) (hb : b ≠ 0) :
    liouvilleBackgroundCharge (1 / b) = liouvilleBackgroundCharge b := by
  unfold liouvilleBackgroundCharge
  have h_inv : 1 / (1 / b) = b := one_div_one_div b
  rw [h_inv, add_comm]

theorem liouville_central_charge_self_dual (b : ℝ) (hb : b ≠ 0) :
    liouvilleCentralCharge (1 / b) = liouvilleCentralCharge b := by
  unfold liouvilleCentralCharge
  rw [liouville_background_charge_self_dual b hb]

theorem brown_henneaux_c1_at_one_sixth :
    brownHenneauxCentralCharge (1 / 6) = 1 := by
  unfold brownHenneauxCentralCharge
  ring

theorem hasDerivAt_liouville_potential (b μ ϕ : ℝ) :
    HasDerivAt (fun x : ℝ => μ * Real.exp (2 * b * x))
               (2 * b * (μ * Real.exp (2 * b * ϕ))) ϕ := by
  have h_inner : HasDerivAt (fun x : ℝ => 2 * b * x) (2 * b) ϕ := by
    simpa only [mul_one] using (hasDerivAt_id ϕ).const_mul (2 * b)
  have h_exp := HasDerivAt.exp h_inner
  have h_mul := HasDerivAt.const_mul μ h_exp
  have h_eval : μ * (Real.exp (2 * b * ϕ) * (2 * b)) = 2 * b * (μ * Real.exp (2 * b * ϕ)) := by ring
  rw [h_eval] at h_mul
  exact h_mul
